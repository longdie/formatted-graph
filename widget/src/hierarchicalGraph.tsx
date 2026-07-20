import * as React from 'react'
import dagre from '@dagrejs/dagre'
import HtmlDisplay, { Html } from './htmlDisplay'

const { graphlib, layout: dagreLayout } = dagre

type BoundingShape =
  | { circle: { radius: number } }
  | { rect: { width: number; height: number } }

interface Vertex {
  id: string
  label: Html
  boundingShape: BoundingShape
  details?: Html
}

interface Edge {
  source: string
  target: string
  attrs: [string, unknown][]
  label?: Html
  details?: Html
}

interface Props {
  vertices: Vertex[]
  edges: Edge[]
  defaultEdgeAttrs: [string, unknown][]
  showDetails: boolean
}

interface Point {
  x: number
  y: number
}

interface LayoutResult {
  positions: Record<string, Point>
  width: number
  height: number
}

interface Bounds {
  center: Point
  width: number
  height: number
}

interface Camera {
  center: Point
  zoom: number
}

interface ViewportSize {
  width: number
  height: number
}

interface EdgeGeometry {
  source: Point
  target: Point
  midpoint: Point
  path: string
}

type EdgeStyle = 'curved' | 'orthogonal'

const minZoom = 0.25
const maxZoom = 3
const readableZoom = 0.72
const zoomStep = 1.2

type Selection =
  | { type: 'vertex'; id: string }
  | { type: 'edge'; index: number }
  | undefined

const dimensions = (shape: BoundingShape): { width: number; height: number } =>
  'rect' in shape
    ? shape.rect
    : { width: shape.circle.radius * 2, height: shape.circle.radius * 2 }

const clamp = (value: number, minimum: number, maximum: number): number =>
  Math.min(maximum, Math.max(minimum, value))

function graphBounds(
  vertices: Vertex[],
  positions: Record<string, Point>,
): Bounds {
  if (vertices.length === 0) {
    return { center: { x: 0, y: 0 }, width: 320, height: 260 }
  }

  let minX = Number.POSITIVE_INFINITY
  let minY = Number.POSITIVE_INFINITY
  let maxX = Number.NEGATIVE_INFINITY
  let maxY = Number.NEGATIVE_INFINITY
  for (const vertex of vertices) {
    const position = positions[vertex.id]
    if (!position) continue
    const { width, height } = dimensions(vertex.boundingShape)
    minX = Math.min(minX, position.x - width / 2)
    maxX = Math.max(maxX, position.x + width / 2)
    minY = Math.min(minY, position.y - height / 2)
    maxY = Math.max(maxY, position.y + height / 2)
  }

  if (!Number.isFinite(minX)) {
    return { center: { x: 0, y: 0 }, width: 320, height: 260 }
  }
  return {
    center: { x: (minX + maxX) / 2, y: (minY + maxY) / 2 },
    width: Math.max(maxX - minX, 1),
    height: Math.max(maxY - minY, 1),
  }
}

function cameraForBounds(
  bounds: Bounds,
  viewport: ViewportSize,
  minimum: number = minZoom,
): Camera {
  const horizontal = viewport.width / (bounds.width + 128)
  const vertical = viewport.height / (bounds.height + 128)
  return {
    center: bounds.center,
    zoom: clamp(Math.min(horizontal, vertical), minimum, maxZoom),
  }
}

function computeLayout(vertices: Vertex[], edges: Edge[]): LayoutResult {
  const graph = new graphlib.Graph()
  graph.setGraph({
    rankdir: 'TB',
    ranker: 'network-simplex',
    ranksep: 96,
    nodesep: 72,
    edgesep: 36,
    marginx: 48,
    marginy: 48,
  })
  graph.setDefaultEdgeLabel(() => ({}))

  for (const vertex of vertices) {
    graph.setNode(vertex.id, dimensions(vertex.boundingShape))
  }
  for (const edge of edges) graph.setEdge(edge.source, edge.target)

  dagreLayout(graph)
  const graphSize = graph.graph()
  const width = Math.max(graphSize.width ?? 0, 320)
  const height = Math.max(graphSize.height ?? 0, 260)
  const positions: Record<string, Point> = {}
  for (const vertex of vertices) {
    const node = graph.node(vertex.id)
    positions[vertex.id] = {
      x: node.x - width / 2,
      y: node.y - height / 2,
    }
  }
  return { positions, width, height }
}

function boundaryPoint(vertex: Vertex, from: Point, toward: Point): Point {
  const dx = toward.x - from.x
  const dy = toward.y - from.y
  const distance = Math.hypot(dx, dy) || 1
  if ('circle' in vertex.boundingShape) {
    const scale = vertex.boundingShape.circle.radius / distance
    return { x: from.x + dx * scale, y: from.y + dy * scale }
  }

  const { width, height } = vertex.boundingShape.rect
  const scale = Math.min(
    Math.abs(dx) < 0.001 ? Number.POSITIVE_INFINITY : width / 2 / Math.abs(dx),
    Math.abs(dy) < 0.001 ? Number.POSITIVE_INFINITY : height / 2 / Math.abs(dy),
  )
  return { x: from.x + dx * scale, y: from.y + dy * scale }
}

function curvedEdgeGeometry(
  sourceVertex: Vertex,
  targetVertex: Vertex,
  sourceCenter: Point,
  targetCenter: Point,
): EdgeGeometry {
  const source = boundaryPoint(sourceVertex, sourceCenter, targetCenter)
  const target = boundaryPoint(targetVertex, targetCenter, sourceCenter)
  const dx = target.x - source.x
  const dy = target.y - source.y
  let path: string
  if (Math.abs(dy) >= Math.abs(dx) * 0.4) {
    const bend = Math.max(36, Math.abs(dy) * 0.45) * Math.sign(dy || 1)
    path = `M ${source.x} ${source.y} C ${source.x} ${source.y + bend}, ${target.x} ${target.y - bend}, ${target.x} ${target.y}`
  } else {
    const bend = Math.max(36, Math.abs(dx) * 0.45) * Math.sign(dx || 1)
    path = `M ${source.x} ${source.y} C ${source.x + bend} ${source.y}, ${target.x - bend} ${target.y}, ${target.x} ${target.y}`
  }
  return {
    source,
    target,
    midpoint: {
      x: (sourceCenter.x + targetCenter.x) / 2,
      y: (sourceCenter.y + targetCenter.y) / 2,
    },
    path,
  }
}

type PortSide = 'top' | 'right' | 'bottom' | 'left'

function portPoint(vertex: Vertex, center: Point, side: PortSide): Point {
  const { width, height } = dimensions(vertex.boundingShape)
  switch (side) {
    case 'top':
      return { x: center.x, y: center.y - height / 2 }
    case 'right':
      return { x: center.x + width / 2, y: center.y }
    case 'bottom':
      return { x: center.x, y: center.y + height / 2 }
    case 'left':
      return { x: center.x - width / 2, y: center.y }
  }
}

function orthogonalEdgeGeometry(
  sourceVertex: Vertex,
  targetVertex: Vertex,
  sourceCenter: Point,
  targetCenter: Point,
  edgeIndex: number,
): EdgeGeometry {
  const dx = targetCenter.x - sourceCenter.x
  const dy = targetCenter.y - sourceCenter.y
  const lane = ((edgeIndex % 5) - 2) * 8

  if (Math.abs(dy) >= Math.abs(dx) * 0.45) {
    const downward = dy >= 0
    const source = portPoint(
      sourceVertex,
      sourceCenter,
      downward ? 'bottom' : 'top',
    )
    const target = portPoint(
      targetVertex,
      targetCenter,
      downward ? 'top' : 'bottom',
    )
    const span = target.y - source.y
    const offset = clamp(lane, -Math.abs(span) / 4, Math.abs(span) / 4)
    const middleY = (source.y + target.y) / 2 + offset
    return {
      source,
      target,
      midpoint: { x: (source.x + target.x) / 2, y: middleY },
      path: `M ${source.x} ${source.y} L ${source.x} ${middleY} L ${target.x} ${middleY} L ${target.x} ${target.y}`,
    }
  }

  const rightward = dx >= 0
  const source = portPoint(
    sourceVertex,
    sourceCenter,
    rightward ? 'right' : 'left',
  )
  const target = portPoint(
    targetVertex,
    targetCenter,
    rightward ? 'left' : 'right',
  )
  const span = target.x - source.x
  const offset = clamp(lane, -Math.abs(span) / 4, Math.abs(span) / 4)
  const middleX = (source.x + target.x) / 2 + offset
  return {
    source,
    target,
    midpoint: { x: middleX, y: (source.y + target.y) / 2 },
    path: `M ${source.x} ${source.y} L ${middleX} ${source.y} L ${middleX} ${target.y} L ${target.x} ${target.y}`,
  }
}

function selfLoopGeometry(vertex: Vertex, center: Point): EdgeGeometry {
  const { width, height } = dimensions(vertex.boundingShape)
  const source = { x: center.x + width / 2 - 4, y: center.y - height / 4 }
  const target = { x: center.x + width / 2 - 4, y: center.y + height / 4 }
  const loopX = center.x + width / 2 + 64
  return {
    source,
    target,
    midpoint: { x: loopX, y: center.y },
    path: `M ${source.x} ${source.y} C ${loopX} ${center.y - height}, ${loopX} ${center.y + height}, ${target.x} ${target.y}`,
  }
}

const attrsToObject = (attrs: [string, unknown][]): Record<string, any> =>
  Object.fromEntries(attrs)

const controlButtonStyle = (active: boolean = false): React.CSSProperties => ({
  minWidth: 30,
  height: 28,
  padding: '0 8px',
  border: '1px solid var(--vscode-editorWidget-border)',
  borderRadius: 4,
  background: active
    ? 'var(--vscode-button-background)'
    : 'var(--vscode-editor-background)',
  color: active
    ? 'var(--vscode-button-foreground)'
    : 'var(--vscode-editor-foreground)',
  fontFamily: 'var(--vscode-font-family)',
  fontSize: 12,
  cursor: 'pointer',
})

export default function HierarchicalGraph({
  vertices,
  edges,
  defaultEdgeAttrs,
  showDetails,
}: Props): React.ReactElement {
  const initialLayout = React.useMemo(
    () => computeLayout(vertices, edges),
    [vertices, edges],
  )
  const initialCanvasWidth = Math.max(initialLayout.width + 128, 480)
  const initialCanvasHeight = Math.max(initialLayout.height + 128, 420)
  const renderedHeight = Math.min(initialCanvasHeight, 720)
  const [positions, setPositions] = React.useState(initialLayout.positions)
  const [selection, setSelection] = React.useState<Selection>()
  const [draggingId, setDraggingId] = React.useState<string>()
  const [edgeStyle, setEdgeStyle] = React.useState<EdgeStyle>('orthogonal')
  const [camera, setCamera] = React.useState<Camera>(() =>
    cameraForBounds(
      graphBounds(vertices, initialLayout.positions),
      { width: initialCanvasWidth, height: renderedHeight },
      readableZoom,
    ),
  )
  const [viewport, setViewport] = React.useState<ViewportSize>({
    width: initialCanvasWidth,
    height: renderedHeight,
  })
  const [panning, setPanning] = React.useState(false)
  const svgRef = React.useRef<SVGSVGElement>(null)
  const drag = React.useRef<{
    id: string
    pointerId: number
    moved: boolean
    startClient: Point
    offset: Point
  }>()
  const pan = React.useRef<{
    pointerId: number
    startClient: Point
    startCenter: Point
  }>()
  const markerId = `formatted-graph-arrow-${React.useId().replace(/:/g, '')}`

  React.useEffect(() => {
    setPositions(initialLayout.positions)
    setSelection(undefined)
    const bounds = graphBounds(vertices, initialLayout.positions)
    setCamera(cameraForBounds(bounds, viewport, readableZoom))
  }, [initialLayout])

  React.useLayoutEffect(() => {
    const svg = svgRef.current
    if (!svg) return
    const updateSize = () => {
      const rect = svg.getBoundingClientRect()
      if (rect.width > 0 && rect.height > 0) {
        setViewport({ width: rect.width, height: rect.height })
      }
    }
    const observer = new ResizeObserver(updateSize)
    observer.observe(svg)
    updateSize()
    return () => observer.disconnect()
  }, [renderedHeight])

  const clientPosition = (clientX: number, clientY: number): Point => {
    const svg = svgRef.current
    if (!svg) return { x: clientX, y: clientY }
    const point = svg.createSVGPoint()
    point.x = clientX
    point.y = clientY
    const matrix = svg.getScreenCTM()
    return matrix
      ? point.matrixTransform(matrix.inverse())
      : { x: clientX, y: clientY }
  }

  const pointerPosition = (event: React.PointerEvent<SVGGElement>): Point =>
    clientPosition(event.clientX, event.clientY)

  const zoomBy = (factor: number) => {
    setCamera(current => ({
      ...current,
      zoom: clamp(current.zoom * factor, minZoom, maxZoom),
    }))
  }

  const resetZoom = () => {
    setCamera({
      center: graphBounds(vertices, positions).center,
      zoom: 1,
    })
  }

  const fitView = () => {
    setCamera(cameraForBounds(graphBounds(vertices, positions), viewport))
  }

  const resetLayout = () => {
    setPositions(initialLayout.positions)
    setSelection(undefined)
    const bounds = graphBounds(vertices, initialLayout.positions)
    setCamera(cameraForBounds(bounds, viewport, readableZoom))
  }

  React.useEffect(() => {
    const svg = svgRef.current
    if (!svg) return
    const handleWheel = (event: WheelEvent) => {
      if (!event.ctrlKey && !event.metaKey) return
      event.preventDefault()
      const rect = svg.getBoundingClientRect()
      const graphPoint = clientPosition(event.clientX, event.clientY)
      const relativeX = (event.clientX - rect.left) / rect.width - 0.5
      const relativeY = (event.clientY - rect.top) / rect.height - 0.5
      const factor = Math.exp(-event.deltaY * 0.002)
      setCamera(current => {
        const zoom = clamp(current.zoom * factor, minZoom, maxZoom)
        return {
          center: {
            x: graphPoint.x - relativeX * viewport.width / zoom,
            y: graphPoint.y - relativeY * viewport.height / zoom,
          },
          zoom,
        }
      })
    }
    svg.addEventListener('wheel', handleWheel, { passive: false })
    return () => svg.removeEventListener('wheel', handleWheel)
  }, [viewport])

  const beginDrag = (event: React.PointerEvent<SVGGElement>, id: string) => {
    event.preventDefault()
    event.stopPropagation()
    event.currentTarget.setPointerCapture(event.pointerId)
    const pointer = pointerPosition(event)
    const current = positions[id] ?? pointer
    drag.current = {
      id,
      pointerId: event.pointerId,
      moved: false,
      startClient: { x: event.clientX, y: event.clientY },
      offset: { x: current.x - pointer.x, y: current.y - pointer.y },
    }
    setDraggingId(id)
  }

  const moveDrag = (event: React.PointerEvent<SVGGElement>, id: string) => {
    if (drag.current?.id !== id || drag.current.pointerId !== event.pointerId) return
    if (Math.hypot(
      event.clientX - drag.current.startClient.x,
      event.clientY - drag.current.startClient.y,
    ) > 3) {
      drag.current.moved = true
    }
    const point = pointerPosition(event)
    const offset = drag.current.offset
    setPositions(current => ({
      ...current,
      [id]: { x: point.x + offset.x, y: point.y + offset.y },
    }))
  }

  const endDrag = (event: React.PointerEvent<SVGGElement>, vertex: Vertex) => {
    if (drag.current?.id !== vertex.id || drag.current.pointerId !== event.pointerId) return
    const moved = drag.current.moved
    drag.current = undefined
    setDraggingId(undefined)
    if (event.currentTarget.hasPointerCapture(event.pointerId)) {
      event.currentTarget.releasePointerCapture(event.pointerId)
    }
    if (!moved && showDetails && vertex.details) {
      setSelection({ type: 'vertex', id: vertex.id })
    }
  }

  const cancelDrag = (event: React.PointerEvent<SVGGElement>, id: string) => {
    if (drag.current?.id !== id || drag.current.pointerId !== event.pointerId) return
    drag.current = undefined
    setDraggingId(undefined)
  }

  const beginPan = (event: React.PointerEvent<SVGSVGElement>) => {
    if (event.button !== 0 || event.target !== event.currentTarget) return
    event.preventDefault()
    event.currentTarget.setPointerCapture(event.pointerId)
    pan.current = {
      pointerId: event.pointerId,
      startClient: { x: event.clientX, y: event.clientY },
      startCenter: camera.center,
    }
    setPanning(true)
  }

  const movePan = (event: React.PointerEvent<SVGSVGElement>) => {
    const currentPan = pan.current
    if (currentPan?.pointerId !== event.pointerId) return
    setCamera(current => ({
      ...current,
      center: {
        x: currentPan.startCenter.x
          - (event.clientX - currentPan.startClient.x) / current.zoom,
        y: currentPan.startCenter.y
          - (event.clientY - currentPan.startClient.y) / current.zoom,
      },
    }))
  }

  const endPan = (event: React.PointerEvent<SVGSVGElement>) => {
    if (pan.current?.pointerId !== event.pointerId) return
    pan.current = undefined
    setPanning(false)
    if (event.currentTarget.hasPointerCapture(event.pointerId)) {
      event.currentTarget.releasePointerCapture(event.pointerId)
    }
  }

  const viewWidth = viewport.width / camera.zoom
  const viewHeight = viewport.height / camera.zoom
  const viewX = camera.center.x - viewWidth / 2
  const viewY = camera.center.y - viewHeight / 2
  const vertexById = new Map(vertices.map(vertex => [vertex.id, vertex]))
  const selectedDetails = selection?.type === 'vertex'
    ? vertexById.get(selection.id)?.details
    : selection?.type === 'edge'
      ? edges[selection.index]?.details
      : undefined

  return (
    <div style={{ width: '100%' }}>
      <div
        style={{
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'space-between',
          flexWrap: 'wrap',
          gap: 8,
          padding: '2px 0 6px',
        }}
      >
        <div role="group" aria-label="Edge style" style={{ display: 'flex', gap: 3 }}>
          <button
            type="button"
            title="Draw edges as curves"
            aria-pressed={edgeStyle === 'curved'}
            onClick={() => setEdgeStyle('curved')}
            style={controlButtonStyle(edgeStyle === 'curved')}
          >
            Curved
          </button>
          <button
            type="button"
            title="Draw edges with right-angle segments"
            aria-pressed={edgeStyle === 'orthogonal'}
            onClick={() => setEdgeStyle('orthogonal')}
            style={controlButtonStyle(edgeStyle === 'orthogonal')}
          >
            Orthogonal
          </button>
        </div>

        <div role="group" aria-label="View controls" style={{ display: 'flex', gap: 3 }}>
          <button
            type="button"
            title="Zoom out"
            aria-label="Zoom out"
            onClick={() => zoomBy(1 / zoomStep)}
            style={controlButtonStyle()}
          >
            -
          </button>
          <button
            type="button"
            title="Reset zoom to 100%"
            onClick={resetZoom}
            style={{ ...controlButtonStyle(), minWidth: 52 }}
          >
            {Math.round(camera.zoom * 100)}%
          </button>
          <button
            type="button"
            title="Zoom in"
            aria-label="Zoom in"
            onClick={() => zoomBy(zoomStep)}
            style={controlButtonStyle()}
          >
            +
          </button>
          <button
            type="button"
            title="Fit the graph in the viewport"
            onClick={fitView}
            style={controlButtonStyle()}
          >
            Fit
          </button>
          <button
            type="button"
            title="Reset node positions and view"
            onClick={resetLayout}
            style={controlButtonStyle()}
          >
            Reset
          </button>
        </div>
      </div>

      <svg
        ref={svgRef}
        width="100%"
        height={renderedHeight}
        viewBox={`${viewX} ${viewY} ${viewWidth} ${viewHeight}`}
        onPointerDown={beginPan}
        onPointerMove={movePan}
        onPointerUp={endPan}
        onPointerCancel={endPan}
        style={{
          display: 'block',
          touchAction: 'none',
          userSelect: 'none',
          cursor: panning ? 'grabbing' : 'grab',
        }}
      >
        <defs>
          <marker
            id={markerId}
            viewBox="0 0 10 10"
            refX="8"
            refY="5"
            markerWidth="7"
            markerHeight="7"
            orient="auto-start-reverse"
          >
            <path d="M 0 0 L 10 5 L 0 10 z" fill="context-stroke" />
          </marker>
        </defs>

        <g>
          {edges.map((edge, index) => {
            const sourceVertex = vertexById.get(edge.source)
            const targetVertex = vertexById.get(edge.target)
            const sourceCenter = positions[edge.source]
            const targetCenter = positions[edge.target]
            if (!sourceVertex || !targetVertex || !sourceCenter || !targetCenter) return null
            const geometry = edge.source === edge.target
              ? selfLoopGeometry(sourceVertex, sourceCenter)
              : edgeStyle === 'orthogonal'
                ? orthogonalEdgeGeometry(
                    sourceVertex,
                    targetVertex,
                    sourceCenter,
                    targetCenter,
                    index,
                  )
                : curvedEdgeGeometry(
                    sourceVertex,
                    targetVertex,
                    sourceCenter,
                    targetCenter,
                  )
            const attributes = {
              ...attrsToObject(defaultEdgeAttrs),
              ...attrsToObject(edge.attrs),
              fill: 'none',
              markerEnd: `url(#${markerId})`,
              strokeLinecap: 'round' as const,
              strokeLinejoin: 'round' as const,
            }
            return (
              <g
                key={`${edge.source}-${edge.target}-${index}`}
                onClick={() => showDetails && edge.details && setSelection({ type: 'edge', index })}
                style={{ cursor: edge.details ? 'pointer' : 'default' }}
              >
                <path
                  d={geometry.path}
                  {...attributes}
                />
                {edge.label && (
                  <g transform={`translate(${geometry.midpoint.x}, ${geometry.midpoint.y})`}>
                    <HtmlDisplay html={edge.label} />
                  </g>
                )}
              </g>
            )
          })}
        </g>

        <g>
          {vertices.map(vertex => {
            const point = positions[vertex.id]
            if (!point) return null
            return (
              <g
                key={vertex.id}
                transform={`translate(${point.x}, ${point.y})`}
                onPointerDown={event => beginDrag(event, vertex.id)}
                onPointerMove={event => moveDrag(event, vertex.id)}
                onPointerUp={event => endDrag(event, vertex)}
                onPointerCancel={event => cancelDrag(event, vertex.id)}
                style={{ cursor: draggingId === vertex.id ? 'grabbing' : 'grab' }}
              >
                <HtmlDisplay html={vertex.label} />
              </g>
            )
          })}
        </g>
      </svg>

      {showDetails && selectedDetails && (
        <div
          style={{
            borderTop: '1px solid var(--vscode-editorWidget-border)',
            padding: '8px 4px 2px',
          }}
        >
          <HtmlDisplay html={selectedDetails} />
        </div>
      )}
    </div>
  )
}
