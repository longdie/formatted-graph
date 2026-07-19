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

type Selection =
  | { type: 'vertex'; id: string }
  | { type: 'edge'; index: number }
  | undefined

const dimensions = (shape: BoundingShape): { width: number; height: number } =>
  'rect' in shape
    ? shape.rect
    : { width: shape.circle.radius * 2, height: shape.circle.radius * 2 }

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

function edgePath(source: Point, target: Point): string {
  const dx = target.x - source.x
  const dy = target.y - source.y
  if (Math.abs(dy) >= Math.abs(dx) * 0.4) {
    const bend = Math.max(36, Math.abs(dy) * 0.45) * Math.sign(dy || 1)
    return `M ${source.x} ${source.y} C ${source.x} ${source.y + bend}, ${target.x} ${target.y - bend}, ${target.x} ${target.y}`
  }
  const bend = Math.max(36, Math.abs(dx) * 0.45) * Math.sign(dx || 1)
  return `M ${source.x} ${source.y} C ${source.x + bend} ${source.y}, ${target.x - bend} ${target.y}, ${target.x} ${target.y}`
}

function selfLoopGeometry(vertex: Vertex, center: Point): {
  source: Point
  target: Point
  midpoint: Point
  path: string
} {
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
  const [positions, setPositions] = React.useState(initialLayout.positions)
  const [selection, setSelection] = React.useState<Selection>()
  const [draggingId, setDraggingId] = React.useState<string>()
  const svgRef = React.useRef<SVGSVGElement>(null)
  const drag = React.useRef<{
    id: string
    pointerId: number
    moved: boolean
    startClient: Point
    offset: Point
  }>()
  const markerId = `formatted-graph-arrow-${React.useId().replace(/:/g, '')}`

  React.useEffect(() => {
    setPositions(initialLayout.positions)
    setSelection(undefined)
  }, [initialLayout])

  const pointerPosition = (event: React.PointerEvent<SVGGElement>): Point => {
    const svg = svgRef.current
    if (!svg) return { x: event.clientX, y: event.clientY }
    const point = svg.createSVGPoint()
    point.x = event.clientX
    point.y = event.clientY
    const matrix = svg.getScreenCTM()
    return matrix
      ? point.matrixTransform(matrix.inverse())
      : { x: event.clientX, y: event.clientY }
  }

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

  const canvasWidth = Math.max(initialLayout.width + 128, 480)
  const canvasHeight = Math.max(initialLayout.height + 128, 420)
  const renderedHeight = Math.min(canvasHeight, 720)
  const vertexById = new Map(vertices.map(vertex => [vertex.id, vertex]))
  const selectedDetails = selection?.type === 'vertex'
    ? vertexById.get(selection.id)?.details
    : selection?.type === 'edge'
      ? edges[selection.index]?.details
      : undefined

  return (
    <div style={{ width: '100%' }}>
      <svg
        ref={svgRef}
        width="100%"
        height={renderedHeight}
        viewBox={`${-canvasWidth / 2} ${-canvasHeight / 2} ${canvasWidth} ${canvasHeight}`}
        style={{ display: 'block', touchAction: 'none', userSelect: 'none' }}
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
              : {
                  source: boundaryPoint(sourceVertex, sourceCenter, targetCenter),
                  target: boundaryPoint(targetVertex, targetCenter, sourceCenter),
                  midpoint: {
                    x: (sourceCenter.x + targetCenter.x) / 2,
                    y: (sourceCenter.y + targetCenter.y) / 2,
                  },
                }
            const attributes = {
              ...attrsToObject(defaultEdgeAttrs),
              ...attrsToObject(edge.attrs),
              fill: 'none',
              markerEnd: `url(#${markerId})`,
              strokeLinecap: 'round' as const,
            }
            return (
              <g
                key={`${edge.source}-${edge.target}-${index}`}
                onClick={() => showDetails && edge.details && setSelection({ type: 'edge', index })}
                style={{ cursor: edge.details ? 'pointer' : 'default' }}
              >
                <path
                  d={'path' in geometry ? geometry.path : edgePath(geometry.source, geometry.target)}
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
