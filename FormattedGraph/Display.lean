import FormattedGraph.Graph
import Mathlib.Data.Finset.Sort
import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay

/-!
# FormattedGraph.Display

Conversion from generic graphs to ProofWidgets graph display data.
-/

namespace FormattedGraph

open Lean Server ProofWidgets
open scoped ProofWidgets.Jsx

/-- Presentation data for one graph node. -/
structure NodePresentation where
  label : Html
  boundingShape : GraphDisplay.BoundingShape
  details? : Option Html := none

/-- Presentation data for one graph edge. -/
structure EdgePresentation where
  label? : Option Html := none
  details? : Option Html := none
  attrs : Array (String × Json) := #[]

/-- Describes how an application's node identifiers and data are displayed. -/
class NodeRenderer (ν : Type u) [GraphWithData.NodeData ν] where
  id : ν → String
  render : (node : ν) → GraphWithData.δ ν → MetaM NodePresentation

/-- Describes how an application's edge identifiers and data are displayed. -/
class EdgeRenderer (ε : Type u) [GraphWithData.EdgeData ε] where
  render : (edge : ε) → GraphWithData.δ ε → MetaM EdgePresentation

/-- Values that can be converted to ProofWidgets graph properties. -/
class ToGraphDisplay (α : Type u) where
  toGraphDisplay : α → MetaM GraphDisplay.Props

namespace HierarchicalGraphDisplay

/-- Properties consumed by the draggable, top-to-bottom graph widget. -/
structure Props where
  vertices : Array GraphDisplay.Vertex
  edges : Array GraphDisplay.Edge
  defaultEdgeAttrs : Array (String × Json)
  showDetails : Bool := false
  deriving Inhabited, RpcEncodable

end HierarchicalGraphDisplay

/-- A top-to-bottom dependency layout whose nodes keep their user-adjusted positions. -/
@[widget_module]
def HierarchicalGraphDisplay : Component HierarchicalGraphDisplay.Props where
  javascript := include_str ".." / "widget" / "js" / "hierarchicalGraph.js"

/-- A compact rectangular node suitable for text labels. -/
def NodePresentation.text (label : String) (details? : Option Html := none) :
    NodePresentation :=
  let width := max 104 (label.length * 8 + 32)
  let x : Int := -(Int.ofNat width / 2)
  {
    label :=
      <g>
        <rect
          x={x}
          y={(-20 : Int)}
          width={width}
          height={40}
          rx={6}
          fill="var(--vscode-editor-background)"
          stroke="var(--vscode-editorWidget-border)"
          strokeWidth="1.25"
        />
        <text
          textAnchor="middle"
          dominantBaseline="middle"
          fill="var(--vscode-editor-foreground)"
        >{.text label}</text>
      </g>
    boundingShape := .rect width.toFloat 40
    details?
  }

/-- A text label suitable for the midpoint of an edge. -/
def EdgePresentation.text (label : String) (details? : Option Html := none) :
    EdgePresentation :=
  let width := max 36 (label.length * 7 + 16)
  let x : Int := -(Int.ofNat width / 2)
  {
    label? := some <| <g>
      <rect
        x={x}
        y={(-10 : Int)}
        width={width}
        height={20}
        rx={4}
        fill="var(--vscode-editor-background)"
      />
      <text
        textAnchor="middle"
        dominantBaseline="middle"
        fill="var(--vscode-editor-foreground)"
      >{.text label}</text>
    </g>
    details?
  }

/-- Convert a data-carrying graph to deterministic ProofWidgets display data. -/
def graphToProps
    [DecidableEq ν] [DecidableEq ε]
    [LinearOrder ν] [LinearOrder ε]
    [GraphWithData.NodeData ν] [GraphWithData.EdgeData ε]
    [NodeRenderer ν] [EdgeRenderer ε]
    {ep : ε → ν × ν}
    (graph : GraphWithData ep) : MetaM GraphDisplay.Props := do
  let mut vertices : Array GraphDisplay.Vertex := #[]
  let mut nodeIds : Array String := #[]

  for node in graph.V.attach.sort do
    let id := NodeRenderer.id node.val
    if id.isEmpty then
      throwError "a graph node was rendered with an empty ID"
    if nodeIds.contains id then
      throwError "duplicate rendered node ID: {id}"
    let presentation ← NodeRenderer.render node.val (graph.data_v node)
    nodeIds := nodeIds.push id
    vertices := vertices.push {
      id
      label := presentation.label
      boundingShape := presentation.boundingShape
      details? := presentation.details?
    }

  let mut edges : Array GraphDisplay.Edge := #[]
  let mut endpointPairs : Array (String × String) := #[]

  for edge in graph.E.attach.sort do
    let (source, target) := ep edge.val
    let sourceId := NodeRenderer.id source
    let targetId := NodeRenderer.id target
    let endpointPair := (sourceId, targetId)
    if endpointPairs.contains endpointPair then
      throwError "parallel edges are not supported between {sourceId} and {targetId}"
    let presentation ← EdgeRenderer.render edge.val (graph.data_e edge)
    endpointPairs := endpointPairs.push endpointPair
    edges := edges.push {
      source := sourceId
      target := targetId
      attrs := presentation.attrs
      label? := presentation.label?
      details? := presentation.details?
    }

  return { vertices, edges, showDetails := true }

instance graphWithDataToGraphDisplay
    [DecidableEq ν] [DecidableEq ε]
    [LinearOrder ν] [LinearOrder ε]
    [GraphWithData.NodeData ν] [GraphWithData.EdgeData ε]
    [NodeRenderer ν] [EdgeRenderer ε]
    {ep : ε → ν × ν} :
    ToGraphDisplay (GraphWithData ep) where
  toGraphDisplay := graphToProps

/-- Build the HTML panel displayed by `#show_graph`. -/
def graphHtml [ToGraphDisplay α] (graph : α) : MetaM Html := do
  let props ← ToGraphDisplay.toGraphDisplay graph
  return (<details «open»={true}>
      <summary className="mv2 pointer">Formatted graph</summary>
      <div style={json% { minHeight: "360px", width: "100%" }}>
        <HierarchicalGraphDisplay
          vertices={props.vertices}
          edges={props.edges}
          defaultEdgeAttrs={props.defaultEdgeAttrs}
          showDetails={props.showDetails}
        />
      </div>
    </details>)

end FormattedGraph
