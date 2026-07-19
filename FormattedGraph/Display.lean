import FormattedGraph.Graph
import Mathlib.Data.Finset.Sort
import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay

/-!
# FormattedGraph.Display

Conversion from generic graphs to ProofWidgets graph display data.
-/

namespace FormattedGraph

open Lean ProofWidgets
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
class NodeRenderer (ν : Type u) [WithData.NodeData ν] where
  id : ν → String
  render : (node : ν) → WithData.δ ν → MetaM NodePresentation

/-- Describes how an application's edge identifiers and data are displayed. -/
class EdgeRenderer (ε : Type u) [WithData.EdgeData ε] where
  render : (edge : ε) → WithData.δ ε → MetaM EdgePresentation

/-- Values that can be converted to ProofWidgets graph properties. -/
class ToGraphDisplay (α : Type u) where
  toGraphDisplay : α → MetaM GraphDisplay.Props

/-- A compact rectangular node suitable for text labels. -/
def NodePresentation.text (label : String) (details? : Option Html := none) :
    NodePresentation :=
  let width := max 88 (label.length * 8 + 24)
  let x : Int := -(Int.ofNat width / 2)
  {
    label :=
      <g>
        <rect
          x={x}
          y={(-18 : Int)}
          width={width}
          height={36}
          rx={6}
          fill="var(--vscode-editor-background)"
          stroke="var(--vscode-editor-foreground)"
          strokeWidth="1.5"
        />
        <text
          textAnchor="middle"
          dominantBaseline="middle"
          fill="var(--vscode-editor-foreground)"
        >{.text label}</text>
      </g>
    boundingShape := .rect width.toFloat 36
    details?
  }

/-- A text label suitable for the midpoint of an edge. -/
def EdgePresentation.text (label : String) (details? : Option Html := none) :
    EdgePresentation :=
  {
    label? := some <| <text
      textAnchor="middle"
      dominantBaseline="middle"
      fill="var(--vscode-editor-foreground)"
    >{.text label}</text>
    details?
  }

/-- Convert a data-carrying graph to deterministic ProofWidgets display data. -/
def graphToProps
    [DecidableEq ν] [DecidableEq ε]
    [LinearOrder ν] [LinearOrder ε]
    [WithData.NodeData ν] [WithData.EdgeData ε]
    [NodeRenderer ν] [EdgeRenderer ε]
    {ep : ε → ν × ν}
    (graph : WithData.GraphWithData ep) : MetaM GraphDisplay.Props := do
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
    [WithData.NodeData ν] [WithData.EdgeData ε]
    [NodeRenderer ν] [EdgeRenderer ε]
    {ep : ε → ν × ν} :
    ToGraphDisplay (WithData.GraphWithData ep) where
  toGraphDisplay := graphToProps

/-- Build the HTML panel displayed by `#show_graph`. -/
def graphHtml [ToGraphDisplay α] (graph : α) : MetaM Html := do
  let props ← ToGraphDisplay.toGraphDisplay graph
  return (<details «open»={true}>
      <summary className="mv2 pointer">Formatted graph</summary>
      <div style={json% { minHeight: "360px", width: "100%" }}>
        <GraphDisplay
          vertices={props.vertices}
          edges={props.edges}
          defaultEdgeAttrs={props.defaultEdgeAttrs}
          forces={props.forces}
          showDetails={props.showDetails}
        />
      </div>
    </details>)

end FormattedGraph
