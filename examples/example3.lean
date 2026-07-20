import FormattedGraph
import Mathlib.Data.String.Basic

/-!
# FormattedGraph architecture

A self-describing graph of the path from graph construction to an interactive
InfoView panel. Backend data, renderers, layout, and interaction all converge
on the final widget.
-/

namespace FormattedGraph.Examples.Example3

structure NodeId where
  value : String
deriving DecidableEq, Repr

inductive EdgeId where
  | addNodeToBuild
  | addEdgeToBuild
  | buildToResult
  | resultToConversion
  | nodeRendererToConversion
  | edgeRendererToConversion
  | conversionToWidget
  | dagreToWidget
  | pointerToWidget
  | commandToConversion
  | commandToInfoView
  | widgetToInfoView
deriving DecidableEq, Repr

instance : LinearOrder NodeId :=
  LinearOrder.lift' (fun node => node.value) (by
    intro a b h
    cases a
    cases b
    simp_all)

def EdgeId.rank : EdgeId → Nat
  | .addNodeToBuild => 0
  | .addEdgeToBuild => 1
  | .buildToResult => 2
  | .resultToConversion => 3
  | .nodeRendererToConversion => 4
  | .edgeRendererToConversion => 5
  | .conversionToWidget => 6
  | .dagreToWidget => 7
  | .pointerToWidget => 8
  | .commandToConversion => 9
  | .commandToInfoView => 10
  | .widgetToInfoView => 11

instance : LinearOrder EdgeId :=
  LinearOrder.lift' EdgeId.rank (by
    intro a b h
    cases a <;> cases b <;> simp_all [EdgeId.rank])

structure NodeInfo where
  label : String
  category : String
  description : String
deriving Repr

structure EdgeInfo where
  label : String
  description : String
deriving Repr

instance : Data.NodeData NodeId where
  data_type := NodeInfo

instance : Data.EdgeData EdgeId where
  data_type := EdgeInfo

instance : FormattedGraph.NodeRenderer NodeId where
  id node := node.value
  render _ data :=
    pure <| FormattedGraph.NodePresentation.text data.label <|
      some (.text s!"{data.category}: {data.description}")

instance : FormattedGraph.EdgeRenderer EdgeId where
  render _ data :=
    pure <| FormattedGraph.EdgePresentation.text data.label <|
      some (.text data.description)

def addNode : NodeId := ⟨"builder-add-node"⟩
def addEdge : NodeId := ⟨"builder-add-edge"⟩
def build : NodeId := ⟨"builder-build"⟩
def graphResult : NodeId := ⟨"graph-result"⟩
def nodeRenderer : NodeId := ⟨"node-renderer"⟩
def edgeRenderer : NodeId := ⟨"edge-renderer"⟩
def conversion : NodeId := ⟨"graph-to-props"⟩
def dagre : NodeId := ⟨"dagre-layout"⟩
def pointerEvents : NodeId := ⟨"pointer-events"⟩
def widget : NodeId := ⟨"hierarchical-widget"⟩
def showGraph : NodeId := ⟨"show-graph-command"⟩
def infoView : NodeId := ⟨"infoview-panel"⟩

def endpoints : EdgeId → NodeId × NodeId
  | .addNodeToBuild => (addNode, build)
  | .addEdgeToBuild => (addEdge, build)
  | .buildToResult => (build, graphResult)
  | .resultToConversion => (graphResult, conversion)
  | .nodeRendererToConversion => (nodeRenderer, conversion)
  | .edgeRendererToConversion => (edgeRenderer, conversion)
  | .conversionToWidget => (conversion, widget)
  | .dagreToWidget => (dagre, widget)
  | .pointerToWidget => (pointerEvents, widget)
  | .commandToConversion => (showGraph, conversion)
  | .commandToInfoView => (showGraph, infoView)
  | .widgetToInfoView => (widget, infoView)

def formattedGraphPipeline : GraphWithData.Result endpoints :=
  GraphWithData.Builder.build do
    GraphWithData.Builder.addNode addNode
      { label := "Builder.addNode"
        category := "Graph backend"
        description := "Adds a typed node and its data to the graph." }
    GraphWithData.Builder.addNode addEdge
      { label := "Builder.addEdge"
        category := "Graph backend"
        description := "Adds a typed edge after checking its endpoints." }
    GraphWithData.Builder.addNode build
      { label := "Builder.build"
        category := "Graph backend"
        description := "Runs graph operations from an empty graph." }
    GraphWithData.Builder.addNode graphResult
      { label := "GraphWithData.Result"
        category := "Graph backend"
        description := "Contains either a valid graph or a build error." }
    GraphWithData.Builder.addNode nodeRenderer
      { label := "NodeRenderer"
        category := "Rendering interface"
        description := "Maps node IDs and data to labels and details." }
    GraphWithData.Builder.addNode edgeRenderer
      { label := "EdgeRenderer"
        category := "Rendering interface"
        description := "Maps edge data to labels, details, and SVG attrs." }
    GraphWithData.Builder.addNode conversion
      { label := "graphToProps"
        category := "Lean display layer"
        description :=
          "Converts GraphWithData into ProofWidgets graph properties." }
    GraphWithData.Builder.addNode dagre
      { label := "Dagre layout"
        category := "Widget layout"
        description := "Computes the initial top-to-bottom DAG layout." }
    GraphWithData.Builder.addNode pointerEvents
      { label := "Pointer events"
        category := "Widget interaction"
        description := "Updates node positions while the user drags them." }
    GraphWithData.Builder.addNode widget
      { label := "Hierarchical widget"
        category := "TypeScript widget"
        description := "Draws nodes, edges, labels, arrows, and details." }
    GraphWithData.Builder.addNode showGraph
      { label := "#show_graph"
        category := "Lean command"
        description := "Elaborates a graph expression and opens its panel." }
    GraphWithData.Builder.addNode infoView
      { label := "InfoView panel"
        category := "Editor output"
        description := "Hosts the final interactive graph in VS Code." }

    GraphWithData.Builder.addEdge .addNodeToBuild
      { label := "operation"
        description := "Node additions are executed by the builder." }
    GraphWithData.Builder.addEdge .addEdgeToBuild
      { label := "operation"
        description := "Edge additions are executed by the builder." }
    GraphWithData.Builder.addEdge .buildToResult
      { label := "returns"
        description := "The builder returns an error-aware graph result." }
    GraphWithData.Builder.addEdge .resultToConversion
      { label := "graph data"
        description := "The successful graph supplies vertices and edges." }
    GraphWithData.Builder.addEdge .nodeRendererToConversion
      { label := "renders nodes"
        description := "NodeRenderer supplies stable IDs and presentation." }
    GraphWithData.Builder.addEdge .edgeRendererToConversion
      { label := "renders edges"
        description := "EdgeRenderer supplies edge presentation data." }
    GraphWithData.Builder.addEdge .conversionToWidget
      { label := "props"
        description := "Encoded graph properties cross into the widget." }
    GraphWithData.Builder.addEdge .dagreToWidget
      { label := "initial layout"
        description := "Dagre provides deterministic node positions." }
    GraphWithData.Builder.addEdge .pointerToWidget
      { label := "drag updates"
        description := "Pointer events preserve user-adjusted positions." }
    GraphWithData.Builder.addEdge .commandToConversion
      { label := "evaluates"
        description := "The command requests conversion of its graph term." }
    GraphWithData.Builder.addEdge .commandToInfoView
      { label := "saves panel"
        description := "Widget panel information is attached to the command." }
    GraphWithData.Builder.addEdge .widgetToInfoView
      { label := "renders"
        description := "The custom component is displayed in InfoView." }

#check formattedGraphPipeline

#show_graph formattedGraphPipeline

end FormattedGraph.Examples.Example3
