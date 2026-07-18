import FormattedGraph.Graph

/-!
# A small workflow graph

This is the main visualization example for FormattedGraph. It contains four
nodes and three directed edges, with no self-loops or parallel edges.
-/

namespace FormattedGraph.Examples.Example1

structure NodeId where
  value : String
deriving DecidableEq, Repr

structure EdgeId where
  value : String
  source : NodeId
  target : NodeId
deriving DecidableEq, Repr

structure NodeInfo where
  label : String
  description : String
deriving Repr

structure EdgeInfo where
  label : String
deriving Repr

instance : WithData.NodeData NodeId where
  data_type := NodeInfo

instance : WithData.EdgeData EdgeId where
  data_type := EdgeInfo

def inputNode : NodeId := ⟨"input"⟩
def parseNode : NodeId := ⟨"parse"⟩
def checkNode : NodeId := ⟨"check"⟩
def outputNode : NodeId := ⟨"output"⟩

def inputToParse : EdgeId := ⟨"input-to-parse", inputNode, parseNode⟩
def parseToCheck : EdgeId := ⟨"parse-to-check", parseNode, checkNode⟩
def checkToOutput : EdgeId := ⟨"check-to-output", checkNode, outputNode⟩

def endpoints (edge : EdgeId) : NodeId × NodeId :=
  (edge.source, edge.target)

open WithData

def missingNodeData : NodeInfo :=
  ⟨"Unknown", "Automatically added endpoint"⟩

def exampleGraph : GraphWithData endpoints :=
  GraphWithData.empty endpoints
    |> GraphWithData.add_node inputNode
      (NodeInfo.mk "Input" "Raw input data")
    |> GraphWithData.add_node parseNode
      (NodeInfo.mk "Parse" "Parse the input")
    |> GraphWithData.add_node checkNode
      (NodeInfo.mk "Check" "Validate the parsed data")
    |> GraphWithData.add_node outputNode
      (NodeInfo.mk "Output" "Produce the final result")
    |> GraphWithData.add_edge inputToParse
      (EdgeInfo.mk "next") missingNodeData
    |> GraphWithData.add_edge parseToCheck
      (EdgeInfo.mk "next") missingNodeData
    |> GraphWithData.add_edge checkToOutput
      (EdgeInfo.mk "next") missingNodeData

#check exampleGraph

-- After the InfoView command is implemented, this example will end with:
-- #show_graph exampleGraph

end FormattedGraph.Examples.Example1
