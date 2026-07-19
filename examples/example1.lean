import FormattedGraph
import Mathlib.Data.String.Basic

/-!
# A small workflow graph

This is the main visualization example for FormattedGraph. It contains four
nodes and three directed edges, with no self-loops or parallel edges.
-/

namespace FormattedGraph.Examples.Example1

structure NodeId where
  value : String
deriving DecidableEq, Repr

inductive EdgeId where
  | inputToParse
  | parseToCheck
  | checkToOutput
deriving DecidableEq, Repr

instance : LinearOrder NodeId :=
  LinearOrder.lift' (fun node => node.value) (by
    intro a b h
    cases a
    cases b
    simp_all)

def EdgeId.rank : EdgeId → Nat
  | .inputToParse => 0
  | .parseToCheck => 1
  | .checkToOutput => 2

instance : LinearOrder EdgeId :=
  LinearOrder.lift' EdgeId.rank (by
    intro a b h
    cases a <;> cases b <;> simp_all [EdgeId.rank])

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

instance : FormattedGraph.NodeRenderer NodeId where
  id node := node.value
  render _ data :=
    pure <| FormattedGraph.NodePresentation.text data.label (.some (.text data.description))

instance : FormattedGraph.EdgeRenderer EdgeId where
  render _ data :=
    pure <| FormattedGraph.EdgePresentation.text data.label

def inputNode : NodeId := ⟨"input"⟩
def parseNode : NodeId := ⟨"parse"⟩
def checkNode : NodeId := ⟨"check"⟩
def outputNode : NodeId := ⟨"output"⟩

def inputToParse : EdgeId := .inputToParse
def parseToCheck : EdgeId := .parseToCheck
def checkToOutput : EdgeId := .checkToOutput

def endpoints : EdgeId → NodeId × NodeId
  | .inputToParse => (inputNode, parseNode)
  | .parseToCheck => (parseNode, checkNode)
  | .checkToOutput => (checkNode, outputNode)

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

#show_graph exampleGraph

end FormattedGraph.Examples.Example1
