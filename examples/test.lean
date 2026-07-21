import FormattedGraph.Graph

namespace test

open GraphWithData

open Data

namespace Shape

structure Coordinate where
  x : Float
  y : Float

structure Size where
  size : Float
  h : size > 0 := by native_decide

end Shape

structure NodeFormat where
  size : Shape.Size
  pos : Shape.Coordinate

structure NodeDataType where
  content : String
  format : NodeFormat

structure EdgeFormat where
  pos1 : Shape.Coordinate
  pos2 : Shape.Coordinate

structure EdgeDataType where
  content : String
  format : EdgeFormat

instance : NodeData Nat where
  data_type := NodeDataType

instance : EdgeData (Nat × Nat) where
  data_type := EdgeDataType

abbrev ep : Nat × Nat → Nat × Nat := id

def NodeDataDefault : NodeDataType where
  content := ""
  format := ⟨.mk 1, ⟨0, 0⟩⟩

def NodeDataZt : NodeDataType where
  content := "Zhu tao"
  format := ⟨.mk 10, ⟨1, 0⟩⟩

def NodeDataDzn : NodeDataType where
  content := "Dong Zineng"
  format := ⟨.mk 10, ⟨-1, 0⟩⟩

def EdgeData.mk' (content : String) (dv1 dv2 : NodeDataType) : EdgeDataType where
  content := content
  format := ⟨dv1.format.pos, dv2.format.pos⟩

def graphExample : GraphWithData ep :=
  (((empty
  ).add_node_unsafe
    1 NodeDataZt
  ).add_node_unsafe
    2 NodeDataDzn
  ).add_edge_unsafe
    (1,2)
    (EdgeData.mk' "" NodeDataZt NodeDataDzn)
    (by graph_head_simp [])

def add_edge_info' (e : Nat × Nat) (contents : String)
    (G : GraphWithData ep) : InfoResult ep :=
  if h : e ∉ G.E ∧ (ep e).1 ∈ G.V ∧ (ep e).2 ∈ G.V
  then ⟨.ok,
    Graph.add_edge_unsafe e G.toGraph h.2,
    G.data_v,
    fun ⟨e', _⟩ =>
      if he' : e' ∈ G.E
      then G.data_e ⟨e', he'⟩
      else ⟨contents, ⟨
          (G.data_v ⟨(ep e).1, h.2.1⟩).format.pos,
          (G.data_v ⟨(ep e).2, h.2.2⟩).format.pos
        ⟩⟩
  ⟩
  else ⟨(Graph.add_edge e G.toGraph).1, G⟩

def add_edge' (e : Nat × Nat) (contents : String)
    (G : GraphWithData ep) : Result ep :=
  (add_edge_info' e contents G).allow []

abbrev Builder.addEdge'
    (e : Nat × Nat) (contents : String)
  : Builder ep PUnit :=
  Builder.modifyE (fun G => add_edge' e contents G)

def graphExampleM : Result ep :=
  Builder.build do
    Builder.addNode 1 NodeDataZt
    Builder.addNode 2 NodeDataDzn
    Builder.addEdge' (1, 2) ""

#time example : graphExampleM = .ok graphExample := by
  unfold graphExampleM graphExample

  unfold Builder.build

  rw [Builder.modify_fold];
  rw [Builder.exec_modifyE];
  graph_head_simp [add_edge', add_edge_info']

  rw [Builder.modify_fold];
  rw [Builder.exec_modifyE];
  graph_head_simp [add_edge', add_edge_info']

  rw [Builder.exec_modifyE];
  graph_head_simp [add_edge', add_edge_info']

  rfl

#time example : graphExampleM = .ok graphExample := by
  unfold graphExampleM graphExample

  unfold Builder.build
  repeat(
    try rw [Builder.modify_fold];
    try rw [Builder.exec_modifyE];
    graph_head_simp [add_edge', add_edge_info']
  )

  rfl

#time example : graphExampleM = .ok graphExample := by
  unfold graphExampleM graphExample
  graph_simp [add_edge', add_edge_info']
  rfl

def graphExample2 : Result ep :=
  Builder.build do
    Builder.addNode 1 NodeDataZt
    Builder.addNode 2 NodeDataDzn
    Builder.addEdge' (1, 3) ""

example : graphExample2 = sorry
  -- graphExample2 =
  -- .error (
  --   .edge_error (1, 3) (
  --     .graph_edge_error
  --     .add_edge_end_point_missing
  --   )
  -- )
  := by
  unfold graphExample2
  graph_simp [add_edge', add_edge_info']
  sorry

end test
