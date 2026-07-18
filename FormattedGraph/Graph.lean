import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

namespace FiniteDirectedGraph

variable {ν : Type*} {ε : Type*} [DecidableEq ν] [DecidableEq ε]

/--
finite directed graph
* `ν`: the type of all possible nodes
* `ε`: the type of all possible edges
* `ep`: the endpoints of each edge in `ε`
* `V`: the finite set of nodes
* `E`: the finite set of edges
* `h`: the hypothesis that the endpoints of each edge in `E` is in `V`
-/
structure Graph (ep : ε → ν × ν) where
  V : Finset ν
  E : Finset ε
  h : ∀ {e : ε}, e ∈ E → (ep e).1 ∈ V ∧ (ep e).2 ∈ V

/--
`discrete ep V`: the discrete graph with a given node set `V` and no edges.
-/
def discrete (ep : ε → ν × ν) (V : Finset ν) : Graph ep where
  V := V
  E := ∅
  h := by intro _ he; simp at he

/--
`empty ep`: the empty graph, i.e., the one with no nodes and edges.
-/
def empty {ep : ε → ν × ν} : Graph ep :=
  discrete ep ∅

/--
`add_node v G`: to add a node `v` to a graph `G`.
If `v` is already in `G`, then nothing happens.
-/
def add_node {ep : ε → ν × ν} (v : ν)
    (G : Graph ep) : Graph ep where
  V := {v} ∪ G.V
  E := G.E
  h := by intro _ h; simp [G.h, h]

/--
`add_edge e G`: to add an edge `e` to a graph `G`.
If `e` is already in `G`, then nothing happens.
If some of the endpoints of `e` is not in `G`, then add it.
-/
def add_edge {ep : ε → ν × ν} (e : ε)
    (G : Graph ep) : Graph ep where
  V := {(ep e).1} ∪ {(ep e).2} ∪ G.V
  E := {e} ∪ G.E
  h := by
    intro _ h; simp at h
    rcases h with h | h <;> simp [G.h, h]

/--
`remove_node v G`: to remove a node `v` from a graph `G`.
If `v` is not in `G`, then nothing happens.
If `v` is in `G`, then all the edges that are adjacent to `v` are removed.
-/
def remove_node {ep : ε → ν × ν} (v : ν)
    (G : Graph ep) : Graph ep where
  V := G.V \ {v}
  E := G.E \ { e ∈ G.E | (ep e).1 = v ∨ (ep e).2 = v}
  h := by intro _ h; simp at h; simp [G.h, h]

/--
`remove_edge e G`: to remove an edge `e` from a graph `G`.
If `e` is not in `G`, then nothing happens.
-/
def remove_edge {ep : ε → ν × ν} (e : ε)
    (G : Graph ep) : Graph ep where
  V := G.V
  E := G.E \ {e}
  h := by intro _ h; simp at h; simp [G.h, h]

structure PushForwardStruct (ep : ε → ν × ν) where
  rv : ν → ν
  re : ε → ε
  h1 : ∀ {e : ε}, (ep (re e)).1 = rv (ep e).1
  h2 : ∀ {e : ε}, (ep (re e)).2 = rv (ep e).2

/--
`replace_node v v' re ... G`: to replace a node `v` by `v'` from a graph `G`.
If `v` is not in `G`, then nothing happens.
If `v` is in `G`, then all the edges that are adjacent to `v` are removed.
-/
def push_forward {ep : ε → ν × ν}
    (f : PushForwardStruct ep)
    (G : Graph ep) : Graph ep where
  V := G.V.image f.rv
  E := G.E.image f.re
  h := by
    intro _ h; simp at h
    rcases h with ⟨e, ⟨h, heq⟩⟩; subst heq
    constructor <;> simp
    . exists (ep e).1
      simp [G.h, f.h1, h]
    . exists (ep e).2
      simp [G.h, f.h2, h]

structure PushForwardEdgeStruct (ep : ε → ν × ν) where
  r : ε → ε
  h : ∀ {e : ε}, (ep (r e)) = (ep e)

def PushForwardEdgeStruct.toPushForwardStruct {ep : ε → ν × ν}
    (fe : PushForwardEdgeStruct ep) : PushForwardStruct ep where
  rv := id
  re := fe.r
  h1 := by intro e; simp; rw[fe.h]
  h2 := by intro e; simp; rw[fe.h]

def push_forward_edge {ep : ε → ν × ν}
    (f : PushForwardEdgeStruct ep)
    (G : Graph ep) : Graph ep :=
  push_forward f.toPushForwardStruct G

/--
`add_edge_safe_raw e G h1 h2`: to add an edge `e` to a graph `G`
  under the assumptions that both endpoints of `e` are in `G`.

This operation preserves the node set.
-/
def add_edge_safe {ep : ε → ν × ν} (e : ε)
    (G : Graph ep)
    (h1 : (ep e).1 ∈ G.V)
    (h2 : (ep e).2 ∈ G.V)
  : Graph ep where
  V := G.V
  E := G.E ∪ {e}
  h := by
    intro _ h; simp at h
    rcases h with h | h
    . subst h; constructor <;> assumption
    . exact G.h h

end FiniteDirectedGraph









namespace GraphWithData

variable {ν : Type*} {ε : Type*} [DecidableEq ν] [DecidableEq ε]

class Data (α : Type*) where
  data_type : Type*

class NodeData (ν : Type*) extends Data ν

class EdgeData (ν : Type*) extends Data ν

variable [node_data_type : NodeData ν] [edge_data_type : EdgeData ε]

abbrev δ (α : Type*) [data_type : Data α] := data_type.data_type

end GraphWithData

structure GraphWithData
  {ν : Type*} {ε : Type*}
  [DecidableEq ν] [DecidableEq ε]
  [node_data_type : GraphWithData.NodeData ν]
  [edge_data_type : GraphWithData.EdgeData ε]
  (ep : ε → ν × ν)
    extends FiniteDirectedGraph.Graph ep where
  data_v : V → GraphWithData.δ ν
  data_e : E → GraphWithData.δ ε

namespace GraphWithData

variable {ν : Type*} {ε : Type*} [DecidableEq ν] [DecidableEq ε]
variable [node_data_type : NodeData ν] [edge_data_type : EdgeData ε]

/--
`empty ep`: the empty graph, i.e., the one with no nodes and edges.
-/
def empty {ep : ε → ν × ν} : GraphWithData ep where
  toGraph := FiniteDirectedGraph.empty
  data_v := fun ⟨_, h⟩ => (Finset.notMem_empty _ h).elim
  data_e := fun ⟨_, h⟩ => (Finset.notMem_empty _ h).elim

/--
`discrete ep dv V`: the discrete graph with a given node set `V` and no edges.
Each node is stored with data `dv`.
-/
def discrete (ep : ε → ν × ν) (V : Finset ν) (dv : δ ν)
    : GraphWithData ep where
  toGraph := FiniteDirectedGraph.discrete ep V
  data_v := fun _ => dv
  data_e := fun ⟨_, h⟩ => (Finset.notMem_empty _ h).elim

/--
`add_node v dv G`: to add a node `v` to a graph `G`.
If `v` is already in `G`, then nothing happens.
-/
def add_node {ep : ε → ν × ν} (v : ν) (dv : δ ν)
    (G : GraphWithData ep) : GraphWithData ep where
  toGraph := FiniteDirectedGraph.add_node v G.toGraph
  data_v := fun ⟨v', _⟩ =>
    if hin : v' ∈ G.V
    then G.data_v ⟨v', hin⟩
    else dv
  data_e := G.data_e

/--
`add_edge e de dv G`: to add an edge `e` with data `de` to a graph `G`.
If `e` is already in `G`, then nothing happens.
If some of the endpoints of `e` is not in `G`, then add it with data `dv`,
  which serves as a default value.
-/
def add_edge {ep : ε → ν × ν} (e : ε) (de : δ ε) (dv : δ ν)
    (G : GraphWithData ep) : GraphWithData ep where
  toGraph := FiniteDirectedGraph.add_edge e G.toGraph
  data_v := fun ⟨v', _⟩ =>
    if hin : v' ∈ G.V
    then G.data_v ⟨v', hin⟩
    else dv
  data_e := fun ⟨e', _⟩ =>
    if hin : e' ∈ G.E
    then G.data_e ⟨e', hin⟩
    else de

/--
`remove_node v G`: to remove a node `v` from a graph `G`.
If `v` is not in `G`, then nothing happens.
If `v` is in `G`, then all the edges that are adjacent to `v` are removed.
-/
def remove_node {ep : ε → ν × ν} (v : ν)
    (G : GraphWithData ep) : GraphWithData ep where
  toGraph := FiniteDirectedGraph.remove_node v G.toGraph
  data_v := fun ⟨v', h⟩ =>
    G.data_v ⟨v', by
      unfold FiniteDirectedGraph.remove_node at h
      simp at h
      exact h.1
    ⟩
  data_e := fun ⟨e', h⟩ =>
    G.data_e ⟨e', by
      unfold FiniteDirectedGraph.remove_node at h
      simp at h
      exact h.1
    ⟩

/--
`remove_edge e G`: to remove an edge `e` from a graph `G`.
If `e` is not in `G`, then nothing happens.
-/
def remove_edge {ep : ε → ν × ν}
    (e : ε) (G : GraphWithData ep) : GraphWithData ep where
  toGraph := FiniteDirectedGraph.remove_edge e G.toGraph
  data_v := G.data_v
  data_e := fun ⟨e', h⟩ =>
    G.data_e ⟨e', by
      unfold FiniteDirectedGraph.remove_edge at h
      simp at h
      exact h.1
    ⟩

/--
`edit_node v dv G`: to replace the data of node `v` in `G` by `dv`.
If `v` is not in `G`, then nothing happens.
-/
def edit_node {ep : ε → ν × ν} (v : ν) (dv : δ ν)
    (G : GraphWithData ep) : GraphWithData ep where
  toGraph := G.toGraph
  data_v := fun ⟨v', h⟩ =>
    if v' = v then dv
    else G.data_v ⟨v', h⟩
  data_e := G.data_e

/--
`edit_edge e de G`: to replace the data of edge `e` in `G` by `de`.
If `e` is not in `G`, then nothing happens.
-/
def edit_edge {ep : ε → ν × ν} (e : ε) (de : δ ε)
    (G : GraphWithData ep) : GraphWithData ep where
  toGraph := G.toGraph
  data_v := G.data_v
  data_e := fun ⟨e', h⟩ =>
    if e' = e then de
    else G.data_e ⟨e', h⟩

inductive GraphWithDataError (ν ε : Type*) where
  | add_node_existing (v : ν)
  | add_edge_existing (e : ε)
  | add_edge_start_point_missing (e : ε)
  | add_edge_end_point_missing (e : ε)
  | remove_node_missing (v : ν)
  | remove_edge_missing (e : ε)
  | edit_node_missing (v : ν)
  | edit_edge_missing (e : ε)

def GraphWithDataM (ep : ε → ν × ν) :=
  Except (GraphWithDataError ν ε) (GraphWithData ep)

/--
`add_node v dv G`: to add a node `v` with data `dv` to a graph `G`.
If `v` is already in `G`, then error `add_node_existing v` will be thrown out.
-/
def add_node_safe {ep : ε → ν × ν} (v : ν) (dv : δ ν)
    (G : GraphWithData ep) : GraphWithDataM ep :=
  if v ∈ G.V
  then .error $ .add_node_existing v
  else .ok (G.add_node v dv)

/--
`add_edge_safe e de G`: to add an edge `e` with data `de` to a graph `G`.
If `e` is already in `G`, then error `add_node_existing e` will be thrown out.
If some of the endpoints of `e` is not in `G`, then error
  `add_edge_start_point_missing` or `add_edge_end_point_missing` will be thrown
  out.
-/
def add_edge_safe {ep : ε → ν × ν} (e : ε) (de : δ ε)
    (G : GraphWithData ep) : GraphWithDataM ep :=
  if e ∈ G.E then .error $ .add_edge_existing e
  else if h1 : (ep e).1 ∈ G.V then
    if h2 : (ep e).2 ∈ G.V then
      .ok ⟨
        FiniteDirectedGraph.add_edge_safe e G.toGraph h1 h2,
        G.data_v,
        fun ⟨e', _⟩ =>
          if he' : e' ∈ G.E
          then G.data_e ⟨e', he'⟩
          else de
      ⟩
    else .error $ .add_edge_end_point_missing e
  else .error $ .add_edge_start_point_missing e

end GraphWithData






namespace test

open GraphWithData

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

def ep : Nat × Nat → Nat × Nat := id

def NodeDataDefault : NodeDataType where
  content := ""
  format := ⟨.mk 1, ⟨0, 0⟩⟩

def NodeDataLxy : NodeDataType where
  content := "Liu Xiaoyang"
  format := ⟨.mk 10, ⟨1, 0⟩⟩

def NodeDataDzn : NodeDataType where
  content := "Dong Zineng"
  format := ⟨.mk 10, ⟨-1, 0⟩⟩

def EdgeData.mk' (content : String) (dv1 dv2 : NodeDataType) : EdgeDataType where
  content := content
  format := ⟨dv1.format.pos, dv2.format.pos⟩

def graphExample : GraphWithData ep :=
  (((empty
  ).add_node
    1 NodeDataLxy
  ).add_node
    2 NodeDataDzn
  ).add_edge
    (1,2)
    (EdgeData.mk' "" NodeDataLxy NodeDataDzn)
    NodeDataDefault
/--
`add_edge_safe e de G`: to add an edge `e` with data `de` to a graph `G`.
If `e` is already in `G`, then error `add_node_existing e` will be thrown out.
If some of the endpoints of `e` is not in `G`, then error
  `add_edge_start_point_missing` or `add_edge_end_point_missing` will be thrown
  out.
-/
def add_edge_safe' (e : Nat × Nat) (contents : String)
    (G : GraphWithData ep) : GraphWithDataM ep :=
  if e ∈ G.E then .error $ .add_edge_existing e
  else if h1 : (ep e).1 ∈ G.V then
    if h2 : (ep e).2 ∈ G.V then
      .ok ⟨
        FiniteDirectedGraph.add_edge_safe e G.toGraph h1 h2,
        G.data_v,
        fun ⟨e', _⟩ =>
          if he' : e' ∈ G.E
          then G.data_e ⟨e', he'⟩
          else ⟨contents, ⟨
              (G.data_v ⟨(ep e).1, h1⟩).format.pos,
              (G.data_v ⟨(ep e).2, h2⟩).format.pos
            ⟩⟩
      ⟩
    else .error $ .add_edge_end_point_missing e
  else .error $ .add_edge_start_point_missing e

def graphExampleM : GraphWithDataM ep := do
  let G0 ← (pure empty)
  let G1 ← G0.add_node_safe 1 NodeDataLxy
  let G2 ← G1.add_node_safe 2 NodeDataDzn
  let G3 ← add_edge_safe' (1,2) "" G2
  pure G3

theorem except_ok_fold (x : α) (m : α → @Except β α)
  : (do
      let y ← Except.ok x
      m y)
    = m x :=
  rfl

example : graphExampleM = .ok graphExample := by
  have h1 : 1 ∉ (empty (ep := ep)).V := by
    apply Finset.notMem_empty
  have h2 : 2 ∉ (add_node 1 NodeDataLxy (empty (ep := ep))).V := by
    unfold add_node; simp
    unfold FiniteDirectedGraph.add_node; simp
    apply Finset.notMem_empty
  have h3 :
    (1, 2) ∉
    (add_node 2 NodeDataDzn (add_node 1 NodeDataLxy (empty (ep := ep)))).E
  := by
    unfold add_node; simp
    unfold FiniteDirectedGraph.add_node; simp
    apply Finset.notMem_empty
  have h4 :
    (ep (1, 2)).1 ∈
    (add_node 2 NodeDataDzn (add_node 1 NodeDataLxy (empty (ep := ep)))).V
  := by
    unfold add_node; simp
    unfold FiniteDirectedGraph.add_node; simp
    left; rfl
  have h5 :
    (ep (1, 2)).2 ∈
    (add_node 2 NodeDataDzn (add_node 1 NodeDataLxy (empty (ep := ep)))).V
  := by
    unfold add_node; simp
    unfold FiniteDirectedGraph.add_node; simp
    right; left; rfl
  unfold graphExampleM
  unfold graphExample
  unfold add_node_safe at *
  unfold add_edge_safe' at *
  unfold add_node at *
  unfold add_edge at *
  simp [h1]; rw [except_ok_fold]
  simp [h2]; rw [except_ok_fold]
  simp [h3]
  simp [h4]
  simp [h5]
  rfl

end test
