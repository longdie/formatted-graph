import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

section Graph

variable {ν : Type*} {ε : Type*} [DecidableEq ν] [DecidableEq ε]

/--
`Graph ep`: finite directed graph
* `ν`: the type of all possible nodes
* `ε`: the type of all possible edges
* `ep`: the endpoints of each edge in `ε`
* `V`: the finite set of nodes
* `E`: the finite set of edges
* `h`: the endpoints of each edge in `E` are in `V`
-/
structure Graph (ep : ε → ν × ν) where
  V : Finset ν
  E : Finset ε
  h : ∀ {e : ε}, e ∈ E → (ep e).1 ∈ V ∧ (ep e).2 ∈ V

namespace Graph

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
`add_node_unsafe v G`: to add a node `v` to a graph `G`.
* If `v` is already in `G`, then `G` remains unchanged.
-/
def add_node_unsafe {ep : ε → ν × ν} (v : ν)
    (G : Graph ep) : Graph ep where
  V := insert v G.V
  E := G.E
  h := by
    intro e he
    have hends := G.h he
    exact ⟨
      Finset.mem_insert_of_mem hends.1,
      Finset.mem_insert_of_mem hends.2
    ⟩

/--
`add_edge_unsafe e G h`: to add an edge `e` to a graph `G` under the assumption
  `h` that the endpoints of `e` are in `G`.
* If `e` is already in `G`, then `G` remains unchanged.
-/
def add_edge_unsafe {ep : ε → ν × ν} (e : ε)
    (G : Graph ep)
    (h : (ep e).1 ∈ G.V ∧ (ep e).2 ∈ G.V)
    : Graph ep where
  V := G.V
  E := insert e G.E
  h := by
    intro e' he'
    simp only [Finset.mem_insert] at he'
    rcases he' with rfl | he'
    · assumption
    · exact G.h he'

/--
`NodeError`: all possible errors about nodes triggerred by graph a modification
-/
inductive NodeError where
  | add_node_existing
  | remove_node_missing

/--
`EdgeError`: all possible errors about edges triggerred by graph a modification
-/
inductive EdgeError where
  | add_edge_existing
  | add_edge_start_point_missing
  | add_edge_end_point_missing
  | remove_edge_missing

/-- `Error`: all possible errors triggerred by graph a modification -/
inductive Error (ep : ε → ν × ν) where
  | node_error (v : ν) (err : NodeError)
  | edge_error (e : ε) (err : EdgeError)

/--
`Info`: the execution info, i.e., whether an error and which error is triggerred
  by graph a modification
-/
inductive Info (ep : ε → ν × ν) where
  | error (err : Error ep)
  | ok

/-- `GraphM`: the monad for graph modifications -/
def GraphM (ep : ε → ν × ν) :=
  StateM (Graph ep) (Info ep)

/--
`add_node v G`: to add a node `v` to a graph `G`.
* If `v` is already in `G`, then `G` remains unchanged and the error
  `.node_error v .add_node_existing` is raised.
-/
def add_node {ep : ε → ν × ν} (v : ν)
  : GraphM ep :=
  fun G => ⟨
    if v ∈ G.V
      then .error $ .node_error v .add_node_existing
      else .ok,
    add_node_unsafe v G
  ⟩

/--
`add_edge e G`: to add a node `e` to a graph `G`.
* If at least one of endpoints of `e` is not in `G`, then
  either the error `.node_error e .add_edge_start_point_missing`
  or another `.node_error e .add_edge_end_point_missing` is raised.
* If `e` is already in `G`, then `G` remains unchanged and the error
  `.node_error e .add_edge_existing` is raised.
-/
def add_edge {ep : ε → ν × ν} (e : ε)
  : GraphM ep :=
  fun G =>
    if h1 : (ep e).1 ∈ G.V then
      if h2 : (ep e).2 ∈ G.V then
        if e ∈ G.E then ⟨.error $ .edge_error e .add_edge_existing, G⟩
        else ⟨.ok, (add_edge_unsafe e G ⟨h1, h2⟩)⟩
      else ⟨.error $ .edge_error e .add_edge_end_point_missing, G⟩
    else ⟨.error $ .edge_error e .add_edge_start_point_missing, G⟩

end Graph

end Graph

section GraphWithData

variable {ν : Type*} {ε : Type*} [DecidableEq ν] [DecidableEq ε]

/-- `Data`: a typeclass for registration of data types. -/
class Data (α : Type*) where
  data_type : Type*

namespace Data

/-- `NodeData`: a typeclass for registration of data types for nodes -/
class NodeData (ν : Type*) extends Data ν

/-- `EdgeData`: a typeclass for registration of data types for edges -/
class EdgeData (ν : Type*) extends Data ν

/-- `δ α`: a shorthand for extracting the stored data type -/
abbrev δ (α : Type*) [data_type : Data α] := data_type.data_type

end Data

/--
`GraphWithData ep`: finited directed graph with data attached to nodes and edges
* extended from `Graph ep`
* `data_v` : the data attached to each node
* `data_e` : the data attached to each edge
-/
structure GraphWithData
  [node_data_type : Data.NodeData ν]
  [edge_data_type : Data.EdgeData ε]
  (ep : ε → ν × ν)
    extends Graph ep where
  data_v : V → Data.δ ν
  data_e : E → Data.δ ε

namespace GraphWithData

open Data

variable [node_data_type : NodeData ν] [edge_data_type : EdgeData ε]

/-- `empty ep`: the empty graph, i.e., the one with no nodes and edges. -/
def empty {ep : ε → ν × ν} : GraphWithData ep where
  toGraph := Graph.empty
  data_v := fun ⟨_, h⟩ => (Finset.notMem_empty _ h).elim
  data_e := fun ⟨_, h⟩ => (Finset.notMem_empty _ h).elim

/--
`discrete ep dv V`: the discrete graph with a given node set `V` and no edges.
Each node is stored with data `dv`.
-/
def discrete (ep : ε → ν × ν) (V : Finset ν) (dv : δ ν)
    : GraphWithData ep where
  toGraph := Graph.discrete ep V
  data_v := fun _ => dv
  data_e := fun ⟨_, h⟩ => (Finset.notMem_empty _ h).elim

/--
`add_node_unsafe v dv G`: to add a node `v` to a graph `G`.
* If `v` is already in `G`, then `G` remains unchanged.
-/
def add_node_unsafe {ep : ε → ν × ν} (v : ν) (dv : δ ν)
    (G : GraphWithData ep) : GraphWithData ep where
  toGraph := Graph.add_node_unsafe v G.toGraph
  data_v := fun ⟨v', _⟩ =>
    if hin : v' ∈ G.V
    then G.data_v ⟨v', hin⟩
    else dv
  data_e := G.data_e

/--
`add_edge e de G h`: to add an edge `e` with data `de` to a graph `G` under the
  assumption `h` that the endpoints of `e` are in `G`.
* If `e` is already in `G`, then `G` remains unchanged.
-/
def add_edge_unsafe {ep : ε → ν × ν} (e : ε) (de : δ ε)
    (G : GraphWithData ep)
    (h : (ep e).1 ∈ G.V ∧ (ep e).2 ∈ G.V)
    : GraphWithData ep where
  toGraph := Graph.add_edge_unsafe e G.toGraph h
  data_v := G.data_v
  data_e := fun ⟨e', _⟩ =>
    if hin : e' ∈ G.E
    then G.data_e ⟨e', hin⟩
    else de

/--
`NodeError`: all possible errors about nodes triggerred by a modification on
  a graph with data
-/
inductive NodeError where
  | graph_node_error (err : Graph.NodeError)
  | edit_node_missing

/--
`EdgeError`: all possible errors about edges triggerred by a modification on
  a graph with data
-/
inductive EdgeError where
  | graph_edge_error (err : Graph.EdgeError)
  | edit_edge_missing

/--
`Error`: all possible errors triggerred by a modification on a graph with data
-/
inductive Error (ep : ε → ν × ν) where
  | node_error (v : ν) (err : NodeError)
  | edge_error (e : ε) (err : EdgeError)

/--
`Info`: the execution info, i.e., whether an error and which error is triggerred
  by a modification on a graph with data
-/
inductive Info (ep : ε → ν × ν) where
  | error (err : Error ep)
  | ok

/-- Embed a node error from `Graph` into the corresponding data-graph error. -/
instance : Coe Graph.NodeError NodeError where
  coe := .graph_node_error

/-- Embed an edge error from `Graph` into the corresponding data-graph error. -/
instance : Coe Graph.EdgeError EdgeError where
  coe := .graph_edge_error

/-- Embed a `Graph.Error` into the corresponding `GraphWithData.Error`. -/
instance {ep : ε → ν × ν} : Coe (Graph.Error ep) (Error ep) where
  coe
  | .node_error v err => .node_error v err
  | .edge_error e err => .edge_error e err

/-- Embed execution information from `Graph` into `GraphWithData.Info`. -/
instance {ep : ε → ν × ν} : Coe (Graph.Info ep) (Info ep) where
  coe
  | .error err => .error err
  | .ok => .ok

/--
`ErrorKind`: declaration of different kinds of errors for graphs with data
-/
inductive ErrorKind (ep : ε → ν × ν) where
  | all
    | node
      | add_node_existing
      | remove_node_missing
      | edit_node_missing
    | edge
      | add_edge_existing
      | add_edge_points_missing
        | add_edge_start_point_missing
        | add_edge_end_point_missing
      | remove_edge_missing
      | edit_edge_missing

/--
`ErrorKindMatch`: definition of different kinds of errors for graphs with data
-/
def ErrorKindMatch {ep : ε → ν × ν} :
  ErrorKind ep → Error ep → Bool
  | .all, _
    | .node, .node_error _ _
      | .add_node_existing, .node_error _ $ .graph_node_error .add_node_existing
      | .remove_node_missing,
          .node_error _ $ .graph_node_error .remove_node_missing
      | .edit_node_missing, .node_error _ $ .edit_node_missing
    | .edge, .edge_error _ _
      | .add_edge_existing, .edge_error _ $ .graph_edge_error .add_edge_existing
      | .add_edge_points_missing,
          .edge_error _ $ .graph_edge_error .add_edge_start_point_missing
      | .add_edge_points_missing,
          .edge_error _ $ .graph_edge_error .add_edge_end_point_missing
        | .add_edge_start_point_missing,
            .edge_error _ $ .graph_edge_error .add_edge_start_point_missing
        | .add_edge_end_point_missing,
            .edge_error _ $ .graph_edge_error .add_edge_end_point_missing
      | .remove_edge_missing,
          .edge_error _ $ .graph_edge_error .remove_edge_missing
      | .edit_edge_missing, .edge_error _ $ .edit_edge_missing
    => true
  | _, _ => false

/--
`BuildM`: the monad for raising errors for modifications on graphs with data
-/
abbrev BuildM (ep : ε → ν × ν) :=
  Except (Error ep)

/--
`InfoResult`: a type that binds the execution info to the result graph
-/
abbrev InfoResult (ep : ε → ν × ν) :=
  Info ep × GraphWithData ep

/--
`Result`:
* the result graph, if the execution is ok, or
* the error,        if this error is thrown out
-/
abbrev Result (ep : ε → ν × ν) :=
  BuildM ep (GraphWithData ep)

/--
`Builder`: the execution monad that raising errors while preserving the result
  graph (with data)
-/
abbrev Builder (ep : ε → ν × ν) :=
  StateT (GraphWithData ep) (BuildM ep)

/--
`add_node_info v dv G`: attempt to add node `v` with data `dv` to `G`.
The returned `InfoResult` contains both the execution information and the
resulting graph.
-/
def add_node_info {ep : ε → ν × ν} (v : ν) (dv : δ ν)
    (G : GraphWithData ep) : InfoResult ep :=
  ⟨
    (Graph.add_node v G.toGraph).1,
    G.add_node_unsafe v dv
  ⟩

/--
`add_edge_info e de G`: attempt to add edge `e` with data `de` to `G`.
The graph is updated only when the edge is new and both endpoints exist.
-/
def add_edge_info {ep : ε → ν × ν} (e : ε) (de : δ ε)
    (G : GraphWithData ep) : InfoResult ep :=
  if h : e ∉ G.E ∧ (ep e).1 ∈ G.V ∧ (ep e).2 ∈ G.V
  then ⟨.ok, G.add_edge_unsafe e de h.2⟩
  else ⟨(Graph.add_edge e G.toGraph).1, G⟩

/--
`InfoResult.allow allow result`: convert `result` to a `Result`.
An error is ignored exactly when it matches at least one kind in `allow`.
-/
def InfoResult.allow {ep : ε → ν × ν} (allow : List (ErrorKind ep)) :
  InfoResult ep → Result ep
  | ⟨i, G⟩ => match i with
    | .ok => .ok G
    | .error err =>
      if allow.foldl (fun b err_kind => b || ErrorKindMatch err_kind err) false
      then .ok G
      else .error err

/--
`add_node v dv G allow`: safely add node `v` with data `dv` to `G`.
Errors matching a kind in `allow` are ignored.
-/
def add_node {ep : ε → ν × ν} (v : ν) (dv : δ ν)
    (G : GraphWithData ep) (allow : List (ErrorKind ep) := [])
    : Result ep :=
  (add_node_info v dv G).allow allow

/--
`add_edge e de G allow`: safely add edge `e` with data `de` to `G`.
Errors matching a kind in `allow` are ignored.
-/
def add_edge {ep : ε → ν × ν} (e : ε) (de : δ ε)
    (G : GraphWithData ep) (allow : List (ErrorKind ep) := [])
    : Result ep :=
  (add_edge_info e de G).allow allow

/--
`Builder.modifyE f`: lift an error-aware graph transformation `f` into the
`Builder` monad.
-/
def Builder.modifyE
    {ep : ε → ν × ν}
    (f : GraphWithData ep → Result ep) :
    Builder ep PUnit :=
  fun G =>
    match f G with
    | .ok G'     => .ok (.unit, G')
    | .error err => .error err

/--
`Builder.addNode v dv allow`: add a node within a `Builder` computation.
Errors matching a kind in `allow` are ignored.
-/
def Builder.addNode
    {ep : ε → ν × ν}
    (v : ν) (dv : δ ν)
    (allow : List (ErrorKind ep) := [])
  : Builder ep PUnit :=
  Builder.modifyE (fun G => add_node v dv G allow)

/--
`Builder.addEdge e de allow`: add an edge within a `Builder` computation.
Errors matching a kind in `allow` are ignored.
-/
def Builder.addEdge
    {ep : ε → ν × ν}
    (e : ε) (de : δ ε)
    (allow : List (ErrorKind ep) := [])
  : Builder ep PUnit :=
  Builder.modifyE (fun G => add_edge e de G allow)

/--
`Builder.exec p G`: execute builder computation `p` from initial graph `G`.
-/
def Builder.exec
    {ep : ε → ν × ν}
    (p : Builder ep PUnit)
    (G : GraphWithData ep) :
    Result ep :=
  match p.run G with
  | .ok ⟨_, G'⟩     => .ok G'
  | .error error   => .error error

/--
`Builder.build p`: execute builder computation `p` from the empty graph.
-/
def Builder.build
    {ep : ε → ν × ν}
    (p : Builder ep PUnit) :
    Result ep :=
  p.exec GraphWithData.empty

/-- Executing one lifted transformation is equivalent to applying it. -/
@[simp] theorem Builder.exec_modifyE
    {ep : ε → ν × ν}
    (f : GraphWithData ep → Result ep)
    (G : GraphWithData ep) :
    Builder.exec (Builder.modifyE f) G = f G := by
  unfold Builder.exec
  unfold StateT.run
  unfold modifyE
  generalize f G = r
  cases r <;> rfl

/--
Split a builder computation after its first lifted graph transformation.
-/
theorem modify_fold
    {ep : ε → ν × ν}
    (first_step : GraphWithData ep → Result ep)
    (others : Builder ep PUnit)
    (G : GraphWithData ep)
  : Builder.exec (do
      Builder.modifyE first_step
      others
    ) G =
    match Builder.exec (do Builder.modifyE first_step) G with
    | .ok G' => Builder.exec (do others) G'
    | .error err => .error err := by
  unfold Builder.exec; simp
  rcases StateT.run (Builder.modifyE first_step) G with
    error | ⟨_, G⟩ <;> rfl

/--
Execute the remaining builder steps only when `first_step` succeeds.
-/
theorem Builder.exec_modifyE_then
    {ep : ε → ν × ν}
    (first_step : GraphWithData ep → Result ep)
    (others : Builder ep PUnit)
    (G : GraphWithData ep)
  : Builder.exec (do
      Builder.modifyE first_step
      others
    ) G =
    match first_step G with
    | .ok G' => Builder.exec others G'
    | .error error => .error error := by
  rw [modify_fold]
  simp

/-- Simplify concrete graph and builder computations by unfolding operations. -/
macro "graph_simp" : tactic =>
  `(tactic|
    (simp (config := { decide := true }) [
      GraphWithData.Builder.addNode,
      GraphWithData.Builder.addEdge,
      GraphWithData.Builder.build,
      GraphWithData.Builder.exec,
      GraphWithData.Builder.modifyE,
      StateT.run,
      GraphWithData.InfoResult.allow,
      GraphWithData.empty,
      GraphWithData.discrete,
      GraphWithData.add_node,
      GraphWithData.add_edge,
      GraphWithData.add_node_info,
      GraphWithData.add_edge_info,
      GraphWithData.add_node_unsafe,
      GraphWithData.add_edge_unsafe,
      Graph.empty,
      Graph.discrete,
      Graph.add_node_unsafe,
      Graph.add_edge_unsafe,
      Graph.add_node,
      Graph.add_edge,
    ] <;> try rfl))

end GraphWithData

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
  ).add_node_unsafe
    1 NodeDataLxy
  ).add_node_unsafe
    2 NodeDataDzn
  ).add_edge_unsafe
    (1,2)
    (EdgeData.mk' "" NodeDataLxy NodeDataDzn)
    (by graph_simp)

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

def Builder.addEdge'
    (e : Nat × Nat) (contents : String)
  : Builder ep PUnit :=
  Builder.modifyE (fun G => add_edge' e contents G)

def graphExampleM : Result ep :=
  Builder.build do
    Builder.addNode 1 NodeDataLxy
    Builder.addNode 2 NodeDataDzn
    Builder.addEdge' (1, 2) ""

example : graphExampleM = .ok graphExample := by
  unfold graphExampleM graphExample
  unfold Builder.addEdge'
  unfold Builder.addNode
  unfold Builder.build
  simp [Builder.exec_modifyE_then]
  graph_simp

end test
