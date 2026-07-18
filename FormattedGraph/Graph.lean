import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-!
# FormattedGraph.Graph

Generic graph data structures and graph operations.
-/


namespace FiniteDirectedGraph

variable {τ : Type*} {ε : Type*} [DecidableEq τ] [DecidableEq ε]

/--
finite directed graph
* `τ`: the type of all possible vertices
* `ε`: the type of all possible edges
* `ep`: the endpoints of each edge in `ε`
* `V`: the finite set of vertices
* `E`: the finite set of edges
* `h`: the hypothesis that the endpoints of each edge in `E` is in `V`
-/
structure Graph (ep : ε → τ × τ) where
  V : Finset τ
  E : Finset ε
  h : ∀ {e : ε}, e ∈ E → (ep e).1 ∈ V ∧ (ep e).2 ∈ V

/--
`discrete ep V`: the discrete graph with a given vertex set `V` and no edges.
-/
def discrete (ep : ε → τ × τ) (V : Finset τ) : Graph ep where
  V := V
  E := ∅
  h := by
    intro _ he
    simp at he

/--
`empty ep`: the empty graph, i.e., the one with no vertices and edges.
-/
def empty (ep : ε → τ × τ) : Graph ep :=
  discrete ep ∅

/--
`add_vertex v G`: to add a vertex `v` to a graph `G`.
If `v` is already in `G`, then nothing happens.
-/
def add_vertex {ep : ε → τ × τ} (v : τ) (G : Graph ep) : Graph ep where
  V := {v} ∪ G.V
  E := G.E
  h := by
    intro _ h
    simp [G.h, h]

/--
`add_edge e G`: to add an edge `e` to a graph `G`.
If `e` is already in `G`, then nothing happens.
If some of the endpoints of `e` is not in `G`, then add it.
-/
def add_edge {ep : ε → τ × τ} (e : ε) (G : Graph ep) : Graph ep where
  V := {(ep e).1} ∪ {(ep e).2} ∪ G.V
  E := {e} ∪ G.E
  h := by
    intro _ h; simp at h
    rcases h with h | h <;> simp [G.h, h]

/--
`remove_vertex v G`: to remove a vertex `v` from a graph `G`.
If `v` is not in `G`, then nothing happens.
If `v` is in `G`, then all the edges that are adjacent to `v` are removed.
-/
def remove_vertex {ep : ε → τ × τ} (v : τ) (G : Graph ep) : Graph ep where
  V := G.V \ {v}
  E := G.E \ { e ∈ G.E | (ep e).1 = v ∨ (ep e).2 = v}
  h := by
    intro _ h; simp at h
    simp [G.h, h]

/--
`remove_edge e G`: to remove an edge `e` from a graph `G`.
If `e` is not in `G`, then nothing happens.
-/
def remove_edge {ep : ε → τ × τ} (e : ε) (G : Graph ep) : Graph ep where
  V := G.V
  E := G.E \ {e}
  h := by
    intro _ h; simp at h
    simp [G.h, h]

structure push_forward_struct (ep : ε → τ × τ) where
  rv : τ → τ
  re : ε → ε
  h1 : ∀ {e : ε}, (ep (re e)).1 = rv (ep e).1
  h2 : ∀ {e : ε}, (ep (re e)).2 = rv (ep e).2

/--
`replace_vertex v v' re ... G`: to replace a vertex `v` by `v'` from a graph `G`.
If `v` is not in `G`, then nothing happens.
If `v` is in `G`, then all the edges that are adjacent to `v` are removed.
-/
def push_forward
  {ep : ε → τ × τ}
  (f : push_forward_struct ep)
  (G : Graph ep) : Graph ep where
  V := G.V.image f.rv
  E := G.E.image f.re
  h := by
    intro _ h; simp at h
    rcases h with ⟨e, ⟨h, heq⟩⟩
    subst heq
    constructor <;> simp
    . exists (ep e).1
      simp [G.h, f.h1, h]
    . exists (ep e).2
      simp [G.h, f.h2, h]

end FiniteDirectedGraph
