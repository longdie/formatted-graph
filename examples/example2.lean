import FormattedGraph
import Mathlib.Data.String.Basic

/-!
# Lean metaprogramming monads

A graph of the principal Lean 4 metaprogramming monads. It shows both the
underlying monads and the context or state added at each layer.
-/

namespace FormattedGraph.Examples.Example2

structure NodeId where
  value : String
deriving DecidableEq, Repr

inductive EdgeId where
  | eioToCore
  | coreDataToCore
  | coreToMeta
  | metaDataToMeta
  | metaToTerm
  | termDataToTerm
  | termToTactic
  | tacticDataToTactic
  | eioToCommand
  | commandDataToCommand
  | termToCommand
deriving DecidableEq, Repr

instance : LinearOrder NodeId :=
  LinearOrder.lift' (fun node => node.value) (by
    intro a b h
    cases a
    cases b
    simp_all)

def EdgeId.rank : EdgeId → Nat
  | .eioToCore => 0
  | .coreDataToCore => 1
  | .coreToMeta => 2
  | .metaDataToMeta => 3
  | .metaToTerm => 4
  | .termDataToTerm => 5
  | .termToTactic => 6
  | .tacticDataToTactic => 7
  | .eioToCommand => 8
  | .commandDataToCommand => 9
  | .termToCommand => 10

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

def eio : NodeId := ⟨"eio-exception"⟩
def coreData : NodeId := ⟨"core-context-state"⟩
def coreM : NodeId := ⟨"core-m"⟩
def metaData : NodeId := ⟨"meta-context-state"⟩
def metaM : NodeId := ⟨"meta-m"⟩
def termData : NodeId := ⟨"term-context-state"⟩
def termElabM : NodeId := ⟨"term-elab-m"⟩
def tacticData : NodeId := ⟨"tactic-context-goals"⟩
def tacticM : NodeId := ⟨"tactic-m"⟩
def commandData : NodeId := ⟨"command-context-state"⟩
def commandElabM : NodeId := ⟨"command-elab-m"⟩

def endpoints : EdgeId → NodeId × NodeId
  | .eioToCore => (eio, coreM)
  | .coreDataToCore => (coreData, coreM)
  | .coreToMeta => (coreM, metaM)
  | .metaDataToMeta => (metaData, metaM)
  | .metaToTerm => (metaM, termElabM)
  | .termDataToTerm => (termData, termElabM)
  | .termToTactic => (termElabM, tacticM)
  | .tacticDataToTactic => (tacticData, tacticM)
  | .eioToCommand => (eio, commandElabM)
  | .commandDataToCommand => (commandData, commandElabM)
  | .termToCommand => (termElabM, commandElabM)

def monadArchitecture : GraphWithData.Result endpoints :=
  GraphWithData.Builder.build do
    GraphWithData.Builder.addNode eio
      { label := "EIO Exception"
        category := "Base monad"
        description := "Provides state-threaded effects and Lean exceptions." }
    GraphWithData.Builder.addNode coreData
      { label := "Core Context + State"
        category := "Core data"
        description := "Carries the environment, options, and core state." }
    GraphWithData.Builder.addNode coreM
      { label := "CoreM"
        category := "Core monad"
        description :=
          "ReaderT Core.Context (StateRefT Core.State (EIO Exception))." }
    GraphWithData.Builder.addNode metaData
      { label := "Meta Context + State"
        category := "Metavariable data"
        description := "Tracks local declarations and metavariable state." }
    GraphWithData.Builder.addNode metaM
      { label := "MetaM"
        category := "Metaprogramming monad"
        description :=
          "Adds Meta.Context and Meta.State on top of CoreM." }
    GraphWithData.Builder.addNode termData
      { label := "Term Context + State"
        category := "Elaboration data"
        description := "Tracks expected types and pending elaboration work." }
    GraphWithData.Builder.addNode termElabM
      { label := "TermElabM"
        category := "Term elaboration monad"
        description :=
          "Adds term elaboration context and state on top of MetaM." }
    GraphWithData.Builder.addNode tacticData
      { label := "Tactic Context + Goals"
        category := "Tactic data"
        description := "Tracks tactic configuration and the current goals." }
    GraphWithData.Builder.addNode tacticM
      { label := "TacticM"
        category := "Tactic monad"
        description := "Adds tactic context and goals on top of TermElabM." }
    GraphWithData.Builder.addNode commandData
      { label := "Command Context + State"
        category := "Command data"
        description := "Tracks command scopes, messages, and environment." }
    GraphWithData.Builder.addNode commandElabM
      { label := "CommandElabM"
        category := "Command elaboration monad"
        description :=
          "A separate EIO-based branch used to elaborate commands." }

    GraphWithData.Builder.addEdge .eioToCore
      { label := "base"
        description := "CoreM ultimately runs in EIO Exception." }
    GraphWithData.Builder.addEdge .coreDataToCore
      { label := "Reader + State"
        description := "CoreM reads Core.Context and updates Core.State." }
    GraphWithData.Builder.addEdge .coreToMeta
      { label := "base"
        description := "MetaM uses CoreM as its underlying monad." }
    GraphWithData.Builder.addEdge .metaDataToMeta
      { label := "Reader + State"
        description := "MetaM adds Meta.Context and Meta.State." }
    GraphWithData.Builder.addEdge .metaToTerm
      { label := "base"
        description := "TermElabM uses MetaM as its underlying monad." }
    GraphWithData.Builder.addEdge .termDataToTerm
      { label := "Reader + State"
        description := "TermElabM adds elaboration context and state." }
    GraphWithData.Builder.addEdge .termToTactic
      { label := "base"
        description := "TacticM uses TermElabM as its underlying monad." }
    GraphWithData.Builder.addEdge .tacticDataToTactic
      { label := "Reader + State"
        description := "TacticM adds tactic context and goal state." }
    GraphWithData.Builder.addEdge .eioToCommand
      { label := "base"
        description := "CommandElabM is another EIO Exception branch." }
    GraphWithData.Builder.addEdge .commandDataToCommand
      { label := "Reader + State"
        description := "CommandElabM adds command context and state." }
    GraphWithData.Builder.addEdge .termToCommand
      { label := "liftTermElabM"
        description :=
          "A command elaborator can execute a TermElabM computation." }

#check monadArchitecture

#show_graph monadArchitecture

end FormattedGraph.Examples.Example2
