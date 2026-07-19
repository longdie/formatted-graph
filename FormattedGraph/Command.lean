import FormattedGraph.Display

/-!
# FormattedGraph.Command

InfoView integration and the `#show_graph` command.
-/

open Lean Server Elab Command
open ProofWidgets

/-- Display the final value of a graph expression in the InfoView. -/
syntax (name := showGraphCmd) "#show_graph " term : command

@[command_elab showGraphCmd]
def elabShowGraphCmd : CommandElab := fun
  | stx@`(#show_graph $graph:term) => do
    let htmlAction ← liftTermElabM <| HtmlCommand.evalCommandMHtml <|
      ← ``(HtmlEval.eval (FormattedGraph.graphHtml $graph))
    let html ← htmlAction
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html : $(← rpcEncode html) })
      stx
  | stx => throwError "unexpected syntax {stx}"
