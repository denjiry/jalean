import Lean
open Lean Elab Term
open Command
syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax

@[commandElab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"

#mycommand1 -- Hello World

@[commandElab Lean.Parser.Command.«def»]
def defOverroad : CommandElab := fun stx => do
  logInfo "def over"

def a: String := "a"
elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, looks like its bad :("
    | _ => logInfo s!"Your syntax may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def aaa := "a"
