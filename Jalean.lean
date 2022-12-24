import Lean
open Lean Elab Term

def hello := "world"

def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) =>
    pure val.ctors
  | _ => pure []

syntax (name := myanon) "⟨⟨" term+ "⟩⟩" : term

@[termElab myanon]
def myanonImpl : TermElab := fun stx typ? => do
  -- tryPostponeIfNoneOrMVar typ? 
  let some typ := typ? | throwError "expected type must be known"
  let args := TSyntaxArray.mk stx[1].getSepArgs
  logInfo s!"{args}"
  if typ.isMVar then
    throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type doesn't have exactly one constructor"
  logInfo s!"stx:{stx}"
  let stx ← `($(mkIdent ctor) $args*) -- syntax quotations
  logInfo s!"stx2:{stx}"
  elabTerm stx typ -- call term elaboration recursively


#check (⟨⟨1 sorry⟩⟩ : Fin 12)
def oo: List Char := ⟨⟨ hello ⟩⟩
