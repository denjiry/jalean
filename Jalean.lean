import Lean
open Lean Elab Term

def «こんにちは» := "hello"
#eval «こんにちは»++«こんにちは»

def say (a : String) := a.capitalize
#eval say «こんにちは»

inductive Entity where
  | entity : Entity

def «太郎が» := 1
def «次郎を» := 2
-- i==2 -> S\NP\NP:       \y.\x.\c.(e:event)X(op(e,x,y)X(ce)
inductive «ほめるsr» (e1 : Entity)(e2 : Entity) : Prop
  | mk : Entity -> Entity -> «ほめるsr» e1 e2
#check «ほめるsr».mk Entity.entity Entity.entity

def «ほめる» := 3

#check «太郎が» «次郎を» «ほめる»

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

-- #check (⟨⟨1 sorry⟩⟩ : Fin 12)
-- def oo: List Char := ⟨⟨ hello ⟩⟩

declare_syntax_cat ja_expr
syntax "こんにちは" : ja_expr
syntax "言う" : ja_expr
-- def こんにちは := "hello"
-- def 言う (a : String) := a.capitalize
-- @[termElab ja_expr]
-- def 

elab "ja(" je:ja_expr+ ")" : term => do
  let _a: Syntax := (je[0]!).raw
  logInfo s!"kk{je[1]!}"
  pure $ mkStrLit s!"o{je}"

#eval ja(こんにちは)
#eval ja(こんにちは言う)
