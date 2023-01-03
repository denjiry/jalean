import Lean
open Lean Elab Term

-- def こんにちは := "world"
def say (a : String) := a.capitalize

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
syntax (name:=ja_expr) "ja(" term+ ")" : term
-- def こんにちは := "hello"
-- def 言う (a : String) := a.capitalize
-- @[termElab ja_expr]
-- def 

@[termElab ja_expr]
def hogeImpl : TermElab := fun stx typ? => do
  logInfo s!"kk{stx[2]}"
  match stx with
  | `(ja_expr | ja( $jexpr )) =>
    logInfo s!"mm{jexpr}"
    pure $ mkStrLit "a"
  | _ => throwUnsupportedSyntax

-- #check ja( こんにちは 言う )
#check ja( 1 2 )

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

syntax "[Bool|" boolean_expr "]" : term
#check [Bool| ⊥ AND ⊤] -- elaboration function hasn't been implemented but parsing passes
