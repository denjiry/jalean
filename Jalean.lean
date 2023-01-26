import Lean
open Lean Elab Term

def «こんにちは» := "hello"
#eval «こんにちは»++«こんにちは»

def say (a : String) := a.capitalize
#eval say «こんにちは»

-- WRAP Sbar[decl] (e0:evt)× (誉める/ほめる/ガヲ(e0,太郎/たろう;太郎/たろう,次郎/じろう)) [0.85]
--   > S[v:1<1>][term|attr<4>][] λx0.(e0:evt)× (u0:誉める/ほめる/ガヲ(e0,太郎/たろう;太郎/たろう,次郎/じろう))× x0(e0) [0.95]
--     > T1/(T1\NP[ga]) λx0.x0(太郎/たろう;太郎/たろう) [0.99]
--       LEX 太郎 T1/(T1\NP[nc]) λx0.x0(太郎/たろう;太郎/たろう) (PN) [0.99]
--       LEX が T1/(T1\NP[ga])\NP[nc] λx0.λx1.x1(x0) (524) [1.00]
--     > S[v:1<1>][term|attr<4>][]\NP[ga] λx0.λx1.(e0:evt)× (u0:誉める/ほめる/ガヲ(e0,x0,次郎/じろう))× x1(e0) [0.96]
--       > T1/(T1\NP[o]) λx0.x0(次郎/じろう) [0.99]
--         LEX 次郎 T1/(T1\NP[nc]) λx0.x0(次郎/じろう) (PN) [0.99]
--         LEX を T1/(T1\NP[o])\NP[nc] λx0.λx1.x1(x0) (524) [1.00]
--       <B2 S[v:1<1>][term|attr][]\NP[ga]\NP[o] λx0.λx1.λx2.(e0:evt)× (u0:誉める/ほめる/ガヲ(e0,x1,x0))× x2(e0) [0.97]
--         LEX ほめ S[v:1][stem|neg|cont|+][]\NP[ga]\NP[o] λx0.λx1.λx2.(e0:evt)× (u0:誉める/ほめる/ガヲ(e0,x1,x0))× x2(e0) (JCon) [0.97]
--         LEX る S[v:5:r|v:1|v:5:ARU|+<1>][term|attr][]\S[v:5:r|v:1|v:5:ARU|+<1>][stem][] λx0.x0 (125) [1.00]
-- Sig. [太郎/たろう;太郎/たろう:entity, 次郎/じろう:entity, 誉める/ほめる/ガヲ:(x0:entity)→ (x1:entity)→ (e0:evt)→ type]

inductive Entity where
  | entity (n : Name) : Entity
open Entity
#print entity
def taro := entity `a
def jiro := entity `b
#check False
example : taro ≠ jiro := by 
  admit

def «太郎が» := 1
def «次郎を» := 2
#check Eq
#check λy x => And.intro x y
-- i==2 -> S\NP\NP:       \y.\x.\c.(e:event)X(op(e,x,y)X(ce)
structure «ほめるsr» (ga wo : Entity) where
  ga : Entity
  wo : Entity

#check Fin 1
#check «ほめるsr» (entity `a) (entity `b)
#check «ほめるsr».mk (entity `a) (entity `b)

theorem aa : ∀ (p1 p2 : Prop) {_ : p1} {_ : p2}, And p1 p2 := by
  intros p1 p2 hp1 hp2
  exact And.intro hp1 hp2

#print aa

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
