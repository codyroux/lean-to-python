import Lean.Meta
import Lean.Elab
import Lean.Expr
import Qq

structure Signature (S : Type) where
  arity : S → Nat
  argTy (s : S) : Fin (arity s) → Type
  outTy (s : S) : Type

inductive FreeM {S : Type} (σ : Signature S) : Type → Type 1 where
| fPure : α → FreeM σ α
| fBind : FreeM σ α → (α → FreeM σ β) → FreeM σ β
| fOp (s : S) : (args : ∀ i : Fin (σ.arity s), σ.argTy _ i) →
                FreeM σ (σ.outTy s)

instance : Monad (FreeM σ) where
  pure := FreeM.fPure
  bind := FreeM.fBind

structure Env {S : Type} (σ : Signature S) (m : Type → Type) where
  evalS (s : S) : (∀ i : Fin (σ.arity s), σ.argTy _ i) → m (σ.outTy s)


open FreeM

/-- You can eval a `FreeM` if you have a rich enough monad. -/
def evalFreeM [Monad m] (env : Env σ m) (x : FreeM σ α) : m α :=
match x with
| fPure a => return a
| fBind x f => do
  let a ← evalFreeM env x
  evalFreeM env (f a)
| fOp s f => env.evalS s (fun i => f i)


def iNil {α : Type u} (n : Fin 0) : α := by cases n; omega

def iCons {α : Type u} {n : Nat} (a : α) (v : Fin n → α) : Fin (n+1) → α := Fin.cases a (fun j => v j)

def listToVec (l : List α) : Fin (l.length) → α :=
match l with
| [] => iNil
| a::as => iCons a (listToVec as)



/-- Syntax for vectors -/
syntax (name := «term⟦_,⟧») "⟦" withoutPosition(term,*,?) "⟧" : term

open Lean in
macro_rules
  | `(⟦ $elems,* ⟧) => `(listToVec [$elems,*])

#check ⟦1, 2, 3⟧

section Test

inductive Commands where
| read
| write

def RWSig : Signature Commands where
  arity
    | .read => 0
    | .write => 1
  argTy c _ :=
  match c with
  | .write => Nat
  outTy c :=
  match c with
  | .read => Nat
  | .write => Unit

#print ULift

--- whyyyy
def read : FreeM RWSig Nat := FreeM.fOp Commands.read (fun i => ⟦⟧ i)

def write : Nat → FreeM RWSig Unit := fun n => FreeM.fOp Commands.write ⟦n⟧

#check ⟦⟧
#check do
  let x ← pure 4
  let y : Nat ← read
  let _ ← write 3
  return x + y

end Test

open Lean
open Std.Format

#check OfNat.ofNat

#check Expr.isAppOfArity
#check Expr.getArg!
#check Expr.getArg!'

#check Expr.isApp
#check Expr.isConst
#check Expr.constName!
#check Meta.inferType

abbrev PyVal := Format

-- IDK what I'm doing with this
class PythonRepr (α : Type) where
  toPython : α → PyVal

private def x : Nat := 4
private def f : Nat → Nat := fun n => n+1

#eval do
  -- let t ← `(if true then 3 else 4)
  let t ← `(x * x)
  let e ← Elab.Term.elabTerm t none
  let e ← instantiateMVars e
  logInfo m!"{t} -> {e}"
  logInfo s!"{e}"
  logInfo m!"{e.isApp}"
  logInfo m!"{e.getAppFn}"
  let n := ``HAdd.hAdd
  logInfo m!"{e.getAppFn.constName! == n}"


def numToPython (e : Lean.Expr) : MetaM PyVal :=
  let c : Option _ := e.app3? ``OfNat.ofNat
  if let .some (_, n, _) := c
  then return s!"{n}"
  else failure

def constToPython (e : Lean.Expr) : MetaM PyVal :=
  if let .some (c, _) := e.const?
  then return s!"{c.getString!}"
  else failure

def countImplicits (e : Lean.Expr) : Nat :=
match e with
| .forallE _ _ e' info =>
  if info == BinderInfo.implicit
  then countImplicits e' + 1
  else countImplicits e'
| _ => 0

mutual

partial def addToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``HAdd.hAdd then
    do
      let arg₁ ← exprToPython <| e.getArg! 4
      let arg₂ ← exprToPython <| e.getArg! 5
      return s!"({arg₁} + {arg₂})"
  else
  failure

partial def mulToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``HMul.hMul then
    do
      let arg₁ ← exprToPython <| e.getArg! 4
      let arg₂ ← exprToPython <| e.getArg! 5
      return s!"({arg₁} * {arg₂})"
  else
  failure


partial def eqToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``Eq then
    do
      let arg₁ ← exprToPython <| e.getArg! 1
      let arg₂ ← exprToPython <| e.getArg! 5
      return s!"({arg₁} == {arg₂})"
  else
  failure


partial def iteToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``ite then
    do
      let arg₁ ← exprToPython <| e.getArg! 1
      let arg₂ ← exprToPython <| e.getArg! 3
      let arg₃ ← exprToPython <| e.getArg! 4
      return s!"({arg₂} if {arg₁} else {arg₃})"
  else
  failure

partial def funToPython (e : Lean.Expr) : MetaM PyVal := do
  let ty ← Meta.inferType e
  let numImplicits := countImplicits ty
  let args := e.getAppArgs.drop numImplicits
  let argsPy ← args.mapM exprToPython
  let argsPy := paren <| joinSep argsPy.toList ","
  let f ← exprToPython e.getAppFn
  return s!"{f}{argsPy}"

partial def exprToPython (e : Lean.Expr) : MetaM PyVal := do
  if e.isConst then
    constToPython e
  else
    if e.isApp then
      let n := e.getAppFn.constName!
      if n == ``OfNat.ofNat then numToPython e
      else if n == ``HAdd.hAdd then addToPython e
      else if n == ``HMul.hMul then mulToPython e
      else if n == ``Eq then eqToPython e
      else if n == ``ite then iteToPython e
      else funToPython e
    else failure

end

#eval do
  let t ← `(if 3 = 3 then 0 else f (0 * x))
  let e ← Elab.Term.elabTerm t none
  let e ← instantiateMVars e
  logInfo s!"{e}"
  let py ← exprToPython e
  logInfo py

def toPython (e : Expr) : PyVal := ""

--- This is all garbage?


/- -- TODO: how do I model effectful operations?
-- Do I need to be step-indexed somehow?
-- How do I model fixpoints?



/--
A free monad with extra operations

This is all pretty standard stuff.
-/
inductive FreeM : Type → Type 1 where
-- The monadic ops
| fPure : α → FreeM α
| fBind : FreeM α → (α → FreeM β) → FreeM β
-- Declaring fresh types and operations
| typeDecl : (Type → FreeM α) → FreeM α
-- Operations can be effectful
| opDecl : FreeM α
-- and assumptions
| assume {P : Prop} : Decidable P → (P → FreeM α) → FreeM α
-- What does assert look like?
-- | assert {P : Prop} : FreeM ???

-- Question: if I assume that this is going to be a state monad
-- is there an easy way to add effectful ops?

-- This is the environment that supplies the pure operations
inductive EvalEnv (m : Type → Type) : Type → Type _ where
| runPure : EvalEnv m α
-- This seems nuts
| runBind : (∀ α, EvalEnv m α) → (∀ α, α → EvalEnv m β) → EvalEnv m β
| runTypeDecl : Type → EvalEnv m α → EvalEnv m α
| runOpDecl {α : Type} : m α → EvalEnv m α
| runAssume {P : Type} : EvalEnv m α → EvalEnv m α

open FreeM EvalEnv

def evalFreeM [Monad m] (x : FreeM α) (env : EvalEnv m α) : OptionT m α :=
  match x, env with
  | fPure a, runPure => return a
  | @fBind α β m f, runBind em ef => do
    let x ← evalFreeM m (em _)
    let v ← evalFreeM (f x) (ef _ x)
    return v
  | typeDecl x, runTypeDecl ty e => evalFreeM (x ty) e
  | opDecl, runOpDecl op => op
  | assume h x, runAssume e =>
    (match h with
    | .isTrue p => evalFreeM (x p) e
    | _ => failure)
  | _, _ => failure
 -/

/-
-- I don't get how any of this works
section TestQ
open Qq

def foo (x : Q(Nat)) : MetaM String :=
  match x with
  | ~q(0) => return "foo"
  | ~q($x) => return s!"{x}"
  | _ => return "bar"

abbrev y : Nat := 0

#eval do
  let t ← `(y)
  let e ← Elab.Term.elabTerm t none
  let bar ← foo e
  logInfo m!"{bar}"


end TestQ
 -/
