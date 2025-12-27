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

abbrev RWSig : Signature Commands where
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

--- whyyyy
def read : FreeM RWSig Nat := FreeM.fOp Commands.read (fun i => ⟦⟧ i)

def write : Nat → FreeM RWSig Unit := fun n => FreeM.fOp Commands.write ⟦n⟧

def test := do
  let x ← pure 4
  let y : Nat ← read
  let _ ← write 3
  return x + y

def StateEnv : Env RWSig (StateM Nat) where
  evalS
    | .read => fun _ => get
    | .write => fun i => set (i (0 : Fin (RWSig.arity .write)))

#eval StateT.run (evalFreeM StateEnv test) 42

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
  else do
    logError m!"{e} is not an `OfNat`"
    failure

def constToPython (e : Lean.Expr) : MetaM PyVal :=
  if let .some (c, _) := e.const?
  then
    if c == ``Bool.true then return "True"
    else if c == ``Bool.false then return "False"
    else return s!"{c.getString!}"
  else do
    logError m!"{e} is not a const"
    failure

def fvarToPython (e : Lean.Expr) : MetaM PyVal :=
  dbg_trace s!"FVar: {e}"
  if e.isFVar
  then do
    let name := e.fvarId!.name
    return s!"{joinSep name.components "_"}"
  else do
    logError m!"{e} is not an `FVar`"
    failure

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
  else do
    logError m!"{e} is not an `HAdd`"
    failure

partial def mulToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``HMul.hMul then
    do
      let arg₁ ← exprToPython <| e.getArg! 4
      let arg₂ ← exprToPython <| e.getArg! 5
      return s!"({arg₁} * {arg₂})"
  else do
    logError m!"{e} is not an `HMul`"
    failure


partial def eqToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``Eq then
    do
      let arg₁ ← exprToPython <| e.getArg! 1
      let arg₂ ← exprToPython <| e.getArg! 5
      return s!"({arg₁} == {arg₂})"
  else do
    logError m!"{e} is not an `Eq`"
    failure


partial def iteToPython (e : Lean.Expr) : MetaM PyVal :=
  if e.getAppFn.constName! == ``ite then
    do
      let arg₁ ← exprToPython <| e.getArg! 1
      let arg₂ ← exprToPython <| e.getArg! 3
      let arg₃ ← exprToPython <| e.getArg! 4
      return s!"({arg₂} if {arg₁} else {arg₃})"
  else do
    logError m!"{e} is not an `if ... then ... else ...`"
    failure

partial def funToPython (e : Lean.Expr) : MetaM PyVal := do
  let ty ← Meta.inferType e
  let numImplicits := countImplicits ty
  let args := e.getAppArgs.drop numImplicits
  let argsPy ← args.mapM exprToPython
  let argsPy := paren <| joinSep argsPy.toList ", "
  let f ← exprToPython e.getAppFn
  return s!"{f}{argsPy}"

partial def lamToPython (e : Lean.Expr) : MetaM PyVal := do
  dbg_trace s!"Lambda: {e}"
  if e.isLambda then
    Meta.lambdaTelescope e
      (fun args body => do
        let args ← args.mapM exprToPython
        let args := joinSep args.toList ", "
        let body ← exprToPython body
        return s!"(lambda {args}: {body})")
  else do
    logError m!"{e} is not a λ"
    failure

partial def exprToPython (e : Lean.Expr) : MetaM PyVal := do
  if e.isConst then
    constToPython e
  else if e.isFVar then
    fvarToPython e
  else if e.isApp then
    let hd := e.getAppFn
    if hd.isConst then
      let n := hd.constName!
      if n == ``OfNat.ofNat then numToPython e
      else if n == ``HAdd.hAdd then addToPython e
      else if n == ``HMul.hMul then mulToPython e
      else if n == ``Eq then eqToPython e
      else if n == ``ite then iteToPython e
      else funToPython e
    else funToPython e
  else if e.isLambda then lamToPython e
  else do
    logError m!"{e} is not of a handled form."
    failure

end

def lamToPythonDef (n : Name) (e : Expr) : MetaM PyVal := do
  if not e.isLambda then
    let body ← exprToPython e
    return s!"def {n.getString!}():\n\t{body}"
  else
    Meta.lambdaTelescope e
      (fun args body => do
        let args ← args.mapM exprToPython
        let args := joinSep args.toList ", "
        let body ← exprToPython body
        return s!"def {n.getString!}({args}):\n\t{body}")

#print DefinitionVal

def defToPython (n : Name) : MetaM PyVal := do
  let info ← getConstInfo n
  match info with
  | .defnInfo info =>
    lamToPythonDef n info.value
  | _ =>
    logError m!"{n} is not a definition"
    failure

def test_1 (x y : Nat) : Nat := x + y

#eval do
  let t ← `(if true then (fun x => 3) 4 else (fun z => f (z * x)) 5)
  let e ← Elab.Term.elabTerm t none
  let e ← instantiateMVars e
  logInfo s!"{e}"
  let py ← exprToPython e
  logInfo py

#eval do
  defToPython ``test_1

#eval do
  let i ← getConstInfo ``countImplicits
  match i with
  | .defnInfo i =>
    logInfo m!"{i.value}"
    logInfo "def"
  | .recInfo _ => logInfo "rec"
  | .ctorInfo _ => logInfo "ctor"
  | .inductInfo _ => logInfo "induct"
  | .quotInfo _ => logInfo "quot"
  | .opaqueInfo _ => logInfo "opaque"
  | .thmInfo _ => logInfo "thm"
  | .axiomInfo _ => logInfo "axiom"


def toPython (e : Expr) : PyVal := ""
