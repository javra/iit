/- Eliminator relation -/

import Lean.Elab
import Init.Data.Array.Basic
import IIT.InductiveUtils
import IIT.Util
import IIT.Erasure
import IIT.Wellformedness

open Lean
open Elab
open Command
open Meta
open Expr
open Array

namespace IIT

variables (its : List InductiveType) (ls : List Level)

def motiveSuffix : Name := "m"
def methodSuffix : Name := "m"

def motiveAux (fVars : Array Expr) (t tm : Expr) :=
match t with
| app f e d   => let fm := appFn! tm
                 let em := appArg! tm
                 mkApp (mkApp (motiveAux fVars f fm) e) em
| const n l _ =>
  match headerAppIdx? its t with
  | some j    => fVars[j]
  | none      => t
| _           => t

partial def motive (l : Level) (fVars : Array Expr) (e : Expr) (ref : Expr) : Expr :=
match e with
| forallE n t b d =>
   match headerAppIdx? its t with
  | some j => let b  := liftBVarsOne b
              let t' := liftBVarsOne t
              mkForall n BinderInfo.implicit t $
              mkForall (n ++ "m") e.binderInfo (mkApp (motiveAux its fVars t' t) $ mkBVar 0) $
              motive l fVars b (mkApp (liftBVarsTwo ref) (mkBVar 1))
  | none   => mkForall n e.binderInfo t $
              motive l fVars b (mkApp (liftBVarsOne ref) (mkBVar 0))
| sort l' d       => mkForall "x" BinderInfo.default ref (mkSort l)
| _ => e

section
variables (methods : Array (Array Expr)) (motives : Array Expr)

/- We invoke a dirty, dirty hack here:
   We hand on one version `em` of the expression where loose BVars refer to the model and one `e`
   where they refer to the syntax. -/
def methodTmP (e em : Expr) : Expr :=
match e with
| app f e d => let fm := appFn! em
               let em := appArg! em
               mkApp (mkApp (methodTmP f fm) e) em
| _           =>
  match ctorAppIdx? its em with
  | some (i, j) => methods[i][j]
  | none        => em

def methodTmS (e : Expr) (em : Expr) : TermElabM Expr := do
match e with
| app f e d =>
  let fm := appFn! em
  let em := appArg! em            
  let f_type := bindingDomain! $ ← inferType f
  match headerAppIdx? its f_type with --TODO is this too shaky?
  | some _ => let methodFn ← methodTmS f fm
              mkApp (mkApp methodFn e) (methodTmP its methods e em)
  | none   => mkApp (← methodTmS f fm) e
| const n l d =>
  match headerAppIdx? its e with
  | some j => motives[j]
  | none   => e
| _ => e

partial def method (name : Name) (e : Expr) (em : Expr := e) (ref := mkConst name) : TermElabM Expr := do
match e with
| forallE n t b d =>
  match headerAppIdx? its t with
  | some j => let ref := mkApp (liftBVarsTwo ref) $ mkBVar 1
              let t' := liftBVarsOne t
              let b' := liftBVarsOne b
              mkForall n BinderInfo.implicit t $
              mkForall (n ++ "m") e.binderInfo 
                (mkApp (← methodTmS its methods motives t' t) $ mkBVar 0) $
                (← method name b' b ref)
  | none   => let ref := mkApp (liftBVarsOne ref) $ mkBVar 0
              mkForall n e.binderInfo t $
              ← method name b (bindingBody! em) ref
| _ => mkApp (← methodTmS its methods motives e em) ref

end

--TODO generalize the construction of this sort of function
partial def withMotives {α} (x : Array Expr → TermElabM α)
  (i : Nat := 0) (fVars : Array Expr := #[]) : TermElabM α :=
if i >= its.length then x fVars else
let name := (its.get! i).name ++ motiveSuffix
let type := motive its (ls.get! i) fVars (its.get! i).type (mkConst (its.get! i).name)
withLocalDeclD name type fun fVar => do
  withMotives x (i + 1) (fVars.push fVar)

partial def withMethodsAux {α} (motives : Array Expr) 
  (methods : Array (Array Expr)) (i : Nat) (x : Array Expr → TermElabM α)
  (j : Nat := 0) (fVars : Array Expr := #[]) : TermElabM α :=
if j >= (its.get! i).ctors.length then x fVars else do
let ctor := (its.get! i).ctors.get! j
let type ← method its methods motives ctor.name ctor.type
let name := ctor.name ++ methodSuffix
withLocalDeclD name type fun fVar => do
  withMethodsAux motives methods i x (j + 1) (fVars.push fVar)

partial def withMethods {α} (motives : Array Expr) (x : Array (Array Expr) → TermElabM α)
  (i : Nat := 0) (methods : Array (Array Expr) := #[]) : TermElabM α :=
if i >= its.length then x methods else
withMethodsAux its motives methods i fun fVars =>
  withMethods motives x (i + 1) (methods.push fVars)

def withRecArgs {α} (x : Array Expr → Array (Array Expr) → TermElabM α) : TermElabM α :=
withMotives its ls fun motives =>
  withMethods its motives fun methods =>
    x motives methods

section

variables (motives : Array Expr) (methods : Array (Array Expr))

def relationSuffix : Name := "r"

def elimRelationHeaderTmS (e em : Expr) : Expr :=
match e with
| app f e d   => let fm := appFn! em
                 let em := appArg! em
                 mkApp (mkApp (elimRelationHeaderTmS f fm) e) em
| const n l d =>
  match headerAppIdx? its e with
  | some j => motives[j]
  | none   => e
| _ => e

partial def elimRelationHeader (e sref dref : Expr) : Expr :=
match e with
| sort _ _ => let dref := mkApp (liftBVarsOne dref) (mkBVar 0)
              mkForall "s" BinderInfo.default sref $ 
              mkForall "d" BinderInfo.default dref $
              mkSort levelZero
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some j => let b'    := liftBVarsOne b
              let td   := elimRelationHeaderTmS its motives (liftBVarsOne t) t
              let td   := mkApp td (mkBVar 0)
              let sref := mkApp (liftBVarsTwo sref) (mkBVar 1)
              let dref := mkApp (mkApp (liftBVarsTwo dref) (mkBVar 1)) (mkBVar 0)
              mkForall n BinderInfo.implicit t $
              mkForall (n ++ motiveSuffix) e.binderInfo td $
              elimRelationHeader b' sref dref
  | none   => let sref := mkApp (liftBVarsOne sref) (mkBVar 0)
              let dref := mkApp (liftBVarsOne dref) (mkBVar 0)
              mkForall n e.binderInfo t $
              elimRelationHeader b sref dref
| _ => e

partial def elimRelation (its : List InductiveType) (i : Nat := 0) (rits := []) : MetaM $ List InductiveType :=
if i >= its.length then rits else do
let it := its.get! i
let type := elimRelationHeader its motives (its.get! i).type (mkConst (its.get! i).name) motives[i]
let motivesAndMethods := motives ++ methods.concat
let type ← mkForallFVars motivesAndMethods type
let ctors := []
let rit := { name  := it.name ++ relationSuffix,
             type  := type,
             ctors := ctors : InductiveType }
elimRelation its (i + 1) (rits.append [rit])

end

end IIT
