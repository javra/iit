/- Builds the recursor -/

import IIT.Relation
import IIT.Totality

open Lean
open Elab
open Command
open Meta
open Expr
open Array
open Tactic

namespace IIT

def recursorSuffix : Name := "rec"

variable (its : List InductiveType) (ls : List Level)
  (motives : Array Expr) (methods : Array (Array Expr))

def addRecIfHeader (n : Name) (l : List Level) : Expr :=
if contains (collectHeaderNames its) n then mkConst (n ++ recursorSuffix) l
else mkConst n l

partial def recTypeTmS (e : Expr) : MetaM Expr := do
match e with
| app f e _ => mkApp (←recTypeTmS f) e
| const n l _ => let t := addRecIfHeader its n l
                 mkAppN t (motives ++ methods.concat)
| _ => e --TODO

partial def recType (l : Level) (e sref dref : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some _ => let sref := mkApp (liftBVarsOne sref) $ mkBVar 0
              let trec ← recTypeTmS its motives methods (liftBVarsOne t)
              let trec := mkApp trec $ mkBVar 0
              let dref := mkApp2 (liftBVarsOne dref) (mkBVar 0) trec
              mkForall n e.binderInfo t $
              ← recType l b sref dref
  | none   => let sref := mkApp (liftBVarsOne sref) $ mkBVar 0
              let dref := mkApp (liftBVarsOne dref) $ mkBVar 0
              mkForall n e.binderInfo t $
              ← recType l b sref dref
| sort l _ => let dref := liftBVarsOne dref
              mkForall "s" BinderInfo.default sref $
              mkApp dref $ mkBVar 0
| _ => e

partial def recTypes (i : Nat := 0) (rTypes : List Expr := []) : MetaM $ List Expr :=
if i >= its.length then rTypes else do
let name := (its.get! i).name
let type := (its.get! i).type
let recType ← recType its motives methods (ls.get! i) type (mkConst name) motives[i]
let recType ← mkForallFVars (motives ++ methods.concat) recType
recTypes (i + 1) (rTypes.append [recType])

def addTotIfHeader (n : Name) (l : List Level) : Expr :=
if contains (collectHeaderNames its) n then mkConst (n ++ totalitySuffix) l
else mkConst n l

private partial def recVal_motiveRelRef (e : Expr) : MetaM Expr := do
match e with
| const n l _ => let t := addTotIfHeader its n l
                 mkAppN t (motives ++ methods.concat)
| _ => e

-- Invariant: `recVal l e sref dref` should be of type `recType l e sref dref`.
partial def recVal (l : Level) (e sref tref : Expr) : MetaM Expr := do
match e with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let sref := mkApp (liftBVarsOne sref) (mkBVar 0)
              let mrref ← recVal_motiveRelRef its motives methods t
              let tref := mkAppN (liftBVarsOne tref) #[mkBVar 0, mkFst mrref, mkSnd mrref]
              mkLambda n e.binderInfo t $
              ← recVal l b sref tref
  | none   => let sref := mkApp (liftBVarsOne sref) (mkBVar 0)
              let tref := mkApp (liftBVarsOne tref) (mkBVar 0)
              mkLambda n e.binderInfo t $
              ← recVal l b sref tref
| sort l _ => let tref := mkApp (liftBVarsOne tref) (mkBVar 0)
              mkLambda "s" BinderInfo.default sref $
              mkFst tref
| _ => e

partial def recVals (i : Nat := 0) (rVals : List Expr := []) : MetaM $ List Expr :=
if i >= its.length then rVals else do
let name := (its.get! i).name
let type := (its.get! i).type
let tref := mkAppN (mkConst (name ++ "tot")) (motives ++ methods.concat)
let recVal ← recVal its motives methods (ls.get! i) type (mkConst name) tref
let recVal ← mkLambdaFVars (motives ++ methods.concat) recVal
recVals (i + 1) (rVals.append [recVal])

partial def recDecls (i : Nat := 0)
  (recs : List Declaration := []): TermElabM $ List Declaration :=
if i >= its.length then return recs else do
  let recTypes ← recTypes its ls motives methods
  let recVals ← recVals its ls motives methods
  let recType := recTypes.get! i
  let recVal := recVals.get! i
  if i>0 then throwError "rec val is {indentExpr recVal}"
  let decl := Declaration.defnDecl { name     := (its.get! i).name ++ recursorSuffix, 
                                     levelParams  := [], --TODO
                                     value    := recVal,
                                     type     := recType,
                                     hints    := arbitrary,
                                     safety   := DefinitionSafety.safe }
  recDecls (i + 1) (recs.append [decl])

end IIT