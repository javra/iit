/- Builds the recursor -/

import IIT.Relation
import IIT.Totality

open Lean
open Elab
open Command
open Meta
open Lean.Expr
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
| app f e _ => return mkApp (←recTypeTmS f) e
| const n l _ => let t := addRecIfHeader its n l
                 return mkAppN t (motives ++ methods.concat)
| _ => return e --TODO

partial def recType (l : Level) (e sref dref : Expr) : MetaM Expr := do
match e with
| forallE n t b _ => 
  match headerAppIdx? its t with
  | some _ => let sref := mkApp (liftBVarsOne sref) $ mkBVar 0
              let trec ← recTypeTmS its motives methods (liftBVarsOne t)
              let trec := mkApp trec $ mkBVar 0
              let dref := mkApp2 (liftBVarsOne dref) (mkBVar 0) trec
              return mkForall n e.binderInfo t $
              ← recType l b sref dref
  | none   => let sref := mkApp (liftBVarsOne sref) $ mkBVar 0
              let dref := mkApp (liftBVarsOne dref) $ mkBVar 0
              return mkForall n e.binderInfo t $
              ← recType l b sref dref
| sort l _ => let dref := liftBVarsOne dref
              return mkForall "s" BinderInfo.default sref $
              mkApp dref $ mkBVar 0
| _ => return e

partial def recTypes (i : Nat := 0) (rTypes : List Expr := []) : MetaM $ List Expr :=
if i >= its.length then return rTypes else do
let name := (its.get! i).name
let type := (its.get! i).type
let recType ← recType its motives methods (ls.get! i) type (mkConst name) motives[i]
let recType ← mkForallFVars (motives ++ methods.concat) recType
recTypes (i + 1) (rTypes.append [recType])

def addTotIfHeader (n : Name) (l : List Level) : Expr :=
if contains (collectHeaderNames its) n then mkConst (n ++ totalitySuffix) l
else mkConst n l

private partial def recVal_motiveRelRef (e etot : Expr) : MetaM Expr := do
match e with
| app f e _ => let e' := etot.appArg! --need the _type_ of `e` instead
               return mkAppN (←recVal_motiveRelRef f etot.appFn!) #[e, mkFst e', mkSnd e']
| const n l _ => let t := addTotIfHeader its n l
                 return mkAppN t (motives ++ methods.concat)
| _ => return e

-- Invariant: `recVal l e sref dref` should be of type `recType l e sref dref`.
partial def recVal (l : Level) (e etot sref tref : Expr) : MetaM Expr := do
match e with
| forallE n t b _ =>
  match headerAppIdx? its t with
  | some _ => let sref := mkApp (liftBVarsOne sref) (mkBVar 0)
              let mrref ← recVal_motiveRelRef its motives methods t etot.bindingDomain!
              let mrref := mkApp (liftBVarsOne mrref) (mkBVar 0)
              let tref := mkAppN (liftBVarsOne tref) #[mkBVar 0, mkFst mrref, mkSnd mrref]
              -- need a version of `b` where bvars are replaced with calls to `*.tot ...`
              let btot := (etot.bindingBody!).instantiate1 mrref
              return mkLambda n e.binderInfo t $
              ← recVal l b btot sref tref
  | none   => let sref := mkApp (liftBVarsOne sref) (mkBVar 0)
              let tref := mkApp (liftBVarsOne tref) (mkBVar 0)
              let btot := etot.bindingBody!
              return mkLambda n e.binderInfo t $
              ← recVal l b btot sref tref
| sort l _ => let tref := mkApp (liftBVarsOne tref) (mkBVar 0)
              return mkLambda "s" BinderInfo.default sref $
              mkFst tref
| _ => return e

partial def recVals (i : Nat := 0) (rVals : List Expr := []) : MetaM $ List Expr :=
if i >= its.length then return rVals else do
let name := (its.get! i).name
let type := (its.get! i).type
let tref := mkAppN (mkConst (name ++ "tot")) (motives ++ methods.concat)
let recVal ← recVal its motives methods (ls.get! i) type type (mkConst name) tref
let recVal ← mkLambdaFVars (motives ++ methods.concat) recVal
recVals (i + 1) (rVals.append [recVal])

partial def recDecls (i : Nat := 0)
  (recs : List Declaration := []): TermElabM $ List Declaration :=
if i >= its.length then return recs else do
  let recTypes ← recTypes its ls motives methods
  let recVals ← recVals its ls motives methods
  let recType := recTypes.get! i
  let recVal := recVals.get! i
  --if i>1 then throwError "rec val is {indentExpr recVal}"
  let decl := Declaration.defnDecl { name     := (its.get! i).name ++ recursorSuffix, 
                                     levelParams  := [], --TODO
                                     value    := recVal,
                                     type     := recType,
                                     hints    := default,
                                     safety   := DefinitionSafety.safe }
  recDecls (i + 1) (recs.append [decl])

end IIT