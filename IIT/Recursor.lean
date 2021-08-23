/- Builds the recursor -/

import IIT.Relation

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

partial def recDecls (i : Nat := 0)
  (recs : List Declaration := []): TermElabM $ List Declaration :=
if i >= its.length then return recs else do
  let recTypes ← recTypes its ls motives methods
  let recType := recTypes.get! i
  if i>1 then throwError "rec type is {indentExpr recType}"
  let decl := Declaration.defnDecl { name     := (its.get! i).name ++ recursorSuffix, 
                                     levelParams  := [], --TODO
                                     value    := mkConst "foo", -- TODO
                                     type     := recType, -- TODO
                                     hints    := arbitrary,
                                     safety   := DefinitionSafety.safe }
  recDecls (i + 1) (recs.append [decl])

end IIT