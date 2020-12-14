/- Utility functions, copied mainly from Lean.Elab.Inductive -/
import Lean.Parser
import Lean.Elab

namespace IIT

open OrElse
open Lean.Elab.Command
open Lean.Elab
open Lean
open List
open Meta

-- Elab inductive Syntax into a view, copied from Lean.Elab.Declaration
def inductiveSyntaxToView (decl : Syntax) : CommandElabM InductiveView := do
  let binders          := decl[2][0]
  let type             := decl[2][1][1]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId { }
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    let ctorModifiers := { } --← elabModifiers ctor[1]
    let ctorName := ctor.getIdAt 2
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[2] $ applyVisibility ctorModifiers.visibility ctorName
    let inferMod := !ctor[3].isNone
    let (binders, type?) := expandOptDeclSig ctor[4]
    match type? with
    | some type =>
       pure { ref := ctor,
              modifiers := ctorModifiers,
              declName := ctorName,
              inferMod := inferMod,
              binders := binders,
              type? := type? : CtorView }
    | none      => throwError "Give all constructor types for an IIT declartion!"
  pure { ref           := decl,
         modifiers     := { },
         shortDeclName := name,
         declName      := declName,
         levelNames    := levelNames,
         binders       := binders,
         type?         := some type,
         ctors         := ctors : InductiveView }

private def getResultingType (e : Expr) : TermElabM Expr :=
  forallTelescopeReducing e fun _ r => pure r

private def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "unexpected empty inductive declaration"
  | indType :: _ => do
    let r ← getResultingType indType.type
    match r with
    | Expr.sort u _ => pure u
    | _             => throwError "unexpected inductive type resulting type"

private def collectUsed (indTypes : List InductiveType) : StateRefT CollectFVars.State TermElabM Unit := do
  indTypes.forM fun indType => do
    Term.collectUsedFVars indType.type
    indType.ctors.forM fun ctor =>
      Term.collectUsedFVars ctor.type

private def removeUnused (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed indTypes).run {}
  Term.removeUnused vars used

private def withUsed {α} (vars : Array Expr) (indTypes : List InductiveType) (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused vars indTypes
  withLCtx lctx localInsts $ k vars

private def collectLevelParamsInInductive (indTypes : List InductiveType) : Array Name :=
  let usedParams := indTypes.foldl (init := {}) fun (usedParams : CollectLevelParams.State) indType =>
    let usedParams := collectLevelParams usedParams indType.type;
    indType.ctors.foldl (init := usedParams) fun (usedParams : CollectLevelParams.State) ctor =>
      collectLevelParams usedParams ctor.type
  usedParams.params

private def mkIndFVar2Const (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name) : ExprMap Expr :=
  let levelParams := levelNames.map mkLevelParam;
  views.size.fold (init := {}) fun i (m : ExprMap Expr) =>
    let view    := views[i]
    let indFVar := indFVars[i]
    m.insert indFVar (mkConst view.declName levelParams)

private def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars levelNames
  indTypes.mapM fun indType => do
    let ctors ← indType.ctors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type numParams fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else match indFVar2Const.find? e with
            | none   => none
            | some c => mkAppN c (params.extract 0 numVars)
        mkForallFVars params type
      pure { ctor with type := type }
    pure { indType with ctors := ctors }

private def mkCtor2InferMod (views : Array InductiveView) : Ctor2InferMod :=
  views.foldl (init := {}) fun m view =>
    view.ctors.foldl (init := m) fun m ctorView =>
      m.insert ctorView.declName ctorView.inferMod

private def applyInferMod (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : List InductiveType :=
  let ctor2InferMod := mkCtor2InferMod views
  indTypes.map fun indType =>
    let ctors := indType.ctors.map fun ctor =>
      let inferMod := ctor2InferMod.find! ctor.name -- true if `{}` was used
      let ctorType := ctor.type.inferImplicit numParams !inferMod
      { ctor with type := ctorType }
    { indType with ctors := ctors }

end IIT
