/- Prototype for an implementation of IITs -/
import Lean.Parser
import Lean.Elab
import IIT.PreElab
import IIT.Erasure

namespace IIT

-- Parser

section Parser

open Lean.Parser
open Lean.Parser.Command
open OrElse

-- The syntax looks exactly like the one of inductive types, without the presence of modifiers
@[commandParser] def «iit» : Parser := 
parser! "iit " >> declId >> declSig >> Lean.Parser.optional (orElse ":=" "where")  >> many ctor

end Parser

-- Elaborator

-- Elab a single IIT sort

section IITElab

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

def declareInductiveTypes (views : Array InductiveView) (vars : Array Expr) (its : Array InductiveType) : TermElabM Unit := do
  let view0 := views[0]
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  let indTypes := its.toList
  let scopeLevelNames ← Term.getLevelNames
  let u ← getResultingUniverse indTypes
  let inferLevel ← shouldInferResultUniverse u
  withUsed vars indTypes fun vars => do
    let indFVars  := #[] -- TODO
    --let params    := #[] -- TODO
    let numExplicitParams := 0 --params.size
    let numVars   := vars.size
    let numParams := numVars + numExplicitParams
    --let indTypes ← updateParams vars indTypes
    --let indTypes ← levelMVarToParam indTypes
    --let indTypes ← if inferLevel then updateResultingUniverse numParams indTypes else checkResultingUniverses indTypes; pure indTypes
    let usedLevelNames := collectLevelParamsInInductive indTypes
    match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
    | Except.error msg      => throwError msg
    | Except.ok levelParams => do
      let indTypes ← replaceIndFVarsWithConsts views indFVars levelParams numVars numParams indTypes
      let indTypes := applyInferMod views numParams indTypes
      let decl := Declaration.inductDecl levelParams numParams indTypes isUnsafe
      Term.ensureNoUnassignedMVars decl
      addDecl decl
      --mkAuxConstructions views TODO
      -- We need to invoke `applyAttributes` because `class` is implemented as an attribute.
      for view in views do
            Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
  return

def elabIIT (elems : Array Syntax) : CommandElabM Unit := do
  let views ← elems.mapM inductiveSyntaxToView
  let its ← liftTermElabM none (preElabViews #[] views) -- replace #[]!
  let eits := erase its
  let view0 := views[0]
  let ref := view0.ref
  runTermElabM view0.declName fun vars =>
     withRef ref $ declareInductiveTypes views vars eits

end IITElab

-- Elaborate mutual blocks consisting of only IIT declarations

section MutualElab

open Lean.Elab.Command
open Lean

-- Throw an error when encountering a lone IIT declaration
@[commandElab «iit»] def elabLoneIIT : CommandElab :=
λ _ => throwError "Must declare IIT in a 'mutual' block."

-- Checks if all declarations in the block are IITs
private def isIITMutual (stx : Syntax) : Bool :=
  stx[1].getArgs.all fun elem =>
    let declKind := elem[0].getKind
    declKind == `«iit»

-- If all declarations in a mutual block are IITs, elab them,
-- otherwise elab as before
@[commandElab «mutual»] def elabIITMutual : CommandElab :=
fun stx =>
  if isIITMutual stx then
    elabIIT stx[1].getArgs
  else
    elabMutual stx

end MutualElab

end IIT

--set_option trace.Elab true
--set_option syntaxMaxDepth 10
--set_option pp.raw true

mutual

iit Con : Type where
| nil : Con

iit Ty : Con → Type where
| U : Ty Con.nil

end

#check Ty
