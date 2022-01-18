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
  let classes ← getOptDerivingClasses decl[5]
  pure { ref           := decl,
         modifiers     := { },
         shortDeclName := name,
         declName      := declName,
         levelNames    := levelNames,
         binders       := binders,
         type?         := some type,
         ctors         := ctors,
         derivingClasses := classes : InductiveView }

def getResultingType (e : Expr) : TermElabM Expr :=
  forallTelescopeReducing e fun _ r => pure r

def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "unexpected empty inductive declaration"
  | indType :: _ => do
    let r ← getResultingType indType.type
    match r with
    | Expr.sort u _ => pure u
    | _             => throwError "unexpected inductive type resulting type"

def collectUsed (indTypes : List InductiveType) : StateRefT CollectFVars.State MetaM Unit := do
  indTypes.forM fun indType => do
    Meta.collectUsedFVars indType.type
    indType.ctors.forM fun ctor =>
      Meta.collectUsedFVars ctor.type

def removeUnused (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed indTypes).run {}
  Meta.removeUnused vars used

def withUsed {α} (vars : Array Expr) (indTypes : List InductiveType) (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused vars indTypes
  withLCtx lctx localInsts $ k vars

def collectLevelParamsInInductive (indTypes : List InductiveType) : Array Name :=
  let usedParams := indTypes.foldl (init := {}) fun (usedParams : CollectLevelParams.State) indType =>
    let usedParams := collectLevelParams usedParams indType.type;
    indType.ctors.foldl (init := usedParams) fun (usedParams : CollectLevelParams.State) ctor =>
      collectLevelParams usedParams ctor.type
  usedParams.params

--modified to also map free variables of constructors
def mkIndFVar2Const (views : Array InductiveView) (indFVars : Array Expr) (ctorFVars : Array (Array Expr)) 
  (levelNames : List Name) : ExprMap Expr :=
  let levelParams := levelNames.map mkLevelParam;
  views.size.fold (init := {}) fun i (m : ExprMap Expr) =>
    let view    := views[i]
    let indFVar := indFVars[i]
    let m' := m.insert indFVar (mkConst view.declName levelParams)
    views[i].ctors.size.fold (init := m') fun j (m : ExprMap Expr) =>
      m.insert ctorFVars[i][j] (mkConst view.ctors[j].declName levelParams)

--modified to also replace free variables of constructors
def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (ctorFVars : Array (Array Expr))
    (levelNames : List Name) (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars ctorFVars levelNames
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

--replace free variables in headers
def replaceHeaderIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (ctorFVars : Array (Array Expr)) 
  (levelNames : List Name) (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars ctorFVars levelNames
  indTypes.mapM fun indType => do
    let type ← forallBoundedTelescope indType.type numParams fun params type => do
      let type := type.replace fun e =>
        if !e.isFVar then none
        else match indFVar2Const.find? e with
             | none   => none
             | some c => mkAppN c (params.extract 0 numVars)
      mkForallFVars params type
    pure { indType with type := type }

def mkCtor2InferMod (views : Array InductiveView) : Ctor2InferMod :=
  views.foldl (init := {}) fun m view =>
    view.ctors.foldl (init := m) fun m ctorView =>
      m.insert ctorView.declName ctorView.inferMod

def applyInferMod (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : List InductiveType :=
  let ctor2InferMod := mkCtor2InferMod views
  indTypes.map fun indType =>
    let ctors := indType.ctors.map fun ctor =>
      let inferMod := ctor2InferMod.find! ctor.name -- true if `{}` was used
      let ctorType := ctor.type.inferImplicit numParams !inferMod
      { ctor with type := ctorType }
    { indType with ctors := ctors }

def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    pure $ xs.size > numParams

def elabCtors (indFVar : Expr) (params : Array Expr) (r : ElabHeaderResult) : TermElabM (List Constructor) :=
  withRef r.view.ref do
  let indFamily ← isInductiveFamily params.size indFVar
  r.view.ctors.toList.mapM fun ctorView => Term.elabBinders ctorView.binders.getArgs fun ctorParams =>
    withRef ctorView.ref do
    let type ← match ctorView.type? with
      | none          =>
        if indFamily then
          throwError "constructor resulting type must be specified in inductive family declaration"
        pure (mkAppN indFVar params)
      | some ctorType =>
        let type ← Term.elabTerm ctorType none
        let resultingType ← getResultingType type
        unless resultingType.getAppFn == indFVar do
          throwError "unexpected constructor resulting type{indentExpr resultingType}"
        unless (← isType resultingType) do
          throwError "unexpected constructor resulting type, type expected{indentExpr resultingType}"
        let args := resultingType.getAppArgs
        for i in [:params.size] do
          let param := params[i]
          let arg   := args[i]
          unless (← isDefEq param arg) do
            throwError "inductive datatype parameter mismatch{indentExpr arg}\nexpected{indentExpr param}"
        pure type
    let type ← mkForallFVars ctorParams type
    let type ← mkForallFVars params type
    pure { name := ctorView.declName, type := type }

def checkLevelNames (views : Array InductiveView) : TermElabM Unit := do
  if views.size > 1 then
    let levelNames := views[0].levelNames
    for view in views do
      unless view.levelNames == levelNames do
        throwErrorAt view.ref "invalid inductive type, universe parameters mismatch in mutually inductive datatypes"

def updateParams (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type ← mkForallFVars vars indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← mkForallFVars vars ctor.type
      pure { ctor with type := ctorType }
    pure { indType with type := type, ctors := ctors }

def levelMVarToParamAux (indTypes : List InductiveType) : StateRefT Nat TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type  ← Term.levelMVarToParam' indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← Term.levelMVarToParam' ctor.type
      pure { ctor with type := ctorType }
    pure { indType with ctors := ctors, type := type }

def levelMVarToParam (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  (levelMVarToParamAux indTypes).run' 1

/-
  Auxiliary function for `updateResultingUniverse`
  `accLevelAtCtor u r rOffset us` add `u` components to `us` if they are not already there and it is different from the resulting universe level `r+rOffset`.
  If `u` is a `max`, then its components are recursively processed.
  If `u` is a `succ` and `rOffset > 0`, we process the `u`s child using `rOffset-1`.

  This method is used to infer the resulting universe level of an inductive datatype. -/
def accLevelAtCtor : Level → Level → Nat → Array Level → TermElabM (Array Level)
  | Level.max u v _,  r, rOffset,   us => do let us ← accLevelAtCtor u r rOffset us; accLevelAtCtor v r rOffset us
  | Level.imax u v _, r, rOffset,   us => do let us ← accLevelAtCtor u r rOffset us; accLevelAtCtor v r rOffset us
  | Level.zero _,     _, _,         us => pure us
  | Level.succ u _,   r, rOffset+1, us => accLevelAtCtor u r rOffset us
  | u,                r, rOffset,   us =>
    if rOffset == 0 && u == r then pure us
    else if r.occurs u  then throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly"
    else if rOffset > 0 then throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly"
    else if us.contains u then pure us
    else pure (us.push u)

/- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniversesFromCtorTypeAux (r : Level) (rOffset : Nat) : Nat → Expr → Array Level → TermElabM (Array Level)
  | 0,   Expr.forallE n d b c, us => do
    let u ← getLevel d
    let u ← instantiateLevelMVars u
    let us ← accLevelAtCtor u r rOffset us
    withLocalDecl n c.binderInfo d fun x =>
      let e := b.instantiate1 x
      collectUniversesFromCtorTypeAux r rOffset 0 e us
  | i+1, Expr.forallE n d b c, us => do
    withLocalDecl n c.binderInfo d fun x =>
      let e := b.instantiate1 x
      collectUniversesFromCtorTypeAux r rOffset i e us
  | _, _, us => pure us

/- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniversesFromCtorType
    (r : Level) (rOffset : Nat) (ctorType : Expr) (numParams : Nat) (us : Array Level) : TermElabM (Array Level) :=
  collectUniversesFromCtorTypeAux r rOffset numParams ctorType us

/- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniverses (r : Level) (rOffset : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (Array Level) :=
  indTypes.foldlM (init := #[]) fun us indType =>
    indType.ctors.foldlM (init := us) fun us ctor =>
      collectUniversesFromCtorType r rOffset ctor.type numParams us

def mkResultUniverse (us : Array Level) (rOffset : Nat) : Level :=
  if us.isEmpty && rOffset == 0 then
    levelOne
  else
    let r := Level.mkNaryMax us.toList
    if rOffset == 0 && !r.isZero && !r.isNeverZero then
      (mkLevelMax r levelOne).normalize
    else
      r.normalize

def updateResultingUniverse (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) := do
  let r ← getResultingUniverse indTypes
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  unless r.isParam do
    throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly"
  let us ← collectUniverses r rOffset numParams indTypes
  trace[Elab.inductive] "updateResultingUniverse us: {us}, r: {r}, rOffset: {rOffset}"
  let rNew := mkResultUniverse us rOffset
  let updateLevel (e : Expr) : Expr := e.replaceLevel fun u => if u == tmpIndParam then some rNew else none
  return indTypes.map fun indType =>
    let type := updateLevel indType.type;
    let ctors := indType.ctors.map fun ctor => { ctor with type := updateLevel ctor.type };
    { indType with type := type, ctors := ctors }

def checkResultingUniverses (indTypes : List InductiveType) : TermElabM Unit := do
  checkResultingUniverse (← getResultingUniverse indTypes)

-- Adapted to only take names instead of views
def mkAuxConstructions (viewNames : List Name) : TermElabM Unit := do
  let env ← getEnv
  let hasEq   := env.contains `Eq
  let hasHEq  := env.contains `HEq
  let hasUnit := env.contains `PUnit
  let hasProd := env.contains `Prod
  for n in viewNames do
    mkRecOn n
    if hasUnit then mkCasesOn n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
    if hasUnit && hasProd then mkIBelow n
  for n in viewNames do
    if hasUnit && hasProd then mkBRecOn n
    if hasUnit && hasProd then mkBInductionOn n

instance : Inhabited InductiveType :=
⟨{ name := default, type := default, ctors := default }⟩

instance : Inhabited Constructor :=
⟨{ name := default, type := default }⟩

end IIT
