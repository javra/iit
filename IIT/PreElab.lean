-- Elaborate sorts and constructors without kernel declaration
import Lean.Util.ReplaceExpr
import Lean.ResolveName
import Lean.Util.Sorry
import Lean.Structure
import Lean.Meta
import Lean.Hygiene
import Lean.Util.RecDepth
import Lean.Elab
import Lean.LocalContext
import IIT.InductiveUtils

open Lean
open Elab
open Command
open Term
open Level
open Meta
open LocalContext

namespace IIT

partial def elabSingleHeader (view : InductiveView) : TermElabM ElabHeaderResult := do
  -- TODO check headers
  -- TODO check unsafe
  withAutoBoundImplicitLocal
      <| elabBinders view.binders.getArgs (catchAutoBoundImplicit := true) fun params => do
      match view.type? with
      | none         => -- this whole clause is probably not needed
        let u ← Meta.mkFreshLevelMVar
        let type := mkSort u
        let params ← addAutoBoundImplicits params
        pure { lctx := (← getLCtx),
               localInsts := (← getLocalInstances),
               params := params, type := type, view := view }
      | some typeStx =>
        elabTypeWithAutoBoundImplicit typeStx fun type => do
          unless (← isTypeFormerType type) do
            throwErrorAt typeStx "invalid inductive type, resultant type is not a sort"
          let params ← Term.addAutoBoundImplicits params
          pure  { lctx := (← getLCtx),
                  localInsts := (← getLocalInstances),
                  params := params, type := type, view := view }

structure PreElabHeaderResult extends ElabHeaderResult where
  fVar   : Expr

partial def preElabHeadersAux (views : Array InductiveView) (i : Nat) : TermElabM (Array PreElabHeaderResult) := do
  if (i >= views.size) then return #[]
  else
    let hr ← elabSingleHeader views[i]
    let type ← mkForallFVars hr.params hr.type
    withLCtx hr.lctx hr.localInsts do
      withLocalDeclD hr.view.declName type (λ indFVar => do
        let hr := { toElabHeaderResult := { hr with type := type }, fVar := indFVar : PreElabHeaderResult }
        let hrs ← preElabHeadersAux views (i + 1)
        pure $ hrs.push hr)

structure PreElabCtorResult extends Constructor where
  fVar   : Expr

partial def preElabConstrAuxAux (hr : PreElabHeaderResult) (view : InductiveView) (j : Nat) : TermElabM (Array PreElabCtorResult) := do
  if (j >= view.ctors.size) then return #[]
  else withRef view.ref do
    let ctorView := view.ctors[j]
    Term.elabBinders ctorView.binders.getArgs fun ctorParams => do
    let type ← match ctorView.type? with
      | none => throwError "constructor type must be specified"
      | some ctorType => 
        let type ← Term.elabTerm ctorType none
        --throwError ctorType
        let resultingType ← getResultingType type
        unless resultingType.getAppFn == hr.fVar do throwError! "unexpected constructor resulting type{indentExpr resultingType}"
        unless (← isType resultingType) do throwError! "unexpected constructor resulting type, type expected"
        let args := resultingType.getAppArgs
        for i in [:hr.params.size] do
          let param := hr.params[i]
          let arg   := args[i]
          unless (← isDefEq param arg) do throwError! "inductive datatype parameter mismatch"
        pure type
    let type ← mkForallFVars ctorParams type
    let type ← mkForallFVars hr.params type
    withLocalDeclD ctorView.declName type (λ ctorFVar => do
      let cr := { name := ctorView.declName, type := type, fVar := ctorFVar : PreElabCtorResult }
      let crs ← preElabConstrAuxAux hr view (j + 1)
      return crs.push cr)

partial def preElabConstrAux (hrs : Array PreElabHeaderResult) (views : Array InductiveView) (i : Nat) : TermElabM (Array (Array PreElabCtorResult)) := do
  if (i >= views.size) then return #[]
  withRef views[i].ref do
    match hrs.get? i with
    | none => throwError "empty header!"
    | some hr => 
      let prs ← preElabConstrAuxAux hr views[i] 0
      let prss ← preElabConstrAux hrs views (i + 1) --TODO not sure if I need to add context for this step
      return prss.push prs

-- Adapted from Lean.Elab.Inductive
def preElabViews (views : Array InductiveView) : TermElabM (Array PreElabHeaderResult × Array (Array PreElabCtorResult)) := do
  let view0 := views[0]
  let scopeLevelNames ← Term.getLevelNames
  checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref $ Term.withLevelNames allUserLevelNames do
    let hrs ← preElabHeadersAux views 0
    -- do I need to somehow re-add header fVars??
    let cts ← preElabConstrAux hrs views 0
    Term.synthesizeSyntheticMVarsNoPostponing
    --TODO other cosmetics
    pure (hrs, cts)

def prToIT (hr : PreElabHeaderResult) (crs : Array PreElabCtorResult) : InductiveType :=
{ name := hr.view.declName, type := hr.type, ctors := (crs.map (λ cr => { name := cr.name, type := cr.type })).toList }

def preElabViewsIT (views : Array InductiveView) : TermElabM (Array InductiveType) := do
  let (hrs, ctrss) ← preElabViews views
  let prs := Array.zip hrs ctrss
  return prs.map (λ (hr, ctrs) => prToIT hr ctrs)

end IIT
