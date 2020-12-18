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

partial def withPreElabHeaders {α} (views : Array InductiveView)
  (x : Array PreElabHeaderResult → TermElabM α) (hrs : Array PreElabHeaderResult := #[]) : TermElabM α := do
  let i := hrs.size
  if (i >= views.size) then x hrs
  else
    let hr ← elabSingleHeader views[i]
    let type ← mkForallFVars hr.params hr.type
    withLCtx hr.lctx hr.localInsts do -- we should only add this local context for the _first_ sort!
      withLocalDeclD hr.view.declName type $ λ indFVar => do
        let hr := { toElabHeaderResult := { hr with type := type }, fVar := indFVar : PreElabHeaderResult }
        withPreElabHeaders views x $ hrs.push hr

structure PreElabCtorResult extends Constructor where
  fVar   : Expr

partial def withPreElabCtor {α} (view : InductiveView) (hr : PreElabHeaderResult)
  (x : Array PreElabCtorResult → TermElabM α) (crs : Array PreElabCtorResult := #[]) : TermElabM α := do
  let j := crs.size
  if (j >= view.ctors.size) then x crs
  else withRef view.ctors[j].ref do
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
    withLocalDeclD ctorView.declName type $ λ ctorFVar => do
      let cr := { name := ctorView.declName, type := type, fVar := ctorFVar : PreElabCtorResult }
      withPreElabCtor view hr x $ crs.push cr

partial def withPreElabCtors {α} (views : Array InductiveView) (hrs : Array PreElabHeaderResult)
  (x : Array (Array PreElabCtorResult) → TermElabM α) (crss : Array (Array PreElabCtorResult) := #[]) : TermElabM α := do
  let i := crss.size
  if (i >= views.size) then x crss
  else withRef views[i].ref do
    match hrs.get? i with
    | none => throwError "empty header!"
    | some hr =>
      withPreElabCtor views[i] hr $ λ crs =>
        withPreElabCtors views hrs x $ crss.push crs
      
def preElabViews (views : Array InductiveView) : TermElabM (Array PreElabHeaderResult × Array (Array PreElabCtorResult)) := do
  let view0 := views[0]
  let scopeLevelNames ← Term.getLevelNames
  checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref $ Term.withLevelNames allUserLevelNames do
    withPreElabHeaders views $ λ hrs =>
      withPreElabCtors views hrs $ λ crss => do
        Term.synthesizeSyntheticMVarsNoPostponing
        -- TODO other cosmetics go here
        return (hrs, crss)

def prToIT (hr : PreElabHeaderResult) (crs : Array PreElabCtorResult) : InductiveType :=
{ name := hr.view.declName, type := hr.type, ctors := (crs.map (λ cr => { name := cr.name, type := cr.type })).toList }

def preElabViewsIT (views : Array InductiveView) : TermElabM (Array InductiveType) := do
  let (hrs, ctrss) ← preElabViews views
  let prs := Array.zip hrs ctrss
  return prs.map (λ (hr, ctrs) => prToIT hr ctrs)

end IIT
