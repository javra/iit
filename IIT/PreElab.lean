-- Elaborate sorts and constructors without kernel declaration
import Lean.Util.ReplaceExpr
import Lean.Elab
import Lean.Elab.Term
import Lean.ResolveName
import Lean.Util.Sorry
import Lean.Structure
import Lean.Meta.ExprDefEq
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Util
import Lean.Hygiene
import Lean.Util.RecDepth
import Lean.Elab.Log
import Lean.Elab.Level
import Lean.Elab.Attributes
import Lean.LocalContext


open Lean
open Elab
open Command
open Term
open Level
open Meta
open LocalContext

namespace IIT

-- Copied from Lean.Elab.Inductive
def checkLevelNames (views : Array InductiveView) : TermElabM Unit := do
  if views.size > 1 then
    let levelNames := views[0].levelNames
    for view in views do
      unless view.levelNames == levelNames do
        throwErrorAt view.ref "invalid inductive type, universe parameters mismatch in mutually inductive datatypes"

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

partial def preElabViewsAux (views : Array InductiveView) (i : Nat) : TermElabM (Array InductiveType) := do
  if (i >= views.size) then return #[]
  let hr ← elabSingleHeader views[i]
  let type ← mkForallFVars hr.params hr.type
  withLCtx hr.lctx hr.localInsts do
    let ctors := [] --← elabCtors indFVar params r
    let indType := { name := hr.view.declName, type := type, ctors := ctors : InductiveType }
    withLocalDeclD hr.view.declName type (λ _ => do let its ← preElabViewsAux views (i + 1)
                                                    pure $ #[indType] ++ its)

-- Adapted from Lean.Elab.Inductive
def preElabViews (vars : Array Expr) (views : Array InductiveView) : TermElabM (Array InductiveType) := do
  let view0 := views[0]
  let scopeLevelNames ← Term.getLevelNames
  checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref $ Term.withLevelNames allUserLevelNames do
    let indTypes ← preElabViewsAux views 0
    Term.synthesizeSyntheticMVarsNoPostponing
    --TODO other cosmetics
    pure indTypes

end IIT
