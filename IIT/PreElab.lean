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

structure PreElabResult where
  it     : InductiveType
  fVar   : Array Expr
  params : Array Expr

partial def preElabViewsAux (views : Array InductiveView) (i : Nat) : TermElabM (Array PreElabResult) := do
  if (i >= views.size) then return #[]
  let hr ← elabSingleHeader views[i]
  let type ← mkForallFVars hr.params hr.type
  withLCtx hr.lctx hr.localInsts do
    let indFVar := mkFVar hr.view.declName --???
    let ctors := [] --elabCtors indFVar hr.params hr
    let indType := { name := hr.view.declName, type := type, ctors := ctors : InductiveType }
    let per := { it := indType, params := hr.params, fVar := #[indFVar] : PreElabResult } --- [indFvar] ???
    withLocalDeclD hr.view.declName type (λ _ => do let pers ← preElabViewsAux views (i + 1)
                                                    pure $ #[per] ++ pers)

-- Adapted from Lean.Elab.Inductive
def preElabViews (vars : Array Expr) (views : Array InductiveView) : TermElabM (Array PreElabResult) := do
  let view0 := views[0]
  let scopeLevelNames ← Term.getLevelNames
  checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref $ Term.withLevelNames allUserLevelNames do
    let pers ← preElabViewsAux views 0
    Term.synthesizeSyntheticMVarsNoPostponing
    --TODO other cosmetics
    pure pers

end IIT
