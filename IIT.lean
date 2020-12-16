/- Prototype for an implementation of IITs -/
import Lean.Parser
import Lean.Elab
import IIT.InductiveUtils
import IIT.PreElab
import IIT.Erasure

namespace IIT

-- Parser

section Parser

open Lean.Parser
open Command

-- The syntax looks exactly like the one of inductive types, without the presence of modifiers
@[commandParser] def «iit» : Parser := 
parser! "iit " >> declId >> declSig >> Lean.Parser.optional (OrElse.orElse ":=" "where")  >> many ctor

end Parser

-- Elaborator

-- Elab a single IIT sort

section IITElab

open Lean.Elab.Command
open Lean.Elab
open Lean
open List
open Meta

def declareInductiveTypes (views : Array InductiveView) (vars : Array Expr) (params : Array (Array Expr))
 (its : Array InductiveType) : TermElabM Unit := do
  let view0 := views[0]
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  let indTypes := its.toList
  let scopeLevelNames ← Term.getLevelNames
  let u ← getResultingUniverse indTypes
  let inferLevel ← shouldInferResultUniverse u
  withUsed vars indTypes fun vars => do
    let indFVars  := #[] -- TODO
    let numExplicitParams := 0 --params.size
    let numVars   := vars.size
    let numParams := numVars + numExplicitParams
    --let indTypes ← updateParams vars indTypes
    --let indTypes ← levelMVarToParam indTypes
    --let indTypes ← if inferLevel then updateResultingUniverse numParams indTypes else checkResultingUniverses indTypes; pure indTypes
    let usedLevelNames := collectLevelParamsInInductive indTypes
    match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
    | Except.error msg      => throwErrorAt view0.ref msg
    | Except.ok levelParams => do
      --let indTypes ← replaceIndFVarsWithConsts views indFVars levelParams numVars numParams indTypes TODO fix indFVars to call this
      let indTypes := applyInferMod views numParams indTypes
      let decl := Declaration.inductDecl levelParams numParams indTypes isUnsafe
      Term.ensureNoUnassignedMVars decl
      addDecl decl
      throwErrorAt view0.ref $ "Created types ".append (indTypes.map (λ it => it.name)).toString
      --mkAuxConstructions views TODO
      -- We need to invoke `applyAttributes` because `class` is implemented as an attribute.
      for view in views do
            Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
  return

def elabIIT (elems : Array Syntax) : CommandElabM Unit := do
  let views ← elems.mapM inductiveSyntaxToView
  let pers ← liftTermElabM none (preElabViews #[] views) -- replace #[]
  let params := pers.map PreElabResult.params
  let eits := erase $ pers.map PreElabResult.it
  let view0 := views[0]
  let ref := view0.ref
  runTermElabM view0.declName fun vars =>
     withRef ref $ declareInductiveTypes views vars params eits

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

-- TODO one index out of bounds error per sort

iit Con : Nat → Type where
| nil : Con

iit Ty : Con 0 → Type where
| U : Ty Con.nil

iit Tm : (Γ : Con 0) → Ty Γ → Type where

iit Foo : Type where

end

#check @Tm.E.rec
