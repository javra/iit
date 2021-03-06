/- Prototype for an implementation of IITs -/
import Lean.Parser
import Lean.Elab
import Lean.Elab.Tactic.Basic
import IIT.InductiveUtils
import IIT.PreElab
import IIT.Erasure
import IIT.Wellformedness
import IIT.Sigma
import IIT.Relation
import IIT.ClarifyIndices
import IIT.Totality

namespace IIT

-- Parser

section Parser

open Lean.Parser
open Command

-- The syntax looks exactly like the one of inductive types, without the presence of modifiers
@[commandParser] def «iit» : Parser := 
leading_parser "iit " >> declId >> declSig >> Lean.Parser.optional (OrElse.orElse ":=" "where")  >> many ctor

-- The syntax for the totality proof opens a tactic environment
@[commandParser] def «iit_termination» : Parser :=
leading_parser:leadPrec "iit_termination " >> @Tactic.tacticSeq

end Parser

-- Elaborator

-- Elab a single IIT sort

section IITElab

open Lean.Elab.Command
open Lean.Elab
open Lean
open List
open Meta
open Tactic

def declareInductiveTypes (views : Array InductiveView) (pr : PreElabResult) : TermElabM Unit := do
  let decl := mkInductiveDeclEs pr.levelParams pr.numParams pr.its pr.isUnsafe
  Term.ensureNoUnassignedMVars decl
  addDecl decl
  mkAuxConstructions (pr.its.map InductiveType.name)
  for view in views do
    Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
  return

def elabIIT (elems : Array Syntax) : CommandElabM Unit := do
  let ⟨terminations, elems⟩ := elems.partition fun stx =>
    match stx with
    | `(iit_termination $x) => true
    | _                     => false
  -- There should be only one `iit_termination` command
  if terminations.size > 1 then throwIllFormedSyntax
  let termination := terminations[0][1]
  let views ← elems.mapM inductiveSyntaxToView
  let view0 := views[0]
  runTermElabM view0.declName fun vars => do
    withRef view0.ref do
      -- Elaborate IITs without declaring them (kernel would reject)
      let pr ← preElabViews vars views 
      -- Calculate and declare type erasure
      let eits := erase pr.its
      let epr := { pr with its := eits }
      declareInductiveTypes views epr
      -- Calculate and declare wellformedness predicate as an inductively defined proposition
      let wits := wellf pr.its eits
      let wpr := { pr with its := wits }
      declareInductiveTypes views wpr
      -- Calculate sigma construction and declare it
      let sigmaDecls ← sigmaDecls pr.its eits wits
      sigmaDecls.toArray.forM addDecl
      let ls := pr.its.map fun _ => levelOne --TODO make universe polymorphic
      withRecArgs pr.its ls fun motives methods => do
        let rits ← elimRelation motives methods pr.its
        let rpr := { pr with its := rits, 
                             numParams := pr.numParams + motives.size + methods.concat.size }
        declareInductiveTypes views rpr
        -- Calculate the types for totality lemmas
        let totTypes ← totalityTypes pr.its ls motives methods    
        -- Solve them using the tactics provided in by the termination block
        let mut totMVars : List MVarId := []
        let mut totVals : List Expr := []
        for i in [0:pr.its.length] do
          let totType := totTypes.get! i
          let mVar ← mkFreshExprMVar totType
          totVals := totVals.append [mVar]
          -- Run a helper tactic on all of the totality goals
          let ⟨_, s⟩ ← TacticM.run (totalityOuterTac i pr.its) ⟨mVar.mvarId!⟩ ⟨[mVar.mvarId!]⟩
          totMVars := totMVars.append s.goals
        -- Run remaining tactics to solve totality (this should in future be automated)
        TacticM.run' (Tactic.evalTacticSeq termination) ⟨totMVars.get! 0⟩ ⟨totMVars⟩
        for i in [0:pr.its.length] do
          let mv ← instantiateMVars $ totVals.get! i
          -- Declar `Hd.tot` for each sort `Hd`
          let decl := Declaration.defnDecl { name         := (pr.its.get! i).name ++ "tot",
                                             levelParams  := [], -- TODO
                                             value        := mv,
                                             type         := totTypes.get! i,
                                             hints        := arbitrary -- TODO
                                             safety       := DefinitionSafety.safe }
          addDecl decl



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
    (declKind == `«iit») || (declKind == `«iit_termination»)

-- If all declarations in a mutual block are IITs, elab thwem,
-- otherwise elab as before
@[commandElab «mutual»] def elabIITMutual : CommandElab :=
fun stx =>
  if isIITMutual stx then elabIIT stx[1].getArgs
  else elabMutual stx

end MutualElab

end IIT
