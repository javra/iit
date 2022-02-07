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
import IIT.Recursor

namespace IIT

-- Parser

section Parser

open Lean.Parser
open Command

-- The syntax looks exactly like the one of inductive types, without the presence of modifiers
syntax (name := «iit») "iit" declId declSig (":= " <|> "where")? ctor* : command

-- The syntax for the totality proof opens a tactic environment
syntax (name := «iit_termination») "iit_termination" Tactic.tacticSeq : command

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
  let views ← elems.mapM inductiveSyntaxToView
  if views.size = 0 then throwError "Empty IIT declaration."
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
        let ctorss : List (Array Constructor) := rits.map fun rit => rit.ctors.toArray
        --let ctors : Array Constructor := ctorss.toArray.concat
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
          -- TODO make this tactic stronger to actually _solve_ those goals!
          let newMVars ← Tactic.run mVar.mvarId! (totalityOuterTac i pr.its)
          --let newMVars := [mVar.mvarId!]
          totMVars := totMVars.append newMVars
        -- Run remaining tactics to solve totality (this should in future be automated)
        if totMVars.length > 0 then
            -- There should be only one `iit_termination` command
          unless (terminations.size = 1) do throwError "Need to supply a `iit_termination` command to solve totality."
          let termination := terminations[0][1][0]
          let ⟨_, s⟩ ← (Tactic.evalTactic termination { main := totMVars.get! 0, elaborator := Name.anonymous }).run { goals := totMVars }
          unless s.goals.length = 0 do throwError "Tactic block does't solve all goals"
        for i in [0:pr.its.length] do
          let mv ← instantiateMVars $ totVals.get! i
          -- Declare `Hd.tot` for each sort `Hd`
          let decl := Declaration.defnDecl { name         := (pr.its.get! i).name ++ totalitySuffix,
                                             levelParams  := [], -- TODO
                                             value        := mv,
                                             type         := totTypes.get! i,
                                             hints        := default -- TODO
                                             safety       := DefinitionSafety.safe }
          addDecl decl
        -- Declare recursors
        let recDecls ← recDecls pr.its ls motives methods
        recDecls.toArray.forM addDecl

end IITElab

-- Elaborate mutual blocks consisting of only IIT declarations

section MutualElab

open Lean.Elab.Command
open Lean

  -- Throw an error when encountering a lone IIT or termination declaration
  @[commandElab «iit»] def elabLoneIIT : CommandElab :=
  λ _ => throwError "Must declare IIT in a 'mutual' block."

  @[commandElab «iit_termination»] def elabLoneIITTermination : CommandElab :=
  λ _ => throwError "Must declare IIT Termination in a 'mutual' after a series of IIT declarations."

  -- Checks if all declarations in the block are IITs
  private def isIITMutual (stx : Syntax) : Bool := stx[1].getArgs.all fun elem =>
    let declKind := elem[0].getKind
    (declKind == `«iit») || (declKind == `«iit_termination»)

  -- If all declarations in a mutual block are IITs, elab them, otherwise elab as before
  @[commandElab «mutual»] def elabIITMutual : CommandElab := fun stx =>
    if isIITMutual stx then elabIIT stx[1].getArgs
    else elabMutual stx

end MutualElab

builtin_initialize Lean.registerTraceClass `IIT.Totality

end IIT
