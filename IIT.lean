/- Prototype for an implementation of IITs -/
import Lean.Parser
import Lean.Elab
import IIT.InductiveUtils
import IIT.PreElab
import IIT.Erasure
import IIT.Wellformedness

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

def declareInductiveTypes (views : Array InductiveView) (pr : PreElabResult) : TermElabM Unit := do
  let view0 := views[0]
  let decl := Declaration.inductDecl pr.levelParams pr.numParams pr.its pr.isUnsafe
  Term.ensureNoUnassignedMVars decl
  addDecl decl
  --mkAuxConstructions views TODO maybe call this with updated views, that just replace name?s
  --throwErrorAt view0.ref $ "Created types ".append (pr.its.map (λ it => it.name)).toString
  for view in views do
        Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
  return

def elabIIT (elems : Array Syntax) : CommandElabM Unit := do
  let views ← elems.mapM inductiveSyntaxToView
  let view0 := views[0]
  runTermElabM view0.declName fun vars => do
    withRef view0.ref do
      let pr ← preElabViews vars views
      let eits := erase pr.its
      let epr := { pr with its := eits }
      declareInductiveTypes views epr
      let wits := wellf pr.its eits
      let wpr := { pr with its := wits }
      declareInductiveTypes views wpr

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
  if isIITMutual stx then elabIIT stx[1].getArgs
  else elabMutual stx

end MutualElab

end IIT

--set_option trace.Elab true
--set_option syntaxMaxDepth 10
--set_option pp.raw true

mutual

iit Con : Type where
--| nil : Con
--| ext : ∀ (Γ : Con), Ty Γ → Con

iit Ty : Con → Type where
--| U : ∀ (Γ : Con), Ty Γ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → Ty Γ → Type where

iit Foo : Type where
 
end

#check @Ty.w
