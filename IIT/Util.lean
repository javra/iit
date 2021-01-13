/- General purpose utility functions -/
import Lean.Expr
import Lean.Elab

open Lean
open Elab
open Meta

namespace Lean

namespace Expr

def liftBVarsOne (e : Expr) : Expr := liftLooseBVars e 0 1

def liftBVarsTwo (e : Expr) : Expr := liftLooseBVars e 0 2

def liftBVarsThree (e : Expr) : Expr := liftLooseBVars e 0 3

def resultingLevel (e : Expr) : Level :=
match e with
| forallE n t b d => resultingLevel b
| sort l d        => l
| _ => levelZero

def mkSigma (l : Level) (α β : Expr) : Expr :=
mkApp (mkApp (mkConst `PSigma [l, levelZero]) α) β

def mkFst (x : Expr) : Expr := mkProj `PSigma 0 x

def mkSnd (x : Expr) : Expr := mkProj `PSigma 1 x

def mkPair (p q : Expr) : TermElabM Expr := mkAppM `PSigma.mk #[p, q]

end Expr

end Lean

namespace Array

def concat {α} (xss : Array (Array α)) : Array α := Array.foldl Array.append #[] xss

end Array
