/- General purpose utility functions -/
import Lean.Expr

namespace Lean

namespace Expr

def liftBVarsOne (e : Expr) : Expr := liftLooseBVars e 0 1

def liftBVarsTwo (e : Expr) : Expr := liftLooseBVars e 0 2

end Expr

end Lean

namespace Array

def concat {α} (xss : Array (Array α)) : Array α := Array.foldl Array.append #[] xss

end Array
