/- Type Erasure for IITs -/

import Lean.Elab.Command
import Init.Data.Array.Basic

open Lean
open Elab
open Array
open Expr

namespace IIT

def erasureSuffix : String := "E"

def eraseHeader : Expr → Expr := λ e => 
match e with
| forallE n f e x => eraseHeader e
| _ => e

def collectHeaderNames (its : List InductiveType) : Array Name :=
its.toArray.map InductiveType.name

def isHeaderApp (e : Expr) (its : List InductiveType) : Bool :=
match e with
| const n l d => contains (collectHeaderNames its) n
| app f e d   => isHeaderApp f its
| _           => false

def addEIfHeader (n : Name) (its : List InductiveType) : Name :=
if contains (collectHeaderNames its) n then n ++ erasureSuffix
else n

def eraseCtor (e : Expr) (its : List InductiveType) : Expr :=
match e with
| forallE n t b d => mkForall n e.binderInfo (eraseCtor t its) (eraseCtor b its)
| lam n t b d     => mkLambda n e.binderInfo (eraseCtor t its) (eraseCtor b its)
| app f e d       => if isHeaderApp f its then eraseCtor f its -- erase applications of sorts
                     else mkApp (eraseCtor f its) (eraseCtor e its)
| const n l d     => mkConst (addEIfHeader n its) l
| _               => e

def erase (its : List InductiveType) : List InductiveType :=
its.map fun it => { name := it.name ++ erasureSuffix, 
                    type := eraseHeader it.type,
                    ctors := it.ctors.map fun ctor => { name := ctor.name ++ erasureSuffix,
                                                        type := eraseCtor ctor.type its } }

end IIT
