/- Type Erasure for IITs -/

import Lean.Elab.Command
import Lean.Elab.Inductive
import Init.Data.Array.Basic

open Lean.Elab.Command
open Lean
open Array

namespace IIT

open Expr

def erasureSuffix : String := "E"

def eraseSort : Expr → Expr := λ e => 
match e with
| forallE n f e x => eraseSort e
| _ => e

def collectSortNames (its : List InductiveType) : Array Name :=
its.toArray.map InductiveType.name

def isSortApp (e : Expr) (its : List InductiveType) : Bool :=
match e with
| const n l d => contains (collectSortNames its) n -- this is probably not necessary
| fvar n d    => contains (collectSortNames its) n
| app f e d   => isSortApp f its
| _           => false

def addEIfSort (n : Name) (its : List InductiveType) : Name :=
if contains (collectSortNames its) n then n ++ erasureSuffix
else n

def eraseCtor (e : Expr) (its : List InductiveType) : Expr :=
match e with
| forallE n t b d => mkForall n e.binderInfo (eraseCtor t its) (eraseCtor b its)
| lam n t b d     => mkLambda n e.binderInfo (eraseCtor t its) (eraseCtor b its)
| app f e d       => if isSortApp f its then eraseCtor f its -- erase applications of sorts
                     else mkApp (eraseCtor f its) (eraseCtor e its)
| const n l d     => mkConst (addEIfSort n its) l
--| fvar n d        => mkConst (addEIfSort n its) []
| _               => e

def erase (its : List InductiveType) : List InductiveType :=
its.map $ λ it => { name := it.name ++ erasureSuffix, 
                    type := eraseSort it.type,
                    ctors := it.ctors.map (λ ctor => { name := ctor.name ++ erasureSuffix,
                                                       type := eraseCtor ctor.type its } ) }

end IIT
