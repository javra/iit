/- Inversion lemmas for the wellformedness predicate -/

import IIT.Wellformedness

open Lean
open Elab
open Command
open Meta
open Array

namespace IIT



end IIT

#check Nat.le

inductive contains0: List Nat → Prop where
| in_hd : ∀ l, contains0 (0 :: l)
| in_tl : ∀ l b, contains0 l → contains0 (b :: l)

example : ∀ l : List Nat, contains0 (1 :: l) → contains0 l := by
  intros l H
  cases H
  assumption

inductive Le : Nat → Nat → Prop where
| Le0 : ∀ n, Le 0 n
| LeS : ∀ n m, Le n m → Le (Nat.succ n) (Nat.succ m)

example (P : Nat → Nat → Prop) (Q : ∀ n m, Le n m → P n m) (n m : Nat) (H : Le (Nat.succ n) m) : P n m := by
  cases H
  apply Q
  cases H
