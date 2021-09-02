import IIT

mutual

iit A : Type
| ι   : (n : Nat) → A
| mid : (x y : A) → lt' x y → A

iit lt' : (x : A) → (y : A) → Type
| ι     : (m n : Nat) → (p : m < n) → lt' (A.ι m) (A.ι n)

iit_termination
  admit
  admit
  admit
  admit
  admit
  admit
  admit
  admit
  admit
  admit
  admit
  admit

end