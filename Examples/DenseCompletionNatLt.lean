import IIT

mutual

set_option pp.all true
iit A : Type
| ι   : (n : Nat) → A
| mid : (x y : A) → lt' x y → A

iit lt' : (x : A) → (y : A) → Type
| ι     : (m n : Nat) → (p : m < n) → lt' (A.ι m) (A.ι n)
| mid_l : (x y : A) → (p : lt' x y) → lt' x (A.mid x y p)
| mid_r : (x y : A) → (p : lt' x y) → lt' (A.mid x y p) y

iit_termination
  repeat admit
  done

end