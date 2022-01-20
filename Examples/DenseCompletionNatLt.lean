import IIT

mutual

iit A : Type
| ι   : (n : Nat) → A
| mid : (x y : A) → (p : lt' x y) → A

iit lt' : (x : A) → (y : A) → Type
| ι     : (m n : Nat) → (p : m < n) → lt' (A.ι m) (A.ι n)
| mid_l : (x y : A) → (p : lt' x y) → lt' x (A.mid x y p)
| mid_r : (x y : A) → (p : lt' x y) → lt' (A.mid x y p) y

iit_termination
  · apply A.mid.m (x.ih _).1 (y.ih _).1 (p.ih (x.ih _).2 (y.ih _).2 _).1
    repeat assumption
  · apply A.mid.r (x.r := (x.ih _).2) (y.r := (y.ih _).2) (p.r := (p.ih (x.ih _).2 (y.ih _).2 _).2)
  · have : (x.ih _).1 = x.m := sorry
    cases this
    apply lt'.mid_l.m (x.ih _).1 (y.ih _).1 (p.ih _ _ _).1
    skip
  · skip
  · skip
  · skip
  · apply A.mid.m (x.ih _).1 (y.ih _).1 (p.ih (x.ih _).2 (y.ih _).2 _).1
    repeat assumption
  · apply A.mid.r (x.r := (x.ih _).2) (y.r := (y.ih _).2) (p.r := (p.ih (x.ih _).2 (y.ih _).2 _).2)
  · skip
  · skip
  · skip
  · skip

end