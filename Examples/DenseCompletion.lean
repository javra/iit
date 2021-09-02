import IIT

mutual

iit A' (A : Type)(rel : A → A → Prop) : Type
| ι   : ∀(a : A), A'
| mid : ∀(a b : A')(p : rel' A rel a b), A'

iit rel' (A : Type)(rel : A → A → Prop) : A' A rel → A' A rel → Prop
| ι     : ∀(a b : A)(p : rel a b), rel' (A'.ι a) (A'.ι b)
| mid_l : ∀(a b : A')(p : rel' a b), rel' a (A'.mid a b p)
| mid_r : ∀(a b : A')(p : rel' a b), rel' (A'.mid a b p) b

iit_termination
  admit

end
