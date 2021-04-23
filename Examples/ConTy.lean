import IIT

set_option trace.Meta.Tactic.subst true
set_option trace.Meta.Tactic.cases true
set_option trace.Meta.Tactic true
inductive Con : Type
| nil : Con
| foo : Con

inductive Conw : Con → Prop
| nilw : Conw Con.nil

example (x : Conw Con.nil) : x = Conw.nilw := by
  cases x
  skip

#exit

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

end


--set_option trace.Meta.Tactic true
noncomputable def Con_total' : Con.tot  := by
  totalityOuter 0 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U']
  have foo : ctorw = Con.nil.w := by
    cases ctorw
    clear Ty.U'.m
    skip
  skip

#reduce Con_total'


#exit

noncomputable def Ty_total' : Ty.tot := by
  totalityOuter 1 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U']
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat { cases ctorw; assumption }
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  inversion ctorw
  apply Ty.U.m
  apply Ty.U.r
  assumption
  apply Ty.U'.m
  cases Γ.r
  simp at *
  apply Ty.U'.r

