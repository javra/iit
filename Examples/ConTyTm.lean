import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : Tm Con.nil (Ty.U Con.nil) --(Γ : Con) → Tm Γ (Ty.U Γ)

end

open IIT

--set_option trace.Meta.isDefEq true in
noncomputable def Con_total' : Con.tot := by
  totalityOuter 0 [Con, Ty, Tm] [Con.nil, Con.ext] [Ty.U] [Tm.El]
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  simp at *
  have Δ.w : Con.w Δ.E := by { assumption }
  apply Ty.U.m (Δ.m := (Δ.ih Δ.w).1)

noncomputable def Ty_total' : Ty.tot := by
  totalityOuter 1 [Con, Ty, Tm] [Con.nil, Con.ext] [Ty.U] [Tm.El]
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.U.m
  apply Ty.U.r
  assumption
  apply Tm.El.m
  cases A.r
  cases Γ.r
  simp at *
  apply Tm.El.r
