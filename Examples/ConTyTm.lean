import IIT

mutual

iit Con : Type where
| nil : Con
--| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : Tm Con.nil (Ty.U Con.nil) --(Γ : Con) → Tm Γ (Ty.U Γ)

end

open IIT

noncomputable def Con_total' : Con.tot := by
  totalityOuter 0 [Con, Ty, Tm] [Con.nil] [Ty.U] [Tm.El]
  apply Con.nil.m
  apply Con.nil.r
  apply Ty.U.m
  apply Ty.U.r
  assumption
  have e : Con.nil.m = Γ.m := by { cases Γ.r; rfl }
  induction e
  have e : Ty.U.m _ = A.m := by { cases A.r; rfl }
  induction e
  apply Tm.El.m
  cases A.r
  cases Γ.r
  simp at *
  apply Tm.El.r Con.m Ty.m Tm.m Con.nil.m Ty.U.m Tm.El.m

noncomputable def Ty_total' : Ty.tot := by
  totalityOuter 1 [Con, Ty, Tm] [Con.nil] [Ty.U] [Tm.El]
  apply Con.nil.m
  apply Con.nil.r
  apply Ty.U.m
  apply Ty.U.r
  assumption
  have e : Con.nil.m = Γ.m := by { cases Γ.r; rfl }
  induction e
  have e : Ty.U.m _ = A.m := by { cases A.r; rfl }
  induction e
  apply Tm.El.m
  cases A.r
  cases Γ.r
  simp at *
  apply Tm.El.r Con.m Ty.m Tm.m Con.nil.m Ty.U.m Tm.El.m
