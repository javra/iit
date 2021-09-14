import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : (Δ : Con) → Tm Δ (Ty.U Δ)

iit_termination
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption
  clarifyIndices A.r
  apply Tm.El.m
  simp_all
  clarifyIndices A.r
  apply Tm.El.r (Δ.m := Γ.m) (Δ.r := Γ.r)
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption
  clarifyIndices A.r
  apply Tm.El.m
  simp_all
  clarifyIndices A.r
  apply Tm.El.r (Δ.m := Γ.m) (Δ.r := Γ.r)
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  simp at *
  repeat assumption
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption
  clarifyIndices A.r
  apply Tm.El.m
  cases Γ with | mk Γ.E Γ.w => ?_
  renameI Δ.w' Δ.m Δ.r Δ.w U.w U.m A.r' A.w
  have UmTyUm : U.m = Ty.U.m Δ.m := by cases A.r' <;> rfl
  cases UmTyUm
  exact Tm.El.r Con.m @Ty.m @Tm.m @Con.nil.m @Con.ext.m @Ty.U.m @Ty.pi.m @Tm.El.m
    (PSigma.mk Δ.E Δ.w') Δ.r

end
