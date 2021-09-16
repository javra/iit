import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : (Δ : Con) → Tm Δ (Ty.U Δ)

iit_termination
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)
  /-repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
  repeat assumption
  apply Con.ext.m _ (A.ih (Γ.ih _).2 _).1
  repeat assumption
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)
  apply Ty.pi.m _ (A.ih _ _).1 (B.ih _ _).1
  repeat assumption
  apply Con.ext.r (A.r := (A.ih _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
  repeat assumption
  apply Con.ext.m _ (A.ih (Γ.ih _).2 _).1
  repeat assumption
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _).2)
  apply Ty.pi.m _ (A.ih _ _).1 (B.ih _ _).1
  repeat assumption
  apply Con.ext.r (A.r := (A.ih _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
  repeat assumption-/

end

