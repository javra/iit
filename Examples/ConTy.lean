import IIT

mutual

iit Con : Type
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type
| U : (Δ : Con) → Ty Δ
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit_termination
  · apply Ty.pi.m _ (A.ih _ _).1 (B.ih (Con.ext.r _ _ _ _ _ _ _ (A.ih _ _).2) _).1
    repeat assumption 
  · apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
    repeat assumption
  · apply Ty.pi.m _ (A.ih _ _).1 (B.ih (Con.ext.r _ _ _ _ _ _ _ (A.ih _ _).2) _).1
    repeat assumption 
  · apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
    repeat assumption

end
