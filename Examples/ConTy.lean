import IIT

mutual

iit Con : Type
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit_termination
  skip

end