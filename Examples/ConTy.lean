import IIT

set_option trace.Meta.appBuilder true
mutual

iit Con : Type
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit_termination
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)

end

#check Con.rec