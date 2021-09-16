import IIT

mutual

iit Con : Type
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit_termination
    apply Con.ext.m (Γ.ih _).1 (A.ih (Γ.ih _).2 _).1
    repeat assumption
    apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih (Γ.ih _).2 _).2)
    apply Ty.pi.m _ (A.ih _ _).1 (B.ih _ _).1
    repeat assumption
    apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _).2)
    repeat assumption
    apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
    repeat assumption
    apply Con.ext.m (Γ.ih _).1 (A.ih (Γ.ih _).2 _).1
    repeat assumption
    apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _).2)
    apply Ty.pi.m _ (A.ih _ _).1 (B.ih _ _).1
    repeat assumption
    apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _).2)
    repeat assumption
    apply Ty.pi.r (A.r := (A.ih _ _).2) (B.r := (B.ih _ _).2)
    repeat assumption

end
