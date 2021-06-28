import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit_termination
  focus
    totalityOuter 0 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U', Ty.pi]
    apply Con.nil.m
    apply Con.nil.r
    apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ (Γ.ih _).2 _).1)
    repeat assumption
    apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
    apply Ty.U.m
    apply Ty.U.r
    assumption
    apply Ty.U'.m
    clarifyIndices Γ.r
    apply Ty.U'.r
    apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
    repeat assumption
    apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
    repeat assumption
    apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
    repeat assumption
  focus
    totalityOuter 1 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U', Ty.pi]
    apply Con.nil.m
    apply Con.nil.r
    apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ (Γ.ih _).2 _).1)
    repeat assumption
    apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
    apply Ty.U.m
    apply Ty.U.r
    assumption
    apply Ty.U'.m
    clarifyIndices Γ.r
    apply Ty.U'.r
    apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
    repeat assumption
    apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
    repeat assumption
    apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
    repeat assumption

end