import IIT

mutual

set_option pp.all true

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : (Γ : Con) → Tm Γ (Ty.U Γ)

iit_termination
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.U.m
  apply Ty.U.r
  repeat assumption
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
  apply Tm.El.r (Γ.m := Γ.m) (Γ.r := Γ.r)
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.U.m
  apply Ty.U.r
  repeat assumption
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
  apply Tm.El.r (Γ.m := Γ.m) (Γ.r := Γ.r)
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat assumption
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.U.m
  apply Ty.U.r
  repeat assumption
  apply Ty.pi.m (A.m := (A.ih _ _ _ _).1) (B.m := (B.ih _ _ _ _).1)
  repeat assumption
  apply Con.ext.r (Γ.m := Γ.m) (A.r := (A.ih _ _ _ _).2)
  repeat assumption
  apply Ty.pi.r (A.r := (A.ih _ _ _ _).2) (B.r := (B.ih _ _ _ _).2)
  repeat assumption
  clarifyIndices A.r
  apply Tm.El.m
  simp_all
  --clarifyIndices A.r
  admit
  
end

#check Tm.rec
