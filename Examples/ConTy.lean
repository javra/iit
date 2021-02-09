import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

end

noncomputable def Con_total' : Con.tot  := by
  totalityOuter 0 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U']
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat { cases ctorw; assumption }
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.U.m
  apply Ty.U.r
  assumption
  clarifyIndices Γ.r
  apply Ty.U'.m
  cases Γ.r
  simp at *
  apply Ty.U'.r

noncomputable def Ty_total' : Ty.tot := by
  totalityOuter 1 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U']
  apply Con.nil.m
  apply Con.nil.r
  apply Con.ext.m (Γ.m := (Γ.ih _).1) (A.m := (A.ih _ _ _ _).1)
  repeat { cases ctorw; assumption }
  simp at *
  apply (Γ.ih _).2
  apply Con.ext.r (Γ.r := (Γ.ih _).2) (A.r := (A.ih _ _ _ _).2) -- this is sooo fragile!
  apply Ty.U.m
  apply Ty.U.r
  assumption
  clarifyIndices Γ.r
  apply Ty.U'.m
  cases Γ.r
  simp at *
  apply Ty.U'.r

