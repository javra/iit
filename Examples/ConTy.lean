import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
--| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

end

noncomputable def Con_total' : Con.tot := by
  totalityOuter 0 [Con, Ty] [Con.nil, Con.ext] [Ty.U']

#exit

noncomputable def Ty_total' : Ty.tot := by
  totalityOuter 1 [Con, Ty] [Con.nil, Con.ext] [Ty.U, Ty.U']
  apply PSigma.mk
  apply Con.nil.r
  apply PSigma.mk
  apply Con.ext.r (Γ.r := (Γ.ih _).snd) (A.r := (A.ih _ _ _ _).snd)
  repeat { cases ctorw; assumption }
  apply (Γ.ih _).snd
  focus
    have e : Γ.E = Δ.E := by { cases ctorw; rfl }
    induction e
    apply PSigma.mk
    apply Ty.U.r
    assumption
  focus
   have e : Con.nil.E = Γ.E := by { cases ctorw; rfl }
   induction e
   have e' : Γ.m = Con.nil.m := by { cases Γ.r; rfl }
   induction e'
   refine PSigma.mk ?_ ?_
   apply Ty.U'.m
   apply Ty.U'.r
