import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

end

noncomputable def Con_total' : Con.tot := by
  totalityOuter 0 [Con, Ty] [Con.nil, Con.ext] [Ty.U]
  intro Γ.w'
  apply PSigma.mk
  apply Con.nil.r
  intros Γ.w
  apply PSigma.mk
  apply Con.ext.r (Γ.r := (Γ.ih _).snd) (A.r := (A.ih _ _ _ _).snd)
  repeat { cases Γ.w; assumption }
  cases Γ.w
  apply (Γ.ih _).snd
  intros  Γ'' Γ.m'' Γ.r'' Uw
  have e : Γ''.1 = Δ.E := by { cases Uw; rfl }
  induction e
  apply PSigma.mk
  apply Ty.U.r
  assumption

noncomputable def Ty_total' : Ty.tot := by
  totalityOuter 1 [Con, Ty] [Con.nil, Con.ext] [Ty.U]
  intro Γ.w'
  apply PSigma.mk
  apply Con.nil.r
  intros Γ.w
  apply PSigma.mk
  apply Con.ext.r (Γ.r := (Γ.ih _).snd) (A.r := (A.ih _ _ _ _).snd)
  repeat { cases Γ.w; assumption }
  cases Γ.w
  apply (Γ.ih _).snd
  intros  Γ'' Γ.m'' Γ.r'' Uw
  have e : Γ''.1 = Δ.E := by { cases Uw; rfl }
  induction e
  apply PSigma.mk
  apply Ty.U.r
  assumption

#check Ty_total'
