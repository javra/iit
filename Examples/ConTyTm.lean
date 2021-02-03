import IIT

mutual

iit Con : Type where
| nil : Con
--| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : Tm Con.nil (Ty.U Con.nil) --(Γ : Con) → Tm Γ (Ty.U Γ)

end

open IIT

noncomputable def Con_total' : Con.tot := by
  totalityOuter 0 [Con, Ty, Tm] [Con.nil] [Ty.U] [Tm.El]
  refine PSigma.mk ?_ ?_
  apply Con.nil.m
  apply Con.nil.r
  refine PSigma.mk ?_ ?_
  apply Ty.U.m
  apply Ty.U.r
  assumption
  refine PSigma.mk ?_ ?_
  have e' : (Γ.m = Con.nil.m) ∧ (A.m = Ty.U.m Γ.m) := by {  }
  cases e'
  have e' : A.m = Ty.U.m Con.nil.m := by { cases A.r }


section
variable (ConE TyE TmE : Type)
  (ConnilE : ConE) (TyUE : ConE → TyE) (TmElE : TmE)
  (Conm : ConE → Type) (Tym : ConE → TyE → Type) (Tmm : ConE → TyE → TmE → Type)
  (Connilm : Conm ConnilE) (TyUm : (ΔE : ConE) → (Δm : Conm ΔE) → Tym ΔE (TyUE ΔE))
  (TmElm : Tmm ConnilE (TyUE ConnilE) TmElE)

mutual
inductive Conr : (ΓE : ConE) → Conm ΓE → Type where
| nil : Conr ConnilE Connilm

inductive Tyr : (ΓE : ConE) → (Γm : Conm ΓE) → (AE : TyE) → (Am : Tym ΓE AE) → Type where
| U : (ΔE : ConE) → (Δm : Conm ΔE) → (Δr : Conr ΔE Δm) → Tyr ΔE Δm (TyUE ΔE) (TyUm ΔE Δm)

inductive Tmr : ∀ ΓE (Γm : Conm ΓE) AE (Am : Tym ΓE AE) tE (tm : Tmm ΓE AE tE), Type where
| El : Tmr ConnilE Connilm (TyUE ConnilE) (TyUm ConnilE Connilm) TmElE TmElm

end

example (Γm : Conm ConnilE) (Am : Tym ConnilE (TyUE ConnilE))
  (r : Tyr ConE TyE TmE ConnilE TyUE TmElE Conm Tym Tmm Connilm TyUm TmElm _ Γm _ Am)
  (r' : Conr ConE TyE TmE ConnilE TyUE TmElE Conm Tym Tmm Connilm TyUm TmElm _ Γm) :
   Am = TyUm ConnilE Connilm := by
  cases r
  cases r'
  rfl

end
