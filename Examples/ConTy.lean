import IIT

mutual

set_option pp.all true
iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| U' : Ty Con.nil
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit_termination
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


noncomputable def Con.rec :
(Conm : Con → Type) →
  (Tym : {Γ : Con} → Conm Γ → Ty Γ → Type) →
    (Connilm : Conm Con.nil) →
      (Conextm : {Γ : Con} → (Γm : Conm Γ) → {A : Ty Γ} → Tym Γm A → Conm (Con.ext Γ A)) →
        (TyUm : {Δ : Con} → (Δm : Conm Δ) → Tym Δm (Ty.U Δ)) →
          (TyU'm : Tym Connilm Ty.U') →
            (Typim :
                {Γ : Con} →
                  (Γm : Conm Γ) →
                    {A : Ty Γ} →
                      (Am : Tym Γm A) →
                        {B : Ty (Con.ext Γ A)} → Tym (Conextm Γm Am) B → Tym Γm (Ty.pi Γ A B)) →
              (Γ : Con) → Conm Γ := by
  intros Con.m Ty.m Con.nil.m Con.ext.m Ty.U.m Ty.U'.m Ty.pi.m Γ
  exact PSigma.fst $ Con.tot Con.m Ty.m Con.nil.m Con.ext.m Ty.U.m Ty.U'.m Ty.pi.m Γ

noncomputable def Ty.rec :
(Conm : Con → Type) →
  (Tym : {Γ : Con} → Conm Γ → Ty Γ → Type) →
    (Connilm : Conm Con.nil) →
      (Conextm : {Γ : Con} → (Γm : Conm Γ) → {A : Ty Γ} → Tym Γm A → Conm (Con.ext Γ A)) →
        (TyUm : {Δ : Con} → (Δm : Conm Δ) → Tym Δm (Ty.U Δ)) →
          (TyU'm : Tym Connilm Ty.U') →
            (Typim :
                {Γ : Con} →
                  (Γm : Conm Γ) →
                    {A : Ty Γ} →
                      (Am : Tym Γm A) →
                        {B : Ty (Con.ext Γ A)} → Tym (Conextm Γm Am) B → Tym Γm (Ty.pi Γ A B)) →
  (Γ : Con) → (A : Ty Γ) → Tym (Con.rec Conm Tym Connilm Conextm TyUm TyU'm Typim Γ) A := by
  intros Con.m Ty.m Con.nil.m Con.ext.m Ty.U.m Ty.U'.m Ty.pi.m Γ A
  have r := PSigma.snd $ Con.tot Con.m Ty.m Con.nil.m Con.ext.m Ty.U.m Ty.U'.m Ty.pi.m Γ
  exact PSigma.fst $ Ty.tot Con.m Ty.m Con.nil.m Con.ext.m Ty.U.m Ty.U'.m Ty.pi.m Γ r A
