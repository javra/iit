import IIT

mutual

iit Con : Type where
| nil : Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : (Γ : Con) → Tm Γ (Ty.U Γ)

--iit Subb : (Δ Γ : Con) → Type where
--| swap : (Δ Γ : Con) → (A : Subb Γ Δ) → Subb Δ Γ

--iit Foo : (m n : Nat) → Type where
--| bar : Foo 5 3
--| baz : (m n : Nat) → /-(p : Foo n m) →-/ Foo m n

--iit Blubb : (Γ Δ : Con) → (n : Nat) → (A : Ty Δ) → (B : Ty Γ) → Type where

--iit Plapp : (Γ Δ Δ': Con) → (A : Ty Γ) → Type where
--| plapper : (Δ : Con) → Plapp Con.nil Δ Δ Ty.U'

end

open IIT

noncomputable def Cont_total : Con.tot := by
  totalityOuter 0 [Con, Ty, Tm] [Con.nil, Con.ext] [Ty.U, Ty.pi] [Tm.El]
  cases sMain with
  | PSigma.mk Γ.e Γ.w =>
    apply @Con.E.rec
            (fun Γ.e => ∀ Γ.w, PSigma (Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m { fst := Γ.e, snd := Γ.w }))
            (fun A.e => ∀ Γ Γ.m (Γ.r : Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m) A.w, 
              PSigma (@Ty.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m { fst := A.e, snd := A.w }))
            (fun t.e => PUnit)
    focus
      intro Γ.w'
      apply PSigma.mk
      apply Con.nil.r
    focus
      intros _ _ ih1 ih2 Γ.w'
      apply PSigma.mk
      apply Con.ext.r (Γ.r := (ih1 _).snd) (A.r := (ih2 _ _ _ _).snd)
      repeat { cases Γ.w'; assumption }
      apply (ih1 _).snd
    focus
      intros Δ _ Γ' _ _ U.w
      have e : Γ'.1 = Δ := by { cases U.w; rfl }
      induction e
      apply PSigma.mk
      apply Ty.U.r
      assumption
    focus
      intros Γ A B Γ.r A.r B.r Γ' Γ'.m Γ'.r π.w
      have e : Γ'.1 = Γ := by { cases π.w; rfl }
      induction e
      apply PSigma.mk
      apply Ty.pi.r (Γ.r := Γ'.r) (A.r := (A.r _ _ _ _).snd) (B.r := (B.r _ _ _ _).snd)
      cases π.w
      assumption
      assumption
      cases π.w
      assumption
      apply Con.ext.r
      assumption
      cases π.w
      apply (A.r _ _ _ _).snd
    focus
      intros
      exact ()

noncomputable def Ty_total : Ty.tot := by
  totalityOuter 1 [Con, Ty, Tm] [Con.nil, Con.ext] [Ty.U, Ty.pi] [Tm.El]
  cases sMain with
  | PSigma.mk A.e A.w =>
    apply @Ty.E.rec
            (fun Γ.e => ∀ Γ.w, PSigma (Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m { fst := Γ.e, snd := Γ.w }))
            (fun A.e => ∀ Γ Γ.m (Γ.r : Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m) A.w, 
              PSigma (@Ty.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m { fst := A.e, snd := A.w }))
            (fun t.e => PUnit)
    focus
      intro Γ.w'
      apply PSigma.mk
      apply Con.nil.r
    focus
      intros _ _ ih1 ih2 Γ.w'
      apply PSigma.mk
      apply Con.ext.r (Γ.r := (ih1 _).snd) (A.r := (ih2 _ _ _ _).snd)
      repeat { cases Γ.w'; assumption }
      apply (ih1 _).snd
    focus
      intros Δ _ Γ' _ _ U.w
      have e : Γ'.1 = Δ := by { cases U.w; rfl }
      induction e
      apply PSigma.mk
      apply Ty.U.r
      assumption
    focus
      intros Γ A B Γ.r A.r B.r Γ' Γ'.m Γ'.r π.w
      have e : Γ'.1 = Γ := by { cases π.w; rfl }
      induction e
      apply PSigma.mk
      apply Ty.pi.r (Γ.r := Γ'.r) (A.r := (A.r _ _ _ _).snd) (B.r := (B.r _ _ _ _).snd)
      cases π.w
      assumption
      assumption
      cases π.w
      assumption
      apply Con.ext.r
      assumption
      cases π.w
      apply (A.r _ _ _ _).snd
    focus
      intros
      exact ()
    assumption
