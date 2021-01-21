import IIT

mutual

iit Con : Type where
| nil : Con
--| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U : (Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

--iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
--| El : (Γ : Con) → Tm Γ (Ty.U Γ)

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

--set_option pp.all true

noncomputable def Con_total : Con.tot := by
  totalityOuter 0 [Con, Ty] [Con.nil] [Ty.U]
  refine @Con.E.rec
          (fun Γ.e => ∀ Γ.w, PSigma (Con.r Con.m Ty.m Con.nil.m Ty.U.m { fst := Γ.e, snd := Γ.w }))
          (fun A.e => ∀ Γ Γ.m (Γ.r : Con.r Con.m Ty.m Con.nil.m Ty.U.m Γ Γ.m) A.w, 
            PSigma (@Ty.r Con.m Ty.m Con.nil.m Ty.U.m Γ Γ.m { fst := A.e, snd := A.w })) ?_ ?_ S.E S.w
  skip --TODO finde heraus, wie refine die typen der loecher inferiert

#check @Con.E.rec

#exit
noncomputable def Con_total : Con.tot := by
  totalityOuter 0 [Con, Ty, Tm] [Con.nil, Con.ext] [Ty.U, Ty.pi] [Tm.El]
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

#check Tm.El.r

noncomputable def Tm_total : Tm.tot := by
  totalityOuter 2 [Con, Ty, Tm] [Con.nil, Con.ext] [Ty.U, Ty.pi] [Tm.El]
/-  apply @Tm.E.rec
          (fun Γ.e => ∀ Γ.w, PSigma (Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m { fst := Γ.e, snd := Γ.w }))
          (fun A.e => ∀ Γ Γ.m (Γ.r : Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m) A.w, 
            PSigma (@Ty.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m { fst := A.e, snd := A.w }))
          (fun t.e => ∀ Γ Γ.m (Γ.r : Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m)
                        A A.m (A.r : @Ty.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m A A.m) t.w,
            PSigma (@Tm.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m A A.m { fst := t.e, snd := t.w}))
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
    intros Γ.E Γ.r Γ' Γ'.m Γ'.r A A.m A.r El.w
    have e : (Γ'.1 = Γ.E) ∧ (A.1 = Ty.U.E Γ'.1) := by {
      cases Γ';
      cases A;
      cases El.w;
      apply And.intro;
      rfl;
      rfl }
    cases Γ' with
    | mk Γ'.e Γ'.w =>
      cases A
      cases e.1
      cases e.2
      clear e
      refine PSigma.mk ?_ ?_
      --have e : A.m = Ty.U.m Γ'.m := by { cases A.r; rfl }
      --induction e
      --skip-/

#check Tm.Eld.r


inductive fivefive : (n : Nat) → Fin n → Prop where
| mk : fivefive 10 5

example (m x) (q : 5 < m) (p : fivefive m x) : (x = { val := 5, isLt := q }) := by
  cases p
  rfl

mutual

inductive ConE : Type where
|  nilE : ConE
|  extE : ConE → TyE → ConE

inductive TyE : Type where
|  UE : ConE → TyE
|  piE : ConE → TyE → TyE → TyE

inductive TmE : Type where
|  ElE : ConE → TmE

end

mutual

inductive Conw : ConE → Prop where
| nilw : Conw ConE.nilE
| extw : (ΓE : ConE) → Conw ΓE → (AE : TyE) → Tyw ΓE AE → Conw (ConE.extE ΓE AE)

inductive Tyw : ConE → TyE → Prop where
| Uw : (ΓE : ConE) → Conw ΓE → Tyw ΓE (TyE.UE ΓE)
| piw : (ΓE : ConE) → Conw ΓE → (AE : TyE) → Tyw ΓE AE → (BE : TyE) → Tyw (ConE.extE ΓE AE) BE → Tyw ΓE (TyE.piE ΓE AE BE)

inductive Tmw : ConE → TyE → TmE → Prop where
| Elw : (ΓE : ConE) → Conw ΓE → Tmw ΓE (TyE.UE ΓE) (TmE.ElE ΓE)

end

example (ΓE ΓE' AE) (w : Tmw ΓE AE (TmE.ElE ΓE')) : (ΓE = ΓE') ∧ (AE = TyE.UE ΓE) := by
  cases w
  apply And.intro
  rfl
  rfl
