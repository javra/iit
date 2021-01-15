import IIT

--set_option trace.Elab true
--set_option syntaxMaxDepth 10
--set_option pp.all true

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

#check @Con.E.recOn
#check CoeT.mk

set_option pp.all true
set_option trace.Meta.isDefEq true

def Con_total : Con.tot := by
  intros Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ
  cases Γ with
  | PSigma.mk Γ.e Γ.w =>
    skip
    apply @Con.E.rec
            (fun Γ.e => ∀ Γ.w, PSigma (Con.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m { fst := Γ.e, snd := Γ.w }))
            (fun A.e => ∀ Γ Γ.m A.w, PSigma (@Ty.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m { fst := A.e, snd := A.w }))
            (fun t.e => PUnit)
    focus
      intro Γ.w'
      apply PSigma.mk
      apply Con.nil.r
    focus
      intros Γ.e A.e ih1 ih2 Γ.w'
      apply PSigma.mk
      cases Γ.w' with
      | Con.ext.w _ Γ.w'' _ A.w'' =>
        --have r' := Con.ext.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m 
        --            { fst := Γ.e, snd := Γ.w'' } (ih1 Γ.w'').snd
        --            { fst := A.e, snd := A.w'' } (ih2 {fst := Γ.e , snd := Γ.w''} (ih1 Γ.w'').fst A.w'').snd
        --simp
        apply Con.ext.r Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m 
                { fst := Γ.e, snd := Γ.w'' } (ih1 Γ.w'').snd 
                { fst := A.e, snd := A.w'' } (ih2 {fst := Γ.e , snd := Γ.w''} (ih1 Γ.w'').fst A.w'').snd

