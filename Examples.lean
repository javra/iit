import IIT

--set_option trace.Elab true
--set_option syntaxMaxDepth 10
--set_option pp.all true

mutual

iit Con : Type where
| nil : Con
| foo : (b : Bool) → (n : Nat) → Con
| bla : (Γ Δ : Con) → Con
| ext : (Γ : Con) → (A : Ty Γ) → Con

iit Ty : (Γ : Con) → Type where
| U' : Ty Con.nil
--| U : (Γ Δ : Con) → Ty Δ
--| pi : ∀ (Γ : Con) (A : Ty Γ) (B : Ty (Con.ext Γ A)), Ty Γ

iit Tm : (Γ : Con) → (A : Ty Γ) → Type where
| El : Tm Con.nil Ty.U'

iit Subb : (Δ Γ : Con) → Type where
--| swap : (Δ Γ : Con) → (A : Subb Γ Δ) → Subb Δ Γ

iit Foo : (m n : Nat) → Type where
| bar : Foo 5 3
| baz : (m n : Nat) → /-(p : Foo n m) →-/ Foo m n

iit Blubb : (Γ Δ : Con) → (n : Nat) → (A : Ty Δ) → (B : Ty Γ) → Type where

iit Plapp : (Γ Δ Δ': Con) → (A : Ty Γ) → Type where
--| plapper : (Δ : Con) → Plapp Con.nil Δ Δ Ty.U'

end

variables (Con.m : Con → Prop)
  (Ty.m : {Γ : Con} → Con.m Γ → Ty Γ → Prop)
  (Tm.m : {Γ : Con} → (Γ.m : Con.m Γ) → {A : Ty Γ} → @Ty.m Γ Γ.m A → Tm Γ A → Prop)
  (Subb.m : {Δ : Con} → Con.m Δ → {Γ : Con} → Con.m Γ → Subb Δ Γ → Prop)
  (Foo.m : (m n : Nat) → Foo m n → Prop)
  (Blubb.m : {Γ : Con} →
                (Γ.m : Con.m Γ) →
                  {Δ : Con} →
                    (Δ.m : Con.m Δ) →
                      (n : Nat) → {A : Ty Δ} → @Ty.m Δ Δ.m A → {B : Ty Γ} → @Ty.m Γ Γ.m B → Blubb Γ Δ n A B → Prop)
  (Plapp.m : {Γ : Con} →
                  (Γ.m : Con.m Γ) →
                    {Δ : Con} → Con.m Δ → {Δ' : Con} → Con.m Δ' → {A : Ty Γ} → @Ty.m Γ Γ.m A → Plapp Γ Δ Δ' A → Prop)
  (Con.nil.m : Con.m Con.nil)

#check Con.bla.r Con.m Ty.m Tm.m Subb.m Foo.m Blubb.m Plapp.m Con.nil.m
