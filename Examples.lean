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

#check @Con.E.rec

mutual

/-variables
  (Con.m : Con → Type)
  (Ty.m : {Γ : Con} → Con.m Γ → Ty Γ → Type)
  (Tm.m : {Γ : Con} → (Γ.m : Con.m Γ) → {A : Ty Γ} → @Ty.m Γ Γ.m A → Tm Γ A → Type)
  (Con.nil.m : Con.m Con.nil)
  (Con.ext.m : {Γ : Con} → (Γ.m : Con.m Γ) → {A : Ty Γ} → @Ty.m Γ Γ.m A → Con.m (Con.ext Γ A))
  (Ty.U.m : {Δ : Con} → (Δ.m : Con.m Δ) → @Ty.m Δ Δ.m (Ty.U Δ))
  (Ty.pi.m :
                {Γ : Con} →
                  (Γ.m : Con.m Γ) →
                    {A : Ty Γ} →
                      (A.m : @Ty.m Γ Γ.m A) →
                        {B : Ty (Con.ext Γ A)} →
                          @Ty.m (Con.ext Γ A) (@Con.ext.m Γ Γ.m A A.m) B → @Ty.m Γ Γ.m (Ty.pi Γ A B))
  (Tm.El.m : {Γ : Con} → (Γ.m : Con.m Γ) → @Tm.m Γ Γ.m (Ty.U Γ) (@Ty.U.m Γ Γ.m) (Tm.El Γ))
-/

def Con_total : Con.tot := by
  intros Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ
  cases Γ with
  | PSigma.mk Γ.e Γ.w =>
    induction Γ.e with
    | _ => skip

def Tm_total : Tm.tot := by
  intros Con.m Ty.m Tm.m Con.nil.m Con.ext.m Ty.U.m Ty.pi.m Tm.El.m Γ Γ.m Γ.r A A.m A.r t
  induction t with 
  | PSigma.mk t.e t.w =>
    cases t.e with
    | El.E Γ' => _

end

#exit

mutual

inductive ConE : Type where
| nilE : ConE
| extE : ConE → TyE → ConE

inductive TyE : Type where
| UE : ConE → TyE

end

#check @ConE.recOn

noncomputable def length (ΓE : ConE) : Nat := by
  apply @ConE.recOn (fun _ => Nat) (fun _ => Unit) ΓE
  case nilE =>
    exact 0
  case extE => 
    intros ΓE AE ih1 ih2
    exact ih1 + 1
  case UE =>
    intros ΓE ih1
    exact ()

#reduce length (ConE.extE ConE.nilE _)
