import IIT.PropInversion
import IIT.ClarifyIndices

/-
iit A : Type
| ι   : (n : Nat) → A
| mid : (x y : A) → (p : lt' x y) → A

iit lt' : (x : A) → (y : A) → Type
| ι'    : (m n : Nat) → (p : m < n) → lt' (A.ι m) (A.ι n)
| mid_l : (x y : A) → (p : lt' x y) → lt' x (A.mid x y p)
| mid_r : (x y : A) → (p : lt' x y) → lt' (A.mid x y p) y
-/

mutual
inductive Aₑ : Type 1
| ιₑ   : Nat → Aₑ
| midₑ : (x y : Aₑ) → (p : lt'ₑ) → Aₑ


inductive lt'ₑ : Type 1
| ι'ₑ : (m n : Nat) → (p : m < n) → lt'ₑ
| mid_lₑ : (x y : Aₑ) → (p : lt'ₑ) → lt'ₑ
| mid_rₑ : (x y : Aₑ) → (p : lt'ₑ) → lt'ₑ
end

open Aₑ lt'ₑ

mutual
inductive A_w : Aₑ → Prop
| ι_w : ∀ n, A_w (ιₑ n)
| mid_w : ∀ {x}, A_w x → ∀ {y}, A_w y → ∀ {p}, lt'_w x y p → A_w (midₑ x y p)

inductive lt'_w : Aₑ → Aₑ → lt'ₑ → Prop
| ι'_w : ∀ m n p, lt'_w (ιₑ m) (ιₑ n) (ι'ₑ m n p)
| mid_l_w : ∀ {x}, A_w x → ∀ {y}, A_w y → ∀ {p}, lt'_w x y p 
    → lt'_w x (midₑ x y p) (mid_lₑ x y p)
| mid_r_w : ∀ {x}, A_w x → ∀ {y}, A_w y → ∀ {p}, lt'_w x y p 
    → lt'_w (midₑ x y p) y (mid_rₑ x y p)
end

open A_w lt'_w

def A := PSigma A_w
def lt' := fun (x y : A) => PSigma (lt'_w x.1 y.1)

def ι : Nat → A := fun n => ⟨ιₑ n, ι_w n⟩
def mid (x y : A) (p : lt' x y) : A := ⟨midₑ x.1 y.1 p.1, mid_w x.2 y.2 p.2⟩ 
def ι' (m n : Nat) (p : m < n) : lt' (ι m) (ι n) := ⟨ι'ₑ m n p, ι'_w m n p⟩
def mid_l (x y : A) (p : lt' x y) : lt' x (mid x y p) :=
  ⟨mid_lₑ x.1 y.1 p.1, mid_l_w x.2 y.2 p.2⟩
def mid_r (x y : A) (p : lt' x y) : lt' (mid x y p) y :=
  ⟨mid_rₑ x.1 y.1 p.1, mid_r_w x.2 y.2 p.2⟩

section
variable
  (Aₘ     : A → Type 1)
  (lt'ₘ   : ∀ {x}, Aₘ x → ∀ {y}, Aₘ y → lt' x y → Type 1)
  (ιₘ     : ∀ n, Aₘ (ι n))
  (midₘ   : ∀ {x}, (xₘ : Aₘ x) → ∀ {y}, (yₘ : Aₘ y) → ∀ {p}, (pₘ : lt'ₘ xₘ yₘ p) → Aₘ (mid x y p))
  (ι'ₘ    : ∀ m n p, lt'ₘ (ιₘ m) (ιₘ n) (ι' m n p))
  (mid_lₘ : ∀ {x}, (xₘ : Aₘ x) → ∀ {y}, (yₘ : Aₘ y) → ∀ {p}, (pₘ : lt'ₘ xₘ yₘ p)
    → lt'ₘ xₘ (midₘ xₘ yₘ pₘ) (mid_l x y p))
  (mid_rₘ : ∀ {x}, (xₘ : Aₘ x) → ∀ {y}, (yₘ : Aₘ y) → ∀ {p}, (pₘ : lt'ₘ xₘ yₘ p)
    → lt'ₘ (midₘ xₘ yₘ pₘ) yₘ (mid_r x y p))

mutual
inductive Aᵣ : (x : A) → Aₘ x → Type 1
| ιᵣ : ∀ n, Aᵣ (ι n) (ιₘ n)
| midᵣ : ∀ {x} {xₘ : Aₘ x}, Aᵣ x xₘ →
           ∀ {y} {yₘ : Aₘ y}, Aᵣ y yₘ →
             ∀ {p} {pₘ : lt'ₘ xₘ yₘ p}, lt'ᵣ xₘ yₘ p pₘ → Aᵣ (mid x y p) (midₘ xₘ yₘ pₘ)

inductive lt'ᵣ : {x : A} → (xₘ : Aₘ x) → {y : A} → (yₘ : Aₘ y) → (p : lt' x y) → lt'ₘ xₘ yₘ p → Type 1
| ι'ᵣ : ∀ m n p, lt'ᵣ (ιₘ m) (ιₘ n) (ι' m n p) (ι'ₘ m n p)
| mid_lᵣ : ∀ {x} {xₘ : Aₘ x}, Aᵣ x xₘ →
             ∀ {y} {yₘ : Aₘ y}, Aᵣ y yₘ →
               ∀ {p} {pₘ : lt'ₘ xₘ yₘ p}, lt'ᵣ xₘ yₘ p pₘ →
                 lt'ᵣ xₘ (midₘ xₘ yₘ pₘ) (mid_l x y p) (mid_lₘ xₘ yₘ pₘ)
| mid_rᵣ : ∀ {x} {xₘ : Aₘ x}, Aᵣ x xₘ →
             ∀ {y} {yₘ : Aₘ y}, Aᵣ y yₘ →
               ∀ {p} {pₘ : lt'ₘ xₘ yₘ p}, lt'ᵣ xₘ yₘ p pₘ →
                 lt'ᵣ (midₘ xₘ yₘ pₘ) yₘ (mid_r x y p) (mid_rₘ xₘ yₘ pₘ)
end

open Aᵣ lt'ᵣ

structure PSigmaUnique {α : Type _} (β : α → Type _) :=
  fst : α
  snd : β fst
  unique : ∀ {a}, β a → a = fst

noncomputable def A_tot (x : A) : PSigmaUnique (Aᵣ Aₘ lt'ₘ ιₘ midₘ ι'ₘ mid_lₘ mid_rₘ x) := by
  cases x with | mk xₑ x_w => ?_
  apply Aₑ.recOn xₑ
    (motive_1 := fun xₑ => ∀ x_w, PSigmaUnique (Aᵣ Aₘ lt'ₘ ιₘ midₘ ι'ₘ mid_lₘ mid_rₘ ⟨xₑ, x_w⟩))
    (motive_2 := fun pₑ => ∀ {x xₘ} (xᵣ : Aᵣ Aₘ lt'ₘ ιₘ midₘ ι'ₘ mid_lₘ mid_rₘ x xₘ)
                  {y yₘ} (yᵣ : Aᵣ Aₘ lt'ₘ ιₘ midₘ ι'ₘ mid_lₘ mid_rₘ y yₘ)
                   p_w, PSigmaUnique (lt'ᵣ Aₘ lt'ₘ ιₘ midₘ ι'ₘ mid_lₘ mid_rₘ xₘ yₘ ⟨pₑ, p_w⟩))
  skip
  · intro n _
    exact ⟨ιₘ n, ιᵣ n, fun {xₘ} xᵣ => by cases xᵣ; rfl⟩
  · intro x y p x_ih y_ih p_ih ctor_w
    inversion ctor_w with x_w y_w p_w
    cases x_ih x_w with | mk xₘ xᵣ x_unique => ?_
    cases y_ih y_w with | mk yₘ yᵣ y_unique => ?_
    cases p_ih xᵣ yᵣ p_w with | mk pₘ pᵣ p_unique => ?_
    exact ⟨midₘ xₘ yₘ pₘ, midᵣ xᵣ yᵣ pᵣ, fun {zₘ} zᵣ => by 
      cases zᵣ with | @midᵣ x' x'ₘ x'ᵣ y' y'ₘ y'ᵣ p' p'ₘ p'ᵣ => ?_
      cases x_unique x'ᵣ
      cases y_unique y'ᵣ
      cases p_unique p'ᵣ
      rfl ⟩
  · intro m n p x xₘ xᵣ y yₘ yᵣ ctor_w
    cases x with | mk xₑ x_w => ?_
    cases y with | mk yₑ y_w => ?_
    simp only at ctor_w
    clarifyIndices ctor_w
    cases xᵣ
    cases yᵣ
    exact ⟨ι'ₘ m n p, ι'ᵣ m n p, fun {qₘ} qᵣ => by
      cases qᵣ
      rfl ⟩
  · intro yₑ zₑ pₑ y_ih z_ih p_ih x' x'ₘ x'ᵣ y' y'ₘ y'ᵣ ctor_w
    cases x' with | mk x'ₑ x'_w => ?_
    cases y' with | mk y'ₑ y'_w => ?_
    simp only at ctor_w
    clarifyIndices ctor_w
    cases y'ᵣ with | @midᵣ x'' x''ₘ x''ᵣ y'' y''ₘ y''ᵣ p'' p''ₘ p''ᵣ => ?_
    simp only at ctor_w
    cases x'' with | mk x''ₑ x''_w => ?_
    cases y'' with | mk y''ₑ y''_w => ?_
    cases p'' with | mk p''ₑ p''_w => ?_
    clarifyIndices ctor_w
    simp only at ctor_w
    cases y_ih x''_w with | mk x'''ₘ x'''ᵣ x'''_unique => ?_
    cases z_ih y''_w with | mk y'''ₘ y'''ᵣ y'''_unique => ?_
    cases p_ih x'''ᵣ y'''ᵣ p''_w with | mk p'''ₘ p'''ᵣ p'''_unique => ?_
    simp only at *
    cases x'''_unique x'ᵣ
    cases x'''_unique x''ᵣ
    cases y'''_unique y''ᵣ
    cases p'''_unique p''ᵣ
    exact ⟨mid_lₘ _ _ _, mid_lᵣ x''ᵣ y''ᵣ p''ᵣ, fun {qₘ} qᵣ => by
      match qᵣ with
      | mid_lᵣ x'''ᵣ y'''ᵣ p'''ᵣ => skip ⟩
  
    
noncomputable def Ty_tot (Γ : Con) (A : Ty Γ) :
  PSigma (Tyᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ (Con_tot Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ).1 A) := by
  cases Γ with | mk Γₑ Γ_w => ?_
  cases A with | mk Aₑ A_w => ?_
  apply Tyₑ.recOn Aₑ
    (motive_1 := fun Γₑ => ∀ Γ_w, PSigma (Conᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ ⟨Γₑ, Γ_w⟩))
    (motive_2 := fun Aₑ => ∀ {Γ Γₘ} (Γᵣ : Conᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ Γₘ)
                   A_w, PSigma (Tyᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γₘ ⟨Aₑ, A_w⟩))
  · intro Γ_w
    exact PSigma.mk nilₘ nilᵣ
  · intro Δₑ Aₑ Δ_ih A_ih ctor_w
    inversion ctor_w with Δ_w A_w
    cases Δ_ih Δ_w with | mk Δₘ Δᵣ => ?_
    cases A_ih Δᵣ A_w with | mk Aₘ Aᵣ => ?_
    exact PSigma.mk (extₘ Δₘ Aₘ) (extᵣ Δᵣ Aᵣ)
  · intro Γₑ Γ_ih Δ Δₘ Δᵣ ctor_w
    cases Δ with | mk Δₑ Δ_w => ?_
    simp only at ctor_w
    clarifyIndices ctor_w
    exact PSigma.mk (baseₘ Δₘ) (baseᵣ Δᵣ)
  · intro Δₑ Aₑ Bₑ Δ_ih A_ih B_ih Δ' Δ'ₘ Δ'ᵣ ctor_w
    cases Δ' with | mk Δ'ₑ Δ_w => ?_
    simp only at ctor_w
    clarifyIndices ctor_w
    inversion ctor_w with Δ_w A_w B_w
    cases A_ih Δ'ᵣ A_w with | mk Aₘ Aᵣ => ?_
    cases B_ih (extᵣ Δ'ᵣ Aᵣ) B_w with | mk Bₘ Bᵣ => ?_ 
    exact PSigma.mk (piₘ Δ'ₘ Aₘ Bₘ) (piᵣ Δ'ᵣ Aᵣ Bᵣ)
  · exact (Con_tot Conₘ Tyₘ nilₘ extₘ baseₘ piₘ ⟨Γₑ, Γ_w⟩).2

noncomputable def Con.rec (Γ : Con) : Conₘ Γ :=
(Con_tot Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ).1

noncomputable def Ty.rec (Γ : Con) (A : Ty Γ) : Tyₘ (Con.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ) A :=
(Ty_tot Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ A).1

theorem nil_beta : Con.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ nil = nilₘ :=
rfl

theorem ext_beta (Γ : Con) (A : Ty Γ) :
  Con.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ (ext Γ A) 
  = extₘ (Con.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ)
    (Ty.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ A) :=
rfl

theorem base_beta (Γ : Con) :
  Ty.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ (base Γ)
  = baseₘ (Con.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ) :=
rfl

theorem pi_beta (Γ : Con) (A : Ty Γ) (B : Ty (ext Γ A)) :
  Ty.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ (pi Γ A B)
  = piₘ (Con.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ)
      (Ty.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ A)
      (Ty.rec Conₘ Tyₘ nilₘ extₘ baseₘ piₘ (ext Γ A) B) :=
rfl

end