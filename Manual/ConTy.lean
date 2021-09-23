import IIT.PropInversion
import IIT.ClarifyIndices

mutual
inductive Conₑ : Type
| nilₑ : Conₑ
| extₑ : Conₑ → Tyₑ → Conₑ


inductive Tyₑ : Type
| baseₑ : Conₑ → Tyₑ
| piₑ   : Conₑ → Tyₑ → Tyₑ → Tyₑ
end

open Conₑ Tyₑ

mutual
inductive Con_w : Conₑ → Prop
| nil_w : Con_w nilₑ
| ext_w : ∀ {Γ}, Con_w Γ → ∀ {A}, Ty_w Γ A → Con_w (extₑ Γ A)

inductive Ty_w : Conₑ → Tyₑ → Prop
| base_w : ∀ {Γ}, Con_w Γ → Ty_w Γ (baseₑ Γ)
| pi_w : ∀ {Γ}, Con_w Γ → ∀ {A}, Ty_w Γ A → ∀ {B}, Ty_w (extₑ Γ A) B → Ty_w Γ (piₑ Γ A B)
end

open Con_w Ty_w

def Con := PSigma Con_w
def Ty := fun (Γ : Con) => PSigma (Ty_w Γ.1)

def nil : Con                                         := ⟨nilₑ,            nil_w⟩
def ext (Γ : Con) (A : Ty Γ) : Con                    := ⟨extₑ Γ.1 A.1,    ext_w Γ.2 A.2⟩ 
def base (Γ : Con) : Ty Γ                             := ⟨baseₑ Γ.1,       base_w Γ.2⟩
def pi (Γ : Con) (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ := ⟨piₑ Γ.1 A.1 B.1, pi_w Γ.2 A.2 B.2⟩ 

section
variable
  (Conₘ  : Con → Sort _)
  (Tyₘ   : ∀ {Γ}, Conₘ Γ → Ty Γ → Sort)
  (nilₘ  : Conₘ nil)
  (extₘ  : ∀ {Γ} (Γₘ : Conₘ Γ) {A}, Tyₘ Γₘ A → Conₘ (ext Γ A))
  (baseₘ : ∀ {Γ} (Γₘ : Conₘ Γ), Tyₘ Γₘ (base Γ))
  (piₘ   : ∀ {Γ} (Γₘ : Conₘ Γ) {A} (Aₘ : Tyₘ Γₘ A) {B} (Bₘ : Tyₘ (extₘ Γₘ Aₘ) B), Tyₘ Γₘ (pi Γ A B))

mutual
inductive Conᵣ : (Γ : Con) → Conₘ Γ → Prop
| nilᵣ : Conᵣ nil nilₘ
| extᵣ : ∀ {Γ} {Γₘ : Conₘ Γ}, Conᵣ Γ Γₘ →
           ∀ {A} {Aₘ : Tyₘ Γₘ A}, Tyᵣ Γₘ A Aₘ → Conᵣ (ext Γ A) (extₘ Γₘ Aₘ)

inductive Tyᵣ : {Γ : Con} → (Γₘ : Conₘ Γ) → (A : Ty Γ) → Tyₘ Γₘ A → Prop
| baseᵣ: ∀ {Γ} {Γₘ : Conₘ Γ}, Conᵣ Γ Γₘ → Tyᵣ Γₘ (base Γ) (baseₘ Γₘ)
| piᵣ: ∀ {Γ} {Γₘ : Conₘ Γ}, Conᵣ Γ Γₘ →
         ∀ {A} {Aₘ : Tyₘ Γₘ A}, Tyᵣ Γₘ A Aₘ →
           ∀ {B} {Bₘ : Tyₘ (extₘ Γₘ Aₘ) B}, Tyᵣ (extₘ Γₘ Aₘ) B Bₘ →
             Tyᵣ Γₘ (pi Γ A B) (piₘ Γₘ Aₘ Bₘ)
end

open Conᵣ Tyᵣ

theorem Con_tot (Γ : Con) : PSigma (Conᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ) := by
  cases Γ with | mk Γₑ Γ_w => ? _
  apply Conₑ.recOn Γₑ 
    (motive_1 := fun Γₑ => ∀ Γ_w, PSigma (Conᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ ⟨Γₑ, Γ_w⟩))
    (motive_2 := fun Aₑ => ∀ {Γ Γₘ} (Γᵣ : Conᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γ Γₘ)
                   A_w, PSigma (Tyᵣ Conₘ Tyₘ nilₘ extₘ baseₘ piₘ Γₘ ⟨Aₑ, A_w⟩))
  · intro Γ_w
    exact PSigma.mk nilₘ nilᵣ
  · intro Δₑ Aₑ Δ_ih A_ih ctor_w
    inversion ctor_w with Δ_w A_w
    refine PSigma.mk ?_ ?_
    · apply extₘ (Δ_ih Δ_w).1 (A_ih (Δ_ih Δ_w).2 A_w).1
    · apply extᵣ (Δ_ih Δ_w).2 (A_ih (Δ_ih Δ_w).2 A_w).2
  · intro Γₑ Γ_ih Δ Δₘ Δᵣ ctor_w
    cases Δ with | mk Δₑ Δ_w => ?_
    simp only at ctor_w
    clarifyIndices ctor_w
    refine PSigma.mk ?_ ?_
    · apply baseₘ
    · apply baseᵣ
      assumption
  · intro Δₑ Aₑ Bₑ Δ_ih A_ih B_ih Δ' Δ'ₘ Δ'ᵣ ctor_w
    cases Δ' with | mk Δ'ₑ Δ_w => ?_
    simp only at ctor_w
    clarifyIndices ctor_w
    inversion ctor_w with Δ_w A_w B_w
    apply PSigma.mk
    simp_all
    apply piᵣ Δ'ᵣ (A_ih _ _).2 (B_ih _ _).2
    repeat assumption
    apply extᵣ
    assumption
    apply (A_ih _ _).2
    assumption

end