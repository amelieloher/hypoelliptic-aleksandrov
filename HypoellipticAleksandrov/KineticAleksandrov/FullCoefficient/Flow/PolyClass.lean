module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.SecondOrder

/-!
# Polynomially growing coefficient families

For the Gaussian exponential `G_θ = gaussExp θ₁ θ₂ θ₃` every iterated coordinate derivative has
the form `P_θ * G_θ` where `P_θ` is a polynomial of degree at most the order. To obtain bounds
that are uniform in the coefficient triple `θ` (on bounded sets, hence on compact `h`-intervals
for the flow), we track a family `θ ↦ P_θ` in the predicate `PG k S`: degree `≤ k`, with growth
constant uniform over `Coef S = {θ | |θᵢ| ≤ S}`. This realizes the polynomial structure behind the
derivative bounds of the Gaussian flow.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The parameter triple `(a, b, c)` of the quadratic form. -/
abbrev Theta : Type := ℝ × ℝ × ℝ

/-- The coefficient triples bounded by `S`. -/
def Coef (S : ℝ) : Set Theta := {θ | |θ.1| ≤ S ∧ |θ.2.1| ≤ S ∧ |θ.2.2| ≤ S}

/-- The gradient `∂_δ Q_θ` of the quadratic form, as a function of the triple. -/
def genT (θ : Theta) (δ : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) : ℝ :=
  gen θ.1 θ.2.1 θ.2.2 δ y

/-- The constant second derivatives `∂_δ' ∂_δ Q_θ`, as a function of the triple. -/
def genCoeffT (θ : Theta) (δ δ' : Fin d ⊕ Fin d) : ℝ := genCoeff θ.1 θ.2.1 θ.2.2 δ δ'

/-- The Gaussian exponential as a function of the triple. -/
def gaussExpT (θ : Theta) (y : EvolutionAmbientState d) : ℝ := gaussExp θ.1 θ.2.1 θ.2.2 y

/-- Families of functions of polynomial growth of degree `≤ k`, uniformly over `Coef S`:
degree `0` means constant, and degree `k + 1` means differentiable, with growth
`C (1 + ‖y‖)^(k+1)` and all coordinate derivatives of degree `≤ k`. -/
def PG : ℕ → ℝ → (Theta → EvolutionAmbientState d → ℝ) → Prop
  | 0, S, p => ∃ C : ℝ, ∀ θ ∈ Coef S, ∃ c : ℝ, |c| ≤ C ∧ p θ = fun _ => c
  | k + 1, S, p =>
      (∃ C : ℝ, ∀ θ ∈ Coef S, ∀ y, |p θ y| ≤ C * (1 + ‖y‖) ^ (k + 1)) ∧
      (∀ θ ∈ Coef S, Differentiable ℝ (p θ)) ∧
      ∀ δ, PG k S (fun θ => dirPartial δ (p θ))

theorem Coef.nonneg {S : ℝ} {θ : Theta} (hθ : θ ∈ Coef S) : 0 ≤ S :=
  (abs_nonneg _).trans hθ.1

theorem PG.congr : ∀ (k : ℕ) {S : ℝ} {p q : Theta → EvolutionAmbientState d → ℝ},
    PG k S p → (∀ θ ∈ Coef S, p θ = q θ) → PG k S q
  | 0, S, p, q, hp, he => by
      obtain ⟨C, hC⟩ := hp
      refine ⟨C, fun θ hθ => ?_⟩
      obtain ⟨c, hc, e⟩ := hC θ hθ
      exact ⟨c, hc, (he θ hθ).symm.trans e⟩
  | k + 1, S, p, q, hp, he => by
      obtain ⟨⟨C, hb⟩, hd, hpart⟩ := hp
      refine ⟨⟨C, fun θ hθ y => ?_⟩, fun θ hθ => ?_, fun δ => ?_⟩
      · rw [← he θ hθ]; exact hb θ hθ y
      · rw [← he θ hθ]; exact hd θ hθ
      · refine PG.congr k (hpart δ) fun θ hθ => ?_
        rw [he θ hθ]

theorem PG.zero (S : ℝ) :
    ∀ k : ℕ, PG k S (fun (_ : Theta) (_ : EvolutionAmbientState d) => (0 : ℝ))
  | 0 => ⟨0, fun θ _ => ⟨0, by simp, rfl⟩⟩
  | k + 1 => by
      refine ⟨⟨0, fun θ _ y => by simp⟩, fun θ _ => differentiable_const _, fun δ => ?_⟩
      refine (PG.zero S k).congr k fun θ _ => ?_
      funext y
      exact (dirPartial_const δ 0 y).symm

theorem PG.mono : ∀ (k : ℕ) {S : ℝ} {p : Theta → EvolutionAmbientState d → ℝ},
    PG k S p → PG (k + 1) S p
  | 0, S, p, hp => by
      obtain ⟨C, hC⟩ := hp
      refine ⟨⟨C, fun θ hθ y => ?_⟩, fun θ hθ => ?_, fun δ => ?_⟩
      · obtain ⟨c, hc, e⟩ := hC θ hθ
        rw [e]
        have : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
        have hC0 : 0 ≤ C := (abs_nonneg c).trans hc
        calc |c| ≤ C := hc
          _ ≤ C * (1 + ‖y‖) ^ (0 + 1) := by
            simpa using mul_le_mul_of_nonneg_left this hC0
      · obtain ⟨c, hc, e⟩ := hC θ hθ
        rw [e]; exact differentiable_const _
      · refine ⟨0, fun θ hθ => ⟨0, by simp, ?_⟩⟩
        obtain ⟨c, hc, e⟩ := hC θ hθ
        funext y
        show dirPartial δ (p θ) y = 0
        rw [e]; exact dirPartial_const δ c y
  | k + 1, S, p, hp => by
      obtain ⟨⟨C, hb⟩, hd, hpart⟩ := hp
      refine ⟨⟨C, fun θ hθ y => ?_⟩, hd, fun δ => PG.mono k (hpart δ)⟩
      refine (hb θ hθ y).trans ?_
      have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have hC0 : 0 ≤ C := by
        have := (abs_nonneg (p θ y)).trans (hb θ hθ y)
        have hp1 : 0 < (1 + ‖y‖) ^ (k + 1) := by positivity
        exact nonneg_of_mul_nonneg_left this hp1
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (Nat.le_succ _)) hC0

theorem PG.partial_succ (δ : Fin d ⊕ Fin d) : ∀ (k : ℕ) {S : ℝ}
    {p : Theta → EvolutionAmbientState d → ℝ},
    PG k S p → PG (k + 1) S (fun θ => dirPartial δ (p θ))
  | 0, S, p, hp => by
      obtain ⟨C, hC⟩ := hp
      refine (PG.zero S 1).congr 1 fun θ hθ => ?_
      obtain ⟨c, hc, e⟩ := hC θ hθ
      funext y
      rw [e]; exact (dirPartial_const δ c y).symm
  | k + 1, S, p, hp => PG.mono (k + 1) (PG.mono k (hp.2.2 δ))

theorem dirPartial_add' (δ : Fin d ⊕ Fin d) {p q : EvolutionAmbientState d → ℝ}
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (y : EvolutionAmbientState d) :
    dirPartial δ (fun y => p y + q y) y = dirPartial δ p y + dirPartial δ q y := by
  unfold dirPartial
  rw [fderiv_fun_add (hp y) (hq y)]
  rfl

theorem dirPartial_const_mul' (δ : Fin d ⊕ Fin d) (c : ℝ) {p : EvolutionAmbientState d → ℝ}
    (hp : Differentiable ℝ p) (y : EvolutionAmbientState d) :
    dirPartial δ (fun y => c * p y) y = c * dirPartial δ p y := by
  unfold dirPartial
  rw [fderiv_const_mul (hp y)]
  rfl

theorem PG.add : ∀ (k : ℕ) {S : ℝ} {p q : Theta → EvolutionAmbientState d → ℝ},
    PG k S p → PG k S q → PG k S (fun θ y => p θ y + q θ y)
  | 0, S, p, q, hp, hq => by
      obtain ⟨C₁, h₁⟩ := hp
      obtain ⟨C₂, h₂⟩ := hq
      refine ⟨C₁ + C₂, fun θ hθ => ?_⟩
      obtain ⟨c₁, hc₁, e₁⟩ := h₁ θ hθ
      obtain ⟨c₂, hc₂, e₂⟩ := h₂ θ hθ
      refine ⟨c₁ + c₂, (abs_add_le _ _).trans (add_le_add hc₁ hc₂), ?_⟩
      funext y
      simp [e₁, e₂]
  | k + 1, S, p, q, hp, hq => by
      obtain ⟨⟨C₁, hb₁⟩, hd₁, hpart₁⟩ := hp
      obtain ⟨⟨C₂, hb₂⟩, hd₂, hpart₂⟩ := hq
      refine ⟨⟨C₁ + C₂, fun θ hθ y => ?_⟩, fun θ hθ => (hd₁ θ hθ).add (hd₂ θ hθ), fun δ => ?_⟩
      · calc |p θ y + q θ y| ≤ |p θ y| + |q θ y| := abs_add_le _ _
          _ ≤ C₁ * (1 + ‖y‖) ^ (k + 1) + C₂ * (1 + ‖y‖) ^ (k + 1) :=
            add_le_add (hb₁ θ hθ y) (hb₂ θ hθ y)
          _ = (C₁ + C₂) * (1 + ‖y‖) ^ (k + 1) := by ring
      · refine (PG.add k (hpart₁ δ) (hpart₂ δ)).congr k fun θ hθ => ?_
        funext y
        exact (dirPartial_add' δ (hd₁ θ hθ) (hd₂ θ hθ) y).symm

theorem PG.const_mul : ∀ (k : ℕ) {S : ℝ} {p : Theta → EvolutionAmbientState d → ℝ}
    {c : Theta → ℝ} {M : ℝ}, (∀ θ ∈ Coef S, |c θ| ≤ M) →
    PG k S p → PG k S (fun θ y => c θ * p θ y)
  | 0, S, p, c, M, hc, hp => by
      obtain ⟨C, hC⟩ := hp
      refine ⟨M * C, fun θ hθ => ?_⟩
      obtain ⟨c₀, hc₀, e⟩ := hC θ hθ
      refine ⟨c θ * c₀, ?_, ?_⟩
      · rw [abs_mul]
        exact mul_le_mul (hc θ hθ) hc₀ (abs_nonneg _) ((abs_nonneg _).trans (hc θ hθ))
      · funext y; simp [e]
  | k + 1, S, p, c, M, hc, hp => by
      obtain ⟨⟨C, hb⟩, hd, hpart⟩ := hp
      refine ⟨⟨M * C, fun θ hθ y => ?_⟩, fun θ hθ => (hd θ hθ).const_mul (c θ), fun δ => ?_⟩
      · rw [abs_mul, mul_assoc]
        have h1 := hb θ hθ y
        have hM : 0 ≤ M := (abs_nonneg _).trans (hc θ hθ)
        exact mul_le_mul (hc θ hθ) h1 (abs_nonneg _) hM
      · refine (PG.const_mul k hc (hpart δ)).congr k fun θ hθ => ?_
        funext y
        exact (dirPartial_const_mul' δ (c θ) (hd θ hθ) y).symm

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
