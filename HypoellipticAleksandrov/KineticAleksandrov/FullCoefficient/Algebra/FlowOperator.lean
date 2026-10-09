module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.Leibniz
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.Coercive

/-!
# The flow operator `M^h : D²` and its carré du champ

The flow identities (calculus input). The operator is
`flowL lam h F = (lam/2)(2h² Δ_z F - 2h ∇_z·∇_v F + Δ_v F)`, and `flowGamma lam h F G` is the
associated symmetric bilinear gradient form, with `flowGamma lam h F F = Mform lam h ∇_zF ∇_vF`.
The Leibniz and chain rules for `flowL` are proved for `C²` functions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The covariance operator `M^h : D² F = (lam/2)(2h² Δ_z - 2h ∇_z·∇_v + Δ_v) F`. -/
def flowL (lam h : ℝ) (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  lam / 2 * (2 * h ^ 2 * positionLaplacian F y - 2 * h * mixedDivergence F y
    + velocityLaplacian F y)

/-- The pairing `∇_z F · ∇_z G`. -/
def gradZZ (F G : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i F y * positionPartial i G y

/-- The pairing `∇_z F · ∇_v G`. -/
def gradZV (F G : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i F y * velocityPartial i G y

/-- The pairing `∇_v F · ∇_v G`. -/
def gradVV (F G : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, velocityPartial i F y * velocityPartial i G y

/-- The symmetric gradient form `Γ_M(F, G)` of the operator `M^h : D²`. -/
def flowGamma (lam h : ℝ) (F G : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    ℝ :=
  lam / 2 * (2 * h ^ 2 * gradZZ F G y - h * (gradZV F G y + gradZV G F y) + gradVV F G y)

/-- The gradient of `F` has `M^h`-norm `flowGamma lam h F F`. -/
theorem flowGamma_self (lam h : ℝ) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    flowGamma lam h F F y
      = Mform lam h (fun i => positionPartial i F y) (fun i => velocityPartial i F y) := by
  simp only [flowGamma, Mform, gradZZ, gradZV, gradVV, PDE.vecDot]
  ring

/-- Symmetry of the gradient form. -/
theorem flowGamma_comm (lam h : ℝ) (F G : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : flowGamma lam h F G y = flowGamma lam h G F y := by
  have h1 : gradZZ F G y = gradZZ G F y := Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : gradVV F G y = gradVV G F y := Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold flowGamma
  rw [h1, h2]
  ring

/-- The gradient form is nonnegative on the diagonal. -/
theorem flowGamma_self_nonneg {lam h : ℝ} (hlam : 0 < lam) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : 0 ≤ flowGamma lam h F F y := by
  rw [flowGamma_self]
  have := Mform_ge (h := h) hlam (fun i => positionPartial i F y) (fun i => velocityPartial i F y)
  have h0 : 0 ≤ PDE.vecDot (fun i => velocityPartial i F y) (fun i => velocityPartial i F y) :=
    PDE.vecNormSq_nonneg _
  nlinarith

/-- A scalar function of the gradients: pointwise first-order data of a product. -/
theorem fderiv_mul_apply {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (a y : EvolutionAmbientState d) :
    fderiv ℝ (fun y => F y * G y) y a
      = F y * fderiv ℝ G y a + G y * fderiv ℝ F y a :=
  congrFun (fderiv_dir_mul hF hG a) y

/-- Pointwise first-order chain rule. -/
theorem fderiv_comp_apply {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y')) (a y : EvolutionAmbientState d) :
    fderiv ℝ (fun y => φ (F y)) y a = φ' (F y) * fderiv ℝ F y a :=
  congrFun (fderiv_dir_comp hF hφ a) y

private theorem position_dirSecond (i j : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    positionPartial i (positionPartial j F) y
      = dirSecond F (0, Pi.single j 1) (0, Pi.single i 1) y :=
  rfl

private theorem velocity_dirSecond (i j : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    velocityPartial i (velocityPartial j F) y
      = dirSecond F (Pi.single j 1, 0) (Pi.single i 1, 0) y :=
  rfl

private theorem mixed_dirSecond (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    positionPartial i (velocityPartial i F) y
      = dirSecond F (Pi.single i 1, 0) (0, Pi.single i 1) y :=
  rfl

/-- Leibniz rule for the position Laplacian. -/
theorem positionLaplacian_mul {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (y : EvolutionAmbientState d) :
    positionLaplacian (fun y => F y * G y) y
      = F y * positionLaplacian G y + G y * positionLaplacian F y + 2 * gradZZ F G y := by
  have key : ∀ i, positionPartial i (positionPartial i (fun y => F y * G y)) y
      = F y * positionPartial i (positionPartial i G) y
        + G y * positionPartial i (positionPartial i F) y
        + 2 * (positionPartial i F y * positionPartial i G y) := by
    intro i
    rw [position_dirSecond, dirSecond_mul hF hG, position_dirSecond, position_dirSecond]
    simp only [positionPartial]
    ring
  unfold positionLaplacian gradZZ
  simp only [key, Finset.sum_add_distrib, Finset.mul_sum]

/-- Leibniz rule for the velocity Laplacian. -/
theorem velocityLaplacian_mul {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (y : EvolutionAmbientState d) :
    velocityLaplacian (fun y => F y * G y) y
      = F y * velocityLaplacian G y + G y * velocityLaplacian F y + 2 * gradVV F G y := by
  have key : ∀ i, velocityPartial i (velocityPartial i (fun y => F y * G y)) y
      = F y * velocityPartial i (velocityPartial i G) y
        + G y * velocityPartial i (velocityPartial i F) y
        + 2 * (velocityPartial i F y * velocityPartial i G y) := by
    intro i
    rw [velocity_dirSecond, dirSecond_mul hF hG, velocity_dirSecond, velocity_dirSecond]
    simp only [velocityPartial]
    ring
  unfold velocityLaplacian gradVV
  simp only [key, Finset.sum_add_distrib, Finset.mul_sum]

/-- Leibniz rule for the mixed operator. -/
theorem mixedDivergence_mul {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (y : EvolutionAmbientState d) :
    mixedDivergence (fun y => F y * G y) y
      = F y * mixedDivergence G y + G y * mixedDivergence F y
        + gradZV F G y + gradZV G F y := by
  have key : ∀ i, positionPartial i (velocityPartial i (fun y => F y * G y)) y
      = F y * positionPartial i (velocityPartial i G) y
        + G y * positionPartial i (velocityPartial i F) y
        + positionPartial i F y * velocityPartial i G y
        + positionPartial i G y * velocityPartial i F y := by
    intro i
    rw [mixed_dirSecond, dirSecond_mul hF hG, mixed_dirSecond, mixed_dirSecond]
    simp only [positionPartial, velocityPartial]
    ring
  unfold mixedDivergence gradZV
  simp only [key, Finset.sum_add_distrib, Finset.mul_sum]

/-- Leibniz rule for `M^h : D²`. -/
theorem flowL_mul {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) (lam h : ℝ) (y : EvolutionAmbientState d) :
    flowL lam h (fun y => F y * G y) y
      = F y * flowL lam h G y + G y * flowL lam h F y + 2 * flowGamma lam h F G y := by
  unfold flowL flowGamma
  rw [positionLaplacian_mul hF hG, velocityLaplacian_mul hF hG, mixedDivergence_mul hF hG]
  ring

/-- Chain rule for the position Laplacian. -/
theorem positionLaplacian_comp {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y'))
    (y : EvolutionAmbientState d) (hφ' : HasDerivAt φ' (φ'' (F y)) (F y)) :
    positionLaplacian (fun y => φ (F y)) y
      = φ' (F y) * positionLaplacian F y + φ'' (F y) * gradZZ F F y := by
  have key : ∀ i, positionPartial i (positionPartial i (fun y => φ (F y))) y
      = φ' (F y) * positionPartial i (positionPartial i F) y
        + φ'' (F y) * (positionPartial i F y * positionPartial i F y) := by
    intro i
    rw [position_dirSecond, dirSecond_comp hF hφ y hφ', position_dirSecond]
    rfl
  unfold positionLaplacian gradZZ
  simp only [key, Finset.sum_add_distrib, Finset.mul_sum]

/-- Chain rule for the velocity Laplacian. -/
theorem velocityLaplacian_comp {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y'))
    (y : EvolutionAmbientState d) (hφ' : HasDerivAt φ' (φ'' (F y)) (F y)) :
    velocityLaplacian (fun y => φ (F y)) y
      = φ' (F y) * velocityLaplacian F y + φ'' (F y) * gradVV F F y := by
  have key : ∀ i, velocityPartial i (velocityPartial i (fun y => φ (F y))) y
      = φ' (F y) * velocityPartial i (velocityPartial i F) y
        + φ'' (F y) * (velocityPartial i F y * velocityPartial i F y) := by
    intro i
    rw [velocity_dirSecond, dirSecond_comp hF hφ y hφ', velocity_dirSecond]
    rfl
  unfold velocityLaplacian gradVV
  simp only [key, Finset.sum_add_distrib, Finset.mul_sum]

/-- Chain rule for the mixed operator. -/
theorem mixedDivergence_comp {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y'))
    (y : EvolutionAmbientState d) (hφ' : HasDerivAt φ' (φ'' (F y)) (F y)) :
    mixedDivergence (fun y => φ (F y)) y
      = φ' (F y) * mixedDivergence F y + φ'' (F y) * gradZV F F y := by
  have key : ∀ i, positionPartial i (velocityPartial i (fun y => φ (F y))) y
      = φ' (F y) * positionPartial i (velocityPartial i F) y
        + φ'' (F y) * (positionPartial i F y * velocityPartial i F y) := by
    intro i
    rw [mixed_dirSecond, dirSecond_comp hF hφ y hφ', mixed_dirSecond]
    rfl
  unfold mixedDivergence gradZV
  simp only [key, Finset.sum_add_distrib, Finset.mul_sum]

/-- Chain rule for `M^h : D²`. -/
theorem flowL_comp {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' φ'' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y'))
    (y : EvolutionAmbientState d) (hφ' : HasDerivAt φ' (φ'' (F y)) (F y)) (lam h : ℝ) :
    flowL lam h (fun y => φ (F y)) y
      = φ' (F y) * flowL lam h F y + φ'' (F y) * flowGamma lam h F F y := by
  unfold flowL flowGamma
  rw [positionLaplacian_comp hF hφ y hφ', velocityLaplacian_comp hF hφ y hφ',
    mixedDivergence_comp hF hφ y hφ']
  ring

/-- The gradient form of a chain composite in the left slot. -/
theorem flowGamma_comp_left {F G : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ 2 F)
    {φ φ' : ℝ → ℝ} (hφ : ∀ y', HasDerivAt φ (φ' (F y')) (F y')) (lam h : ℝ)
    (y : EvolutionAmbientState d) :
    flowGamma lam h (fun y => φ (F y)) G y = φ' (F y) * flowGamma lam h F G y := by
  have hp : ∀ i, positionPartial i (fun y => φ (F y)) y = φ' (F y) * positionPartial i F y :=
    fun i => fderiv_comp_apply hF hφ _ y
  have hv : ∀ i, velocityPartial i (fun y => φ (F y)) y = φ' (F y) * velocityPartial i F y :=
    fun i => fderiv_comp_apply hF hφ _ y
  have e1 : gradZZ (fun y => φ (F y)) G y = φ' (F y) * gradZZ F G y := by
    unfold gradZZ; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hp]; ring
  have e2 : gradZV (fun y => φ (F y)) G y = φ' (F y) * gradZV F G y := by
    unfold gradZV; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hp]; ring
  have e3 : gradZV G (fun y => φ (F y)) y = φ' (F y) * gradZV G F y := by
    unfold gradZV; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hv]; ring
  have e4 : gradVV (fun y => φ (F y)) G y = φ' (F y) * gradVV F G y := by
    unfold gradVV; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hv]; ring
  unfold flowGamma
  rw [e1, e2, e3, e4]
  ring

/-- The gradient form against a product in the right slot. -/
theorem flowGamma_mul_right {F G H : EvolutionAmbientState d → ℝ} (hG : ContDiff ℝ 2 G)
    (hH : ContDiff ℝ 2 H) (lam h : ℝ) (y : EvolutionAmbientState d) :
    flowGamma lam h F (fun y => G y * H y) y
      = G y * flowGamma lam h F H y + H y * flowGamma lam h F G y := by
  have hp : ∀ i, positionPartial i (fun y => G y * H y) y
      = G y * positionPartial i H y + H y * positionPartial i G y :=
    fun i => fderiv_mul_apply hG hH _ y
  have hv : ∀ i, velocityPartial i (fun y => G y * H y) y
      = G y * velocityPartial i H y + H y * velocityPartial i G y :=
    fun i => fderiv_mul_apply hG hH _ y
  have e1 : gradZZ F (fun y => G y * H y) y = G y * gradZZ F H y + H y * gradZZ F G y := by
    unfold gradZZ; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hp]; ring
  have e2 : gradZV F (fun y => G y * H y) y = G y * gradZV F H y + H y * gradZV F G y := by
    unfold gradZV; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hv]; ring
  have e3 : gradZV (fun y => G y * H y) F y = G y * gradZV H F y + H y * gradZV G F y := by
    unfold gradZV; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hp]; ring
  have e4 : gradVV F (fun y => G y * H y) y = G y * gradVV F H y + H y * gradVV F G y := by
    unfold gradVV; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hv]; ring
  unfold flowGamma
  rw [e1, e2, e3, e4]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
