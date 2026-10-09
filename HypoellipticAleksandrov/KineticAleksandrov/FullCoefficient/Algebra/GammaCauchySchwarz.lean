module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.FlowOperator
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Cauchy-Schwarz for the flow gradient form

This is the step in the flow identities that minimizes the quadratic
form in `N^{1/2} Dr`. Since `Mform` is a nonnegative quadratic form, its polar form
`flowGamma` satisfies `Γ(F,G)² ≤ Γ(F,F) Γ(G,G)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

private theorem vecDot_add_smul (a c b e : PDE.Vec d) (t : ℝ) :
    PDE.vecDot (a + t • c) (b + t • e)
      = PDE.vecDot a b + t * PDE.vecDot a e + t * PDE.vecDot c b + t ^ 2 * PDE.vecDot c e := by
  simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Polar expansion of `Mform` along a line. -/
theorem Mform_add_smul (lam h : ℝ) (a b c e : PDE.Vec d) (t : ℝ) :
    Mform lam h (a + t • c) (b + t • e)
      = Mform lam h a b
        + 2 * t * (lam / 2 * (2 * h ^ 2 * PDE.vecDot a c
            - h * (PDE.vecDot a e + PDE.vecDot c b) + PDE.vecDot b e))
        + t ^ 2 * Mform lam h c e := by
  unfold Mform
  rw [vecDot_add_smul, vecDot_add_smul, vecDot_add_smul]
  have h1 : PDE.vecDot c a = PDE.vecDot a c := PDE.vecDot_comm _ _
  have h2 : PDE.vecDot e b = PDE.vecDot b e := PDE.vecDot_comm _ _
  rw [h1, h2]
  ring

/-- Cauchy-Schwarz for the gradient form. -/
theorem flowGamma_sq_le {lam h : ℝ} (hlam : 0 < lam) (F G : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) :
    flowGamma lam h F G y ^ 2 ≤ flowGamma lam h F F y * flowGamma lam h G G y := by
  set a : PDE.Vec d := fun i => positionPartial i F y
  set b : PDE.Vec d := fun i => velocityPartial i F y
  set c : PDE.Vec d := fun i => positionPartial i G y
  set e : PDE.Vec d := fun i => velocityPartial i G y
  have hGam : flowGamma lam h F G y
      = lam / 2 * (2 * h ^ 2 * PDE.vecDot a c - h * (PDE.vecDot a e + PDE.vecDot c b)
          + PDE.vecDot b e) := by
    simp only [flowGamma, gradZZ, gradZV, gradVV, PDE.vecDot, a, b, c, e]
  have hFF : flowGamma lam h F F y = Mform lam h a b := flowGamma_self lam h F y
  have hGG : flowGamma lam h G G y = Mform lam h c e := flowGamma_self lam h G y
  have hnn : ∀ t : ℝ, 0 ≤ Mform lam h c e * (t * t) + 2 * flowGamma lam h F G y * t
      + Mform lam h a b := by
    intro t
    have := Mform_ge (h := h) hlam (a + t • c) (b + t • e)
    have h0 : 0 ≤ PDE.vecDot (b + t • e) (b + t • e) := PDE.vecNormSq_nonneg _
    have hexp := Mform_add_smul lam h a b c e t
    rw [← hGam] at hexp
    nlinarith
  have := discrim_le_zero hnn
  unfold discrim at this
  rw [hFF, hGG]
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
