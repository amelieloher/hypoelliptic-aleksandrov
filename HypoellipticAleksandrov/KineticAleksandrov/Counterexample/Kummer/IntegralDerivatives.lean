module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
# Derivatives of the positive Kummer integral

Exponential domination at half the Laplace parameter permits differentiation under
the integral. Parameter shifts preserve the translated-power factor exactly.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Multiplication by the integration variable shifts both shape parameters. -/
theorem laplaceKernelReal_shift (a b z t : ℝ) (ht : 0 < t) :
    laplaceKernelReal (a + 1) (b + 1) z t = t * laplaceKernelReal a b z t := by
  simp only [laplaceKernelReal]
  rw [show a + 1 - 1 = (a - 1) + 1 by ring,
    show b + 1 - (a + 1) - 1 = b - a - 1 by ring, Real.rpow_add_one ht.ne']
  ring

/-- The kernel decreases when the positive Laplace parameter increases. -/
theorem laplaceKernelReal_antitone (a b t : ℝ) (ht : 0 < t)
    (z w : ℝ) (hzw : z ≤ w) :
    laplaceKernelReal a b w t ≤ laplaceKernelReal a b z t := by
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_right hzw ht.le)
    · exact Real.rpow_nonneg ht.le _
  · exact Real.rpow_nonneg (by linarith only [ht]) _

/-- The first argument derivative is the negative shifted kernel. -/
theorem hasDerivAt_laplaceKernelReal (a b z t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun w => laplaceKernelReal a b w t)
      (-laplaceKernelReal (a + 1) (b + 1) z t) z := by
  have he := (((hasDerivAt_id z).mul_const t).neg.exp.mul_const
    (t ^ (a - 1))).mul_const ((1 + t) ^ (b - a - 1))
  have heq : -laplaceKernelReal (a + 1) (b + 1) z t =
      Real.exp (-(z * t)) * -(1 * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1) := by
    rw [laplaceKernelReal_shift a b z t ht]
    simp only [laplaceKernelReal]
    ring
  rw [heq]
  exact he

/-- The unnormalized Laplace integral. -/
def laplaceIntegral (a b z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), laplaceKernelReal a b z t

/-- Differentiation of the integral by an exact simultaneous parameter shift. -/
theorem hasDerivAt_laplaceIntegral (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (laplaceIntegral a b) (-laplaceIntegral (a + 1) (b + 1) z) z := by
  have hz2 : 0 < z / 2 := half_pos hz
  have hshape : 0 < a + 1 := add_pos ha zero_lt_one
  have hmeas : ∀ w : ℝ,
      AEStronglyMeasurable (laplaceKernelReal a b w) (volume.restrict (Ioi 0)) :=
    fun w => (continuousOn_laplaceKernelReal a b w).aestronglyMeasurable measurableSet_Ioi
  have hdmeas : AEStronglyMeasurable
      (fun t => -laplaceKernelReal (a + 1) (b + 1) z t)
      (volume.restrict (Ioi 0)) :=
    ((continuousOn_laplaceKernelReal (a + 1) (b + 1) z).aestronglyMeasurable
      measurableSet_Ioi).neg
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ Ioi (z / 2),
      ‖-laplaceKernelReal (a + 1) (b + 1) w t‖ ≤
        laplaceKernelReal (a + 1) (b + 1) (z / 2) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_pos (laplaceKernelReal_pos (a + 1) (b + 1) w t ht)]
    exact laplaceKernelReal_antitone (a + 1) (b + 1) t ht (z / 2) w hw.le
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ Ioi (z / 2),
      HasDerivAt (fun u => laplaceKernelReal a b u t)
        (-laplaceKernelReal (a + 1) (b + 1) w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w _
    exact hasDerivAt_laplaceKernelReal a b w t ht
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith only [hz] : z / 2 < z))
    (Eventually.of_forall hmeas) (integrableOn_laplaceKernelReal a b z ha hz)
    hdmeas hbound (integrableOn_laplaceKernelReal (a + 1) (b + 1) (z / 2) hshape hz2)
    hdiff
  change HasDerivAt (fun w => ∫ t in Ioi (0 : ℝ), laplaceKernelReal a b w t)
    (-∫ t in Ioi (0 : ℝ), laplaceKernelReal (a + 1) (b + 1) z t) z
  rw [← integral_neg]
  exact h.2

/-- The normalized integral is differentiable at every positive argument. -/
theorem hasDerivAt_UIr (a : Pos) (b z : ℝ) (hz : 0 < z) :
    HasDerivAt (UIr a b)
      (-(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z) z := by
  have h := (hasDerivAt_laplaceIntegral a.1 b z a.2 hz).const_mul (Real.Gamma a.1)⁻¹
  change HasDerivAt (fun w => (Real.Gamma a.1)⁻¹ * laplaceIntegral a.1 b w)
    (-(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z) z
  rw [neg_mul, ← mul_neg]
  exact h

/-- The unnormalized integral is differentiable throughout the positive half-line. -/
theorem differentiableOn_laplaceIntegral (a b : ℝ) (ha : 0 < a) :
    DifferentiableOn ℝ (laplaceIntegral a b) (Ioi 0) :=
  fun z hz => (hasDerivAt_laplaceIntegral a b z ha hz).differentiableAt.differentiableWithinAt

/-- Exact derivative of the unnormalized integral at a positive argument. -/
theorem deriv_laplaceIntegral (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    deriv (laplaceIntegral a b) z = -laplaceIntegral (a + 1) (b + 1) z :=
  (hasDerivAt_laplaceIntegral a b z ha hz).deriv

/-- Every finite smoothness order follows from the shifted integral derivative. -/
theorem contDiffOn_laplaceIntegral_nat (n : ℕ) (a b : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ n (laplaceIntegral a b) (Ioi 0) := by
  induction n generalizing a b with
  | zero =>
      exact contDiffOn_zero.mpr (differentiableOn_laplaceIntegral a b ha).continuousOn
  | succ n ih =>
      change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (laplaceIntegral a b) (Ioi 0)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨differentiableOn_laplaceIntegral a b ha, ?_, ?_⟩
      · intro hn
        exact False.elim (by simp at hn)
      · exact (ih (a + 1) (b + 1) (add_pos ha zero_lt_one)).neg.congr
          (fun z hz => deriv_laplaceIntegral a b z ha hz)

/-- The positive Laplace integral is smooth, with the C-infinity order. -/
theorem contDiffOn_laplaceIntegral (a b : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceIntegral a b) (Ioi 0) :=
  contDiffOn_infty.mpr (fun n => contDiffOn_laplaceIntegral_nat n a b ha)

/-- Smoothness of the normalized integral on its genuine positive domain. -/
theorem contDiffOn_UIr (a : Pos) (b : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (UIr a b) (Ioi 0) :=
  contDiffOn_const.mul (contDiffOn_laplaceIntegral a.1 b a.2)

/-- Smoothness of the transformed negative-shape formula on the positive half-line. -/
theorem contDiffOn_UNr (a : NegThird) :
    ContDiffOn ℝ (⊤ : ℕ∞) (UNr a) (Ioi 0) :=
  (contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)).mul (contDiffOn_UIr _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
