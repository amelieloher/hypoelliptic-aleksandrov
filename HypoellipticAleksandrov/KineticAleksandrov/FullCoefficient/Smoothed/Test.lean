module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.SignFlip
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.KernelSup
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Mollifier
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Admissible

/-!
# The smoothing test function is admissible

The smoothed equation: for fixed `(τ, y)` the function `φ(s, y') = η_δ(τ - s) Φ_h(y - y')`
is an admissible test function of the forward equation when the time support
`[τ - δ, τ + δ]` lies in `(0, T)` (the Gaussian flow estimates, the admissible test functions).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h τ T : ℝ}

/-- The test function `φ(s, y') = η(τ - s) Φ_h(y - y')`. -/
def smoothingTest (Φ : SmoothingKernelFamily d lam) (η : ℝ → ℝ) (h τ : ℝ)
    (y : EvolutionAmbientState d) (s : ℝ) (y' : EvolutionAmbientState d) : ℝ :=
  η (τ - s) * Φ.kernel h (y - y')

theorem coordPartial_smoothingTest (hh : 0 < h) (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d)
    (s : ℝ) (y' : EvolutionAmbientState d) :
    coordPartial c (smoothingTest Φ η h τ y s) y' =
      -(η (τ - s) * coordPartial c (Φ.kernel h) (y - y')) := by
  have hd : Differentiable ℝ fun z => Φ.kernel h (y - z) :=
    ((Φ.contDiff hh).differentiable (by simp)).comp
      ((differentiable_const _).sub differentiable_id)
  unfold smoothingTest
  rw [coordPartial_const_mul hd, coordPartial_sub_comp ((Φ.contDiff hh).differentiable (by simp))]
  ring

theorem coordPartial₂_smoothingTest (hh : 0 < h) (c c' : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) (s : ℝ) (y' : EvolutionAmbientState d) :
    coordPartial c' (coordPartial c (smoothingTest Φ η h τ y s)) y' =
      η (τ - s) * coordPartial c' (coordPartial c (Φ.kernel h)) (y - y') := by
  have h1 : coordPartial c (smoothingTest Φ η h τ y s) = fun z =>
      (-η (τ - s)) * coordPartial c (Φ.kernel h) (y - z) := by
    funext z
    rw [coordPartial_smoothingTest Φ hh]
    ring
  have hd : Differentiable ℝ fun z => coordPartial c (Φ.kernel h) (y - z) :=
    (differentiable_coordPartial (Φ.contDiff hh) c).comp
      (differentiable_const _ |>.sub differentiable_id)
  rw [h1, coordPartial_const_mul hd,
    coordPartial_sub_comp (differentiable_coordPartial (Φ.contDiff hh) c)]
  ring

theorem deriv_smoothingTest (hη : IsMollifier δ η) (y y' : EvolutionAmbientState d) (s : ℝ) :
    deriv (fun s' => smoothingTest Φ η h τ y s' y') s =
      -(deriv η (τ - s) * Φ.kernel h (y - y')) := by
  have h1 : HasDerivAt (fun s' : ℝ => η (τ - s')) (-deriv η (τ - s)) s := by
    simpa using (hη.hasDerivAt (τ - s)).comp_const_sub τ s
  have := h1.mul_const (Φ.kernel h (y - y'))
  unfold smoothingTest
  rw [this.deriv]
  ring

theorem isBoundedContinuous_sep {e : ℝ → ℝ} {g : EvolutionAmbientState d → ℝ}
    (he : Continuous e) (hg : Continuous g) {Ce Cg : ℝ} (hCe : ∀ t, |e t| ≤ Ce)
    (hCg : ∀ w, |g w| ≤ Cg) (τ : ℝ) (y : EvolutionAmbientState d) :
    IsBoundedContinuous (fun q : ℝ × EvolutionAmbientState d => e (τ - q.1) * g (y - q.2)) := by
  refine ⟨(he.comp (continuous_const.sub continuous_fst)).mul
    (hg.comp (continuous_const.sub continuous_snd)), Ce * Cg, fun q => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCe _) (hCg _) (abs_nonneg _) ((abs_nonneg _).trans (hCe (τ - q.1)))

theorem abs_coord_le_norm (w : EvolutionAmbientState d) (i : Fin d) : |w.1 i| ≤ ‖w‖ := by
  have h1 : ‖w.1 i‖ ≤ ‖w.1‖ := norm_le_pi_norm w.1 i
  have h2 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  simpa [Real.norm_eq_abs] using h1.trans h2

/-- **Admissibility of the smoothing test function**: for
`δ < τ` and `τ + δ < T` the function `η_δ(τ - s) Φ_h(y - y')` is admissible. -/
theorem isAdmissibleTest_smoothingTest (hη : IsMollifier δ η) (hh : 0 < h) (hδ : 0 < δ)
    (hτ : δ < τ) (hτT : τ + δ < T) (y : EvolutionAmbientState d) :
    IsAdmissibleTest T (smoothingTest Φ η h τ y) := by
  obtain ⟨Cη, hCη⟩ := hη.exists_bound
  obtain ⟨Cη', hCη'⟩ := hη.exists_bound_deriv
  obtain ⟨C0, hC0⟩ := exists_abs_kernel_bound Φ hh
  obtain ⟨C1, hC1⟩ := exists_partial_bound Φ hh
  obtain ⟨C1w, hC1w⟩ := exists_weighted_partial_bound Φ hh
  obtain ⟨C2, hC2⟩ := exists_partial_two_bound Φ hh
  have hΦ := Φ.contDiff hh
  have hcont1 : ∀ c, Continuous (coordPartial c (Φ.kernel h)) := fun c =>
    continuous_coordPartial hΦ c
  have hcont2 : ∀ c c', Continuous (coordPartial c' (coordPartial c (Φ.kernel h))) := fun c c' =>
    continuous_coordPartial (contDiff_coordPartial hΦ c) c'
  have hηc := hη.continuous
  have hη'c := hη.contDiff_deriv.continuous
  refine ⟨fun y' => ?_, fun s => ?_, ⟨τ - δ, τ + δ, by linarith, by linarith, by linarith,
    fun s hs => ?_⟩, ?_, ?_, fun i => ?_, fun i => ?_, fun i j => ?_, fun i j => ?_⟩
  · exact ((hη.contDiff.comp (contDiff_const.sub contDiff_id)).mul contDiff_const).of_le
      (by exact_mod_cast le_top)
  · exact (contDiff_const.mul (hΦ.comp (contDiff_const.sub contDiff_id))).of_le
      (by simp)
  · funext y'
    unfold smoothingTest
    rw [hη.support (τ - s) ?_, zero_mul]
    · rfl
    · simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · exact (by linarith : δ ≤ τ - s).trans (le_abs_self _)
      · exact (by linarith : δ ≤ -(τ - s)).trans (neg_le_abs _)
  · exact isBoundedContinuous_sep hηc (hΦ.continuous) hCη hC0 τ y
  · have : (fun q : ℝ × EvolutionAmbientState d =>
        deriv (fun s => smoothingTest Φ η h τ y s q.2) q.1) =
        fun q => (-deriv η (τ - q.1)) * Φ.kernel h (y - q.2) := by
      funext q
      rw [deriv_smoothingTest Φ hη]
      ring
    rw [this]
    exact isBoundedContinuous_sep hη'c.neg hΦ.continuous (fun t => by simpa using hCη' t) hC0 τ y
  · have : (fun q : ℝ × EvolutionAmbientState d =>
        velocityPartial i (smoothingTest Φ η h τ y q.1) q.2) =
        fun q => η (τ - q.1) * (-coordPartial (Sum.inl i) (Φ.kernel h) (y - q.2)) := by
      funext q
      rw [velocityPartial_eq, coordPartial_smoothingTest Φ hh]
      ring
    rw [this]
    exact isBoundedContinuous_sep hηc (hcont1 _).neg hCη (fun w => by simpa using hC1 _ w) τ y
  · have : (fun q : ℝ × EvolutionAmbientState d =>
        positionPartial i (smoothingTest Φ η h τ y q.1) q.2) =
        fun q => η (τ - q.1) * (-coordPartial (Sum.inr i) (Φ.kernel h) (y - q.2)) := by
      funext q
      rw [positionPartial_eq, coordPartial_smoothingTest Φ hh]
      ring
    rw [this]
    exact isBoundedContinuous_sep hηc (hcont1 _).neg hCη (fun w => by simpa using hC1 _ w) τ y
  · have : (fun q : ℝ × EvolutionAmbientState d =>
        velocityPartial i (velocityPartial j (smoothingTest Φ η h τ y q.1)) q.2) =
        fun q => η (τ - q.1) *
          coordPartial (Sum.inl i) (coordPartial (Sum.inl j) (Φ.kernel h)) (y - q.2) := by
      funext q
      rw [velocityPartial_eq, velocityPartial_eq]
      exact coordPartial₂_smoothingTest Φ hh _ _ y q.1 q.2
    rw [this]
    exact isBoundedContinuous_sep hηc (hcont2 _ _) hCη (hC2 _ _) τ y
  · have : (fun q : ℝ × EvolutionAmbientState d =>
        q.2.1 i * positionPartial j (smoothingTest Φ η h τ y q.1) q.2) =
        fun q => η (τ - q.1) *
          (-(q.2.1 i * coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2))) := by
      funext q
      rw [positionPartial_eq, coordPartial_smoothingTest Φ hh]
      ring
    rw [this]
    refine ⟨(hηc.comp (continuous_const.sub continuous_fst)).mul
      (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
        ((hcont1 _).comp (continuous_const.sub continuous_snd))).neg,
      Cη * ((|y.1 i| + 1) * C1w), fun q => ?_⟩
    rw [abs_mul, abs_neg, abs_mul]
    have hw := hC1w (Sum.inr j) (y - q.2)
    have hq : |q.2.1 i| ≤ |y.1 i| + ‖y - q.2‖ := by
      have : q.2.1 i = y.1 i - (y - q.2).1 i := by simp
      rw [this]
      exact (abs_sub _ _).trans (add_le_add le_rfl (abs_coord_le_norm _ i))
    have hg0 : 0 ≤ |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)| := abs_nonneg _
    refine mul_le_mul (hCη _) ?_ (by positivity) ((abs_nonneg _).trans (hCη (τ - q.1)))
    calc |q.2.1 i| * |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)|
        ≤ (|y.1 i| + ‖y - q.2‖) * |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)| :=
          mul_le_mul_of_nonneg_right hq hg0
      _ = |y.1 i| * |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)| +
          ‖y - q.2‖ * |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)| := by ring
      _ ≤ |y.1 i| * C1w + C1w := by
          have h1 : |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)| ≤ C1w :=
            le_trans (by nlinarith [norm_nonneg (y - q.2)]) hw
          have h2 : ‖y - q.2‖ * |coordPartial (Sum.inr j) (Φ.kernel h) (y - q.2)| ≤ C1w :=
            le_trans (by nlinarith [norm_nonneg (y - q.2)]) hw
          have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (y.1 i))
          linarith
      _ = (|y.1 i| + 1) * C1w := by ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
