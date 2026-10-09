module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Mollify

/-!
# The mollification of an admissible test function is a smooth admissible test function

The admissible test functions: mollification with a kernel supported in a ball of radius `r ≤ 1`
preserves admissibility (with the support interval enlarged by `r`), keeps the uniform bounds,
and the weighted term `|v| |∇_z φ|` stays bounded because `|v| ≤ |v'| + 1` on the support.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set

variable {d : ℕ} {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}
  {ρ : ℝ × EvolutionAmbientState d → ℝ} {r : ℝ}

/-- The weighted transport term stays bounded under mollification. -/
theorem abs_weighted_moll_le (hρ : IsMollifierKernel ρ r) (hr1 : r ≤ 1)
    {f : ℝ × EvolutionAmbientState d → ℝ} (i : Fin d) {Cw Cf : ℝ}
    (hw : ∀ x, |x.2.1 i * f x| ≤ Cw) (hb : ∀ x, |f x| ≤ Cf) (x : ℝ × EvolutionAmbientState d) :
    |x.2.1 i * moll ρ f x| ≤ Cw + Cf := by
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hb x)
  have e : x.2.1 i * moll ρ f x = ∫ t, ρ t * (x.2.1 i * f (x - t)) := by
    rw [moll, ← integral_const_mul]
    congr 1
    funext t
    ring
  rw [e]
  have h := norm_integral_le_of_norm_le (hρ.integrable.mul_const (Cw + Cf))
    (f := fun t => ρ t * (x.2.1 i * f (x - t))) (Filter.Eventually.of_forall fun t => ?_)
  · rw [integral_mul_const, hρ.integral_eq_one, one_mul] at h
    simpa [Real.norm_eq_abs] using h
  · rw [norm_mul, Real.norm_eq_abs (ρ t), abs_of_nonneg (hρ.nonneg t)]
    by_cases ht : ρ t = 0
    · simp [ht]
    · have htn : ‖t‖ ≤ r := by
        by_contra h'
        exact ht (hρ.vanishes t (not_le.1 h'))
      have h1 : |t.2.1 i| ≤ 1 := by
        have a1 := norm_le_pi_norm t.2.1 i
        have a2 : ‖t.2.1‖ ≤ ‖t.2‖ := norm_fst_le t.2
        have a3 : ‖t.2‖ ≤ ‖t‖ := norm_snd_le t
        rw [Real.norm_eq_abs] at a1
        linarith
      have hx : x.2.1 i = (x - t).2.1 i + t.2.1 i := by simp
      have hsplit : x.2.1 i * f (x - t) =
          (x - t).2.1 i * f (x - t) + t.2.1 i * f (x - t) := by rw [hx]; ring
      have : ‖x.2.1 i * f (x - t)‖ ≤ Cw + Cf := by
        rw [Real.norm_eq_abs, hsplit]
        refine (abs_add_le _ _).trans (add_le_add (hw _) ?_)
        rw [abs_mul]
        calc |t.2.1 i| * |f (x - t)| ≤ 1 * Cf := mul_le_mul h1 (hb _) (abs_nonneg _) zero_le_one
          _ = Cf := one_mul _
      exact mul_le_mul_of_nonneg_left this (hρ.nonneg t)

/-- A mollification vanishes at `x` if `f` vanishes on the ball of radius `r` around `x`. -/
theorem moll_eq_zero_of_forall {f : ℝ × EvolutionAmbientState d → ℝ} (hρ : IsMollifierKernel ρ r)
    (x : ℝ × EvolutionAmbientState d) (h : ∀ t, ‖t‖ ≤ r → f (x - t) = 0) : moll ρ f x = 0 := by
  unfold moll
  have : ∀ t, ρ t * f (x - t) = 0 := fun t => by
    by_cases ht : ‖t‖ ≤ r
    · rw [h t ht, mul_zero]
    · rw [hρ.vanishes t (not_le.1 ht), zero_mul]
  simp [this]

/-- **Mollification preserves admissibility**. -/
theorem isAdmissibleTest_moll (hφ : IsAdmissibleTest T φ) (hρ : IsMollifierKernel ρ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a b : ℝ} (hab : a < b)
    (hz : ∀ τ, τ ∉ Icc a b → φ τ = 0) (hra : r < a) (hrb : b + r < T) :
    IsAdmissibleTest T (fun τ y => moll ρ (testValue φ) (τ, y)) := by
  set Ψ := moll ρ (testValue φ) with hΨdef
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := contDiff_moll_test hρ hφ
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  obtain ⟨Cf, hCf⟩ := hφ.value.2
  -- partial derivatives of the slices of `Ψ`
  have eT : (fun q : ℝ × EvolutionAmbientState d => deriv (fun τ => Ψ (τ, q.2)) q.1) =
      moll ρ (testTime φ) := funext fun q =>
    (deriv_slice_time Ψ q.1 q.2 (hΨd _)).trans (jointTimePartial_moll hρ hφ q)
  have eV : ∀ i, (fun q : ℝ × EvolutionAmbientState d =>
      velocityPartial i (fun y => Ψ (q.1, y)) q.2) = moll ρ (testVelocity φ i) := fun i =>
    funext fun q => (velocityPartial_slice Ψ q.1 q.2 (hΨd _) i).trans
      (jointVelocityPartial_moll hρ hφ i q)
  have eZ : ∀ i, (fun q : ℝ × EvolutionAmbientState d =>
      positionPartial i (fun y => Ψ (q.1, y)) q.2) = moll ρ (testPosition φ i) := fun i =>
    funext fun q => (positionPartial_slice Ψ q.1 q.2 (hΨd _) i).trans
      (jointPositionPartial_moll hρ hφ i q)
  have eH : ∀ i j, (fun q : ℝ × EvolutionAmbientState d =>
      velocityPartial i (velocityPartial j (fun y => Ψ (q.1, y))) q.2) =
        moll ρ (testHessian φ i j) := fun i j =>
    funext fun q => (velocityPartial_velocityPartial_slice hΨ q.1 q.2 i j).trans
      (jointVelocityPartial_velocityPartial_moll hρ hφ i j q)
  have hcont : ∀ g : ℝ × EvolutionAmbientState d → ℝ, Continuous g → Continuous (moll ρ g) :=
    fun g hg => (contDiff_moll hρ.smooth hρ.compact hg).continuous
  have hbdd : ∀ {g : ℝ × EvolutionAmbientState d → ℝ} {C : ℝ}, (∀ x, |g x| ≤ C) →
      ∀ x, |moll ρ g x| ≤ C := fun {g C} hg x =>
    abs_moll_le hρ.nonneg hρ.integral_eq_one hρ.integrable hg x
  refine ⟨fun y => ?_, fun τ => ?_, ⟨a - r, b + r, by linarith, by linarith, hrb, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact (hΨ.comp (contDiff_id.prodMk contDiff_const)).of_le (by exact_mod_cast le_top)
  · exact (contDiff_slice hΨ τ).of_le (by norm_num)
  · intro τ hτ
    funext y
    refine moll_eq_zero_of_forall hρ (τ, y) fun t ht => ?_
    have h0 : |t.1| ≤ ‖t‖ := by simpa [Real.norm_eq_abs] using norm_fst_le t
    have h1 : |t.1| ≤ r := h0.trans ht
    have h2 : τ - t.1 ∉ Icc a b := by
      intro h
      apply hτ
      constructor <;> linarith [(abs_le.1 h1).1, (abs_le.1 h1).2, h.1, h.2]
    simp only [testValue, Prod.fst_sub]
    rw [hz _ h2]
    rfl
  · exact ⟨hΨ.continuous, Cf, hbdd hCf⟩
  · rw [eT]
    obtain ⟨C, hC⟩ := hφ.timeDeriv.2
    exact ⟨hcont _ hφ.timeDeriv.1, C, hbdd hC⟩
  · intro i
    rw [eV i]
    obtain ⟨C, hC⟩ := (hφ.velocityGrad i).2
    exact ⟨hcont _ (hφ.velocityGrad i).1, C, hbdd hC⟩
  · intro i
    rw [eZ i]
    obtain ⟨C, hC⟩ := (hφ.positionGrad i).2
    exact ⟨hcont _ (hφ.positionGrad i).1, C, hbdd hC⟩
  · intro i j
    rw [eH i j]
    obtain ⟨C, hC⟩ := (hφ.velocityHess i j).2
    exact ⟨hcont _ (hφ.velocityHess i j).1, C, hbdd hC⟩
  · intro i j
    have e : (fun q : ℝ × EvolutionAmbientState d =>
        q.2.1 i * positionPartial j (fun y => Ψ (q.1, y)) q.2) =
        fun q => q.2.1 i * moll ρ (testPosition φ j) q := by
      funext q
      rw [← eZ j]
    rw [e]
    obtain ⟨Cw, hCw⟩ := (hφ.weightedTransport i j).2
    obtain ⟨Cp, hCp⟩ := (hφ.positionGrad j).2
    refine ⟨((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
      (hcont _ (hφ.positionGrad j).1), Cw + Cp, fun q => ?_⟩
    exact abs_weighted_moll_le hρ hr1 i (f := testPosition φ j) hCw hCp q

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
