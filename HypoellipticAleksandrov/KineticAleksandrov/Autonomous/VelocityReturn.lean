module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturnAveraging
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountReturnBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryKernel

/-! # Pointwise velocity return from occupation and the full source return-time comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- The band itself has square-root decay; the constant precedes all coefficient and pole data. -/
theorem velocity_band_return_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (r : ℝ) (z : Z) (t : NNReal),
      0 < r → |z.2| ≤ 3 * r →
      (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) t z
        {w | |w.2| ≤ 3 * r}).toReal ≤ C * (1 + (t : ℝ) / r ^ 2) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨CR, hCR, hreturn⟩ := return_time_ambient_of_scalar hH hLE hlam hLam hReturn
  obtain ⟨B, hB, hocc⟩ := velocity_occupation_and_moment hH hLE hlam hLam
  let K := CR * B * Real.sqrt 3
  have hK : 0 < K := by dsimp only [K]; positivity
  let C := (10 : ℝ) ^ ((1 : ℝ) / 2) + K * (2 : ℝ) ^ ((1 : ℝ) / 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A r z t hr hz
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
  let f := fun s => velocityBandAction E r s z
  let x := (t : ℝ) / r ^ 2
  have hx : 0 ≤ x := div_nonneg t.property (sq_nonneg r)
  have hx1 : 0 < 1 + x := by linarith
  have hdecay : 0 ≤ (1 + x) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx1.le _
  have hf : f t = (kernelXV E t z {w | |w.2| ≤ 3 * r}).toReal := by
    dsimp only [f]
    rw [velocityBandAction_eq_probability A E hE,
      velocityBandProbability_eq_kernelXV, Real.toNNReal_coe]
  by_cases hlarge : 9 * r ^ 2 ≤ (t : ℝ)
  · have ht : 0 < (t : ℝ) := lt_of_lt_of_le (by positivity) hlarge
    have hv : |z.2| ≤ Real.sqrt (t : ℝ) := hz.trans
      (Real.le_sqrt_of_sq_le (by nlinarith))
    have hfcomp (s : ℝ) (hs : s ∈ Ioc (2 * (t : ℝ)) (3 * (t : ℝ))) :
        f t ≤ CR * f s := by
      have hs0 : 0 ≤ s := by linarith [hs.1]
      have hh := hreturn A (velocityBandDatum r) (fun p => by
        change 0 ≤ ({w : EvolutionAmbientState 1 | |w.2 0| ≤ 3 * r}).indicator
          (fun _ => (1 : ℝ)) p
        exact indicator_nonneg (fun _ _ => zero_le_one) _)
        t (Real.toNNReal s) z ht
        (by simpa only [Real.coe_toNNReal s hs0] using hs.1.le)
        (by simpa only [Real.coe_toNNReal s hs0] using hs.2) hv
      change fullSpaceAction E (velocityBandDatum r)
          ⟨t, fun _ => z.1, fun _ => z.2⟩ ≤
        CR * fullSpaceAction E (velocityBandDatum r)
          ⟨Real.toNNReal s, fun _ => z.1, fun _ => z.2⟩ at hh
      rw [← fullSpacePhysicalSemigroup_eq_action A E hE t (velocityBandDatum r)
          (fun _ => z.1, fun _ => z.2),
        ← fullSpacePhysicalSemigroup_eq_action A E hE (Real.toNNReal s)
          (velocityBandDatum r) (fun _ => z.1, fun _ => z.2)] at hh
      simpa only [f, velocityBandAction, Real.toNNReal_coe] using hh
    have hav := velocity_return_time_average A E hE z r t CR ht hCR.le hfcomp
    have hoc := (hocc A r (3 * (t : ℝ)) z hr (by positivity)).1
    have hprod := hav.trans (mul_le_mul_of_nonneg_left hoc hCR.le)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)] at hprod
    have hraw : f t ≤ K * (r * Real.sqrt (t : ℝ) / (t : ℝ)) := by
      have hdiv : f t ≤ (CR * (B * r * (Real.sqrt 3 * Real.sqrt (t : ℝ)))) /
          (t : ℝ) := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hprod)
      convert hdiv using 1
      dsimp only [K]
      ring
    have hscale : r * Real.sqrt (t : ℝ) / (t : ℝ) = x ^ (-(1 : ℝ) / 2) := by
      have hh := box_decay_scaling (alpha := 1) hr ht
      norm_num only [gamma, Real.rpow_one, one_div, show (2 : ℝ) - 1 = 1 by norm_num] at hh
      simpa only [Real.sqrt_eq_rpow, x, neg_div] using hh
    rw [hscale] at hraw
    have hxlarge : 1 ≤ x := by
      dsimp only [x]
      apply (le_div_iff₀ (by positivity : 0 < r ^ 2)).mpr
      nlinarith
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left
      (box_decay_large_comparison (g := 1) hxlarge (by norm_num)) hK.le)
    have hKC : K * (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ C := by
      dsimp only [C]
      exact le_add_of_nonneg_left (by positivity)
    have hbound : K * ((2 : ℝ) ^ ((1 : ℝ) / 2) *
        (1 + x) ^ (-(1 : ℝ) / 2)) ≤ C * (1 + x) ^ (-(1 : ℝ) / 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hdecay
    rw [hf] at hfinal
    exact hfinal.trans hbound
  · have hxsmall : 1 + x ≤ 10 := by
      dsimp only [x]
      have hh := (div_lt_iff₀ (by positivity : 0 < r ^ 2)).mpr (lt_of_not_ge hlarge)
      linarith
    have hp := Real.rpow_le_rpow_of_nonpos hx1 hxsmall (by norm_num : -(1 : ℝ) / 2 ≤ 0)
    have hm := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) ((1 : ℝ) / 2))
    have hone : (10 : ℝ) ^ ((1 : ℝ) / 2) * 10 ^ (-(1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
      norm_num
    rw [hone] at hm
    have hmass : (kernelXV E t z {w | |w.2| ≤ 3 * r}).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono ENNReal.one_ne_top
        ((measure_mono (subset_univ _)).trans (kernelXV_mass_le_one E t z))).trans_eq
          ENNReal.toReal_one
    have hsmallC : (10 : ℝ) ^ ((1 : ℝ) / 2) ≤ C := by
      dsimp only [C]
      exact le_add_of_nonneg_right (by positivity)
    exact (hmass.trans hm).trans (mul_le_mul_of_nonneg_right hsmallC hdecay)

/-- The literal source active-interval return bound, conditional only on full return-time. -/
theorem velocity_return_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (z : Z) (t : ℝ),
      |c.vbar| = 2 * c.r → |z.2| ≤ 3 * c.r → 0 ≤ t →
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z
        {w | w.2 ∈ c.active} ≤ ENNReal.ofReal (C * (1 + t / c.r ^ 2) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C, hC, h⟩ := velocity_band_return_of_return_time hH hLE hlam hLam hReturn
  refine ⟨C, hC, ?_⟩
  intro A c z t hc hz ht
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hb := h A c.r z (Real.toNNReal t) c.positive hz
  rw [Real.coe_toNNReal t ht] at hb
  have hsub : {w : Z | w.2 ∈ c.active} ⊆ {w | |w.2| ≤ 3 * c.r} := by
    intro w hw
    have hh := (c.active_abs_bounds hw).2
    rw [hc] at hh
    change |w.2| ≤ 3 * c.r
    linarith only [hh]
  have hmass := (measure_mono (subset_univ {w : Z | |w.2| ≤ 3 * c.r})).trans
    (kernelXV_mass_le_one E (Real.toNNReal t) z)
  apply (measure_mono hsub).trans
  rw [← ENNReal.ofReal_toReal (hmass.trans_lt ENNReal.one_lt_top).ne]
  exact ENNReal.ofReal_le_ofReal hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
