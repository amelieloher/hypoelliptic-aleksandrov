module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernelEstimates
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Integrability in time of the Gaussian away from the origin -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Away from the pole, the time integral defining the fundamental density is finite. -/
theorem integrable_bellmanGaussianKernel_time (q : BellmanPuncturedPlane) :
    Integrable (fun t => bellmanGaussianKernel t q.val) bellmanPositiveTimeVolume := by
  let f : ℝ → ℝ := fun s => Real.sqrt 3 / (2 * Real.pi * s ^ 2) *
    Real.exp (-3 * q.val.1 ^ 2 / s ^ 3 + 3 * q.val.1 * q.val.2 / s ^ 2 - q.val.2 ^ 2 / s)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have ha : 0 < q.val.1 ^ 2 + q.val.2 ^ 2 := by
    have hnonneg := add_nonneg (sq_nonneg q.val.1) (sq_nonneg q.val.2)
    refine lt_of_le_of_ne hnonneg ?_
    intro h
    apply q.property
    have hx : q.val.1 = 0 := by nlinarith only [h, sq_nonneg q.val.2]
    have hv : q.val.2 = 0 := by nlinarith only [h, sq_nonneg q.val.1]
    exact Prod.ext hx hv
  let C : ℝ := Real.sqrt 3 / (2 * Real.pi)
  let M : ℝ := 64 * Real.sqrt 3 / (Real.pi * (q.val.1 ^ 2 + q.val.2 ^ 2) ^ 2)
  have hsmall : IntegrableOn f (Ioc 0 1) := by
    refine (integrableOn_const (measure_Ioc_lt_top :
      (volume : Measure ℝ) (Ioc (0 : ℝ) 1) < ⊤).ne (C := M)).mono'
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hpos := bellmanGaussianKernel_pos ⟨s, hs.1⟩ q.val
    change ‖bellmanGaussianKernel ⟨s, hs.1⟩ q.val‖ ≤ M
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact bellmanGaussianKernel_le_smallTime ⟨s, hs.1⟩ hs.2 q.val
      (q.val.1 ^ 2 + q.val.2 ^ 2) ha le_rfl
  have hlarge : IntegrableOn f (Ioi 1) := by
    have hi := (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := 1)
      (by norm_num) (by norm_num)).const_mul C
    refine hi.mono' hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := lt_trans (by norm_num) hs
    have hpos := bellmanGaussianKernel_pos ⟨s, hspos⟩ q.val
    change ‖bellmanGaussianKernel ⟨s, hspos⟩ q.val‖ ≤ C * s ^ (-2 : ℝ)
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    have h := bellmanGaussianKernel_le ⟨s, hspos⟩ q.val
    convert h using 1
    dsimp [C]
    rw [Real.rpow_neg hspos.le, Real.rpow_two]
    ring
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext s
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans (by norm_num) h
    · intro h
      by_cases h1 : s ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hall : IntegrableOn f (Ioi 0) := by
    rw [← hunion]
    exact hsmall.union hlarge
  have hmap : Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume = volume.restrict (Ioi (0 : ℝ)) := by
    unfold bellmanPositiveTimeVolume
    convert! map_comap_subtype_coe (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (volume.restrict (Ioi (0 : ℝ))) using 1
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have hfi : Integrable f (Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume) := by
    rw [hmap]
    exact hall
  change Integrable (f ∘ (Subtype.val : BellmanPositiveTime → ℝ))
    bellmanPositiveTimeVolume
  exact (MeasurableEmbedding.subtype_coe (s := Ioi (0 : ℝ))
    measurableSet_Ioi).integrable_map_iff.mp hfi

/-- The literal fundamental density is finite at every punctured-plane point. -/
theorem bellmanFundamentalDensity_ne_top (q : BellmanPuncturedPlane) :
    bellmanFundamentalDensity q ≠ ⊤ := by
  have h := integrable_bellmanGaussianKernel_time q
  exact (lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable
    (ae_of_all _ (fun t => (bellmanGaussianKernel_pos t q.val).le))).mpr h

end HypoellipticAleksandrov.KineticAleksandrov
