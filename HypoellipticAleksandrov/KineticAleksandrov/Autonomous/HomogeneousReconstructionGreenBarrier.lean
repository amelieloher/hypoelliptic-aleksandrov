module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionCollar
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence

/-! # Profile comparison for the actual finite-strip Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology ENNReal

/-- Integrating a smooth nonnegative profile against the actual Green measure is bounded
by any smooth native supersolution profile. -/
theorem reconstruction_green_lintegral_le_barrier
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (k q : Point → ℝ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) (rawLift k)) (hkn : ∀ p, 0 ≤ k p)
    (hqc : Continuous q) (hqr : ∀ p, IsSliceRegularAt q p)
    (hqn : ∀ p ∈ evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T, 0 ≤ q p)
    (hqo : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T,
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      q p ≤ -k p) :
    ∫⁻ p, ENNReal.ofReal (k (sectionTwoPoint p)) ∂stripGreenOfKernel H E.2 T e ≤
      ENNReal.ofReal (q (sectionTwoPoint e.1)) := by
  classical
  have hkcont : Continuous k := hk.continuous.comp
    (KineticPoint.homeomorphProd 1).continuous
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
    (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T
  have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
  obtain ⟨χ, hχ, hb, hmono, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
  let g (n : ℕ) (p : Point) : ℝ :=
    χ n (KineticPoint.equivProd 1 p) * k p
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    ((hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) :=
    (hχ n).1.mul hk
  have hgcont (n : ℕ) : Continuous (g n) :=
    ((hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous).mul
      hkcont
  have hgn (n : ℕ) (p : Point) : 0 ≤ g n p := mul_nonneg (hb n _).1 (hkn _)
  have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
    intro p hp
    have hx := tsupport_mul_subset_left hp
    have hy := (tsupport_comp_subset_preimage (χ n)
      (KineticPoint.homeomorphProd 1).continuous) hx
    have hu := (hχ n).2.2 hy
    change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
    simpa only [Equiv.symm_apply_apply] using hu
  have hgb (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |g n p| ≤ C := by
    obtain ⟨B, hB⟩ := (hgcont n).bounded_above_of_compact_support (hgc n)
    refine ⟨max B 0, le_max_right _ _, fun p => ?_⟩
    have hh : |g n p| ≤ B := by simpa only [Real.norm_eq_abs] using hB p
    exact hh.trans (le_max_left _ _)
  let F (n : ℕ) : BoundedBorel Point :=
    ⟨g n ∘ sectionTwoPoint,
      (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable, by
        obtain ⟨C, hC, hh⟩ := hgb n
        exact ⟨C, hC, fun p => hh (sectionTwoPoint p)⟩⟩
  have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ q (sectionTwoPoint e.1) := by
    have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
    let p := sectionTwoPoint e.1
    have hp : p ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
    have hcmp := reconstruction_duhamel_le_barrier hH hlam hLam A H E hE T (g n)
      q (hgn n) (hgs n) (hgc n) (hgD n) hqc hqr hqn
      (fun z hz => (hqo z hz).trans (neg_le_neg
        (mul_le_of_le_one_left (hkn _) (hb n _).2))) p hp
    have hpot := duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H)
      continuous_const T (g n) (hgn n) (hgcont n) (hgc n)
      e.1.time heT (stripPoleState H T e)
    have hIeq : stripPotentialOfKernel H E.2 T (F n) e = duhamelPotential E.2 T (g n) p := by
      rw [stripPotentialOfKernel, stripGreenOfKernel,
        integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
          (F n).measurable.aestronglyMeasurable]
      exact hpot.symm
    rw [hIeq]
    exact hcmp
  have hfun : (fun p => ENNReal.ofReal (k (sectionTwoPoint p))) =ᵐ[
      stripGreenOfKernel H E.2 T e] fun p => ⨆ n, ENNReal.ofReal (F n p) := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    have hnp : sectionTwoPoint p ∈ D := by
      refine ⟨hp.1, ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
      simpa only [U, mem_preimage, Equiv.symm_apply_apply] using hnp
    obtain ⟨N, hN⟩ := hcover _ hnU
    apply le_antisymm
    · apply le_iSup_of_le N
      change ENNReal.ofReal (k (sectionTwoPoint p)) ≤
        ENNReal.ofReal (χ N (KineticPoint.equivProd 1 (sectionTwoPoint p)) *
          k (sectionTwoPoint p))
      rw [hN N le_rfl, one_mul]
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hkn _) (hb n _).2)
  rw [lintegral_congr_ae hfun, lintegral_iSup]
  · apply iSup_le
    intro n
    have hi := stripGreen_integrable_boundedBorel H E.2 T e (F n)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun p => hgn n (sectionTwoPoint p)))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  · intro n
    exact (F n).measurable.ennreal_ofReal
  · intro i j hij p
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hmono _ hij) (hkn _))

/-- Integrating a smooth nonnegative profile against the actual Green measure is bounded
by any smooth native supersolution profile. -/
theorem reconstruction_green_le_barrier
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (k q : Point → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hk : ContDiff ℝ (⊤ : ℕ∞) (rawLift k)) (hkn : ∀ p, 0 ≤ k p)
    (hkb : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T, k p ≤ C)
    (hqc : Continuous q) (hqr : ∀ p, IsSliceRegularAt q p)
    (hqn : ∀ p ∈ evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T, 0 ≤ q p)
    (hqo : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T,
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      q p ≤ -k p) :
    ∫ p, k (sectionTwoPoint p) ∂stripGreenOfKernel H E.2 T e ≤ q (sectionTwoPoint e.1) := by
  classical
  have hkcont : Continuous k := hk.continuous.comp
    (KineticPoint.homeomorphProd 1).continuous
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
    (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T
  have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
  obtain ⟨χ, hχ, hb, -, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
  let g (n : ℕ) (p : Point) : ℝ :=
    χ n (KineticPoint.equivProd 1 p) * k p
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    ((hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) :=
    (hχ n).1.mul hk
  have hgcont (n : ℕ) : Continuous (g n) :=
    ((hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous).mul
      hkcont
  have hgn (n : ℕ) (p : Point) : 0 ≤ g n p := mul_nonneg (hb n _).1 (hkn _)
  have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
    intro p hp
    have hx := tsupport_mul_subset_left hp
    have hy := (tsupport_comp_subset_preimage (χ n)
      (KineticPoint.homeomorphProd 1).continuous) hx
    have hu := (hχ n).2.2 hy
    change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
    simpa only [Equiv.symm_apply_apply] using hu
  have hgb (n : ℕ) (p : Point) : |g n p| ≤ C := by
    rw [abs_of_nonneg (hgn n p)]
    by_cases hz : g n p = 0
    · simpa only [hz] using hC
    · have hp := hgD n (subset_tsupport _ hz)
      exact (mul_le_of_le_one_left (hkn _) (hb n _).2).trans (hkb _ hp)
  let F (n : ℕ) : BoundedBorel Point :=
    ⟨g n ∘ sectionTwoPoint,
      (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable,
      ⟨C, hC, fun p => hgb n _⟩⟩
  let K : BoundedBorel Point :=
    ⟨fun p => if sectionTwoPoint p ∈ D then k (sectionTwoPoint p) else 0,
      (hkcont.measurable.comp (continuous_sectionTwoPoint 1).measurable).piecewise
        (hD.measurableSet.preimage (continuous_sectionTwoPoint 1).measurable) measurable_const,
      ⟨C, hC, fun p => by
        dsimp only
        split_ifs with hp
        · rw [abs_of_nonneg (hkn _)]
          exact hkb _ hp
        · simpa using hC⟩⟩
  have hlim : ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
      Tendsto (fun n => F n p) atTop (𝓝 (K p)) := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    have hnp : sectionTwoPoint p ∈ D := by
      refine ⟨hp.1, ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
      simpa only [U, mem_preimage, Equiv.symm_apply_apply] using hnp
    obtain ⟨N, hN⟩ := hcover _ hnU
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    change K p = χ n (KineticPoint.equivProd 1 (sectionTwoPoint p)) *
      k (sectionTwoPoint p)
    change (if sectionTwoPoint p ∈ D then k (sectionTwoPoint p) else 0) =
      χ n (KineticPoint.equivProd 1 (sectionTwoPoint p)) * k (sectionTwoPoint p)
    rw [ite_eq_left hnp, hN n hn, one_mul]
  have hI := stripPotentialOfKernel_tendsto H E.2 T e F K C
    (fun n p => hgb n _) hlim
  have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ q (sectionTwoPoint e.1) := by
    have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
    let p := sectionTwoPoint e.1
    have hp : p ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
    have hcmp := reconstruction_duhamel_le_barrier hH hlam hLam A H E hE T (g n)
      q (hgn n) (hgs n) (hgc n) (hgD n) hqc hqr hqn
      (fun z hz => (hqo z hz).trans (neg_le_neg
        (mul_le_of_le_one_left (hkn _) (hb n _).2))) p hp
    have hpot := duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H)
      continuous_const T (g n) (hgn n) (hgcont n) (hgc n)
      e.1.time heT (stripPoleState H T e)
    have hIeq : stripPotentialOfKernel H E.2 T (F n) e = duhamelPotential E.2 T (g n) p := by
      rw [stripPotentialOfKernel, stripGreenOfKernel,
        integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
          (F n).measurable.aestronglyMeasurable]
      exact hpot.symm
    rw [hIeq]
    exact hcmp
  have hle := le_of_tendsto hI (Eventually.of_forall hbound)
  have heq : stripPotentialOfKernel H E.2 T K e =
      ∫ p, k (sectionTwoPoint p) ∂stripGreenOfKernel H E.2 T e := by
    apply integral_congr_ae
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    have hnp : sectionTwoPoint p ∈ D := by
      refine ⟨hp.1, ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    change (if sectionTwoPoint p ∈ D then k (sectionTwoPoint p) else 0) = _
    exact ite_eq_left hnp
  rwa [heq] at hle

/-- Integrating a smooth nonnegative profile against the actual Green measure is bounded
by any smooth native supersolution profile. -/
theorem reconstruction_green_le_profile
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (k q : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkn : ∀ v, 0 ≤ k v)
    (hkb : ∀ v ∈ H.carrier, k v ≤ C)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqn : ∀ v, H.lo ≤ v → v ≤ H.hi → 0 ≤ q v)
    (hqo : ∀ p, transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
      (reconstructionProfile q) p ≤ -k (p.position 0)) :
    ∫ p, k (p.velocity 0) ∂stripGreenOfKernel H E.2 T e ≤ q (e.1.velocity 0) := by
  classical
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
    (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T
  have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
  obtain ⟨χ, hχ, hb, -, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
  let g (n : ℕ) (p : Point) : ℝ :=
    χ n (KineticPoint.equivProd 1 p) * k (p.position 0)
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    ((hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) :=
    (hχ n).1.mul (hk.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.fst))
  have hgcont (n : ℕ) : Continuous (g n) :=
    ((hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous).mul
      (reconstructionProfile_continuous hk.continuous)
  have hgn (n : ℕ) (p : Point) : 0 ≤ g n p := mul_nonneg (hb n _).1 (hkn _)
  have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
    intro p hp
    have hx := tsupport_mul_subset_left hp
    have hy := (tsupport_comp_subset_preimage (χ n)
      (KineticPoint.homeomorphProd 1).continuous) hx
    have hu := (hχ n).2.2 hy
    change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
    simpa only [Equiv.symm_apply_apply] using hu
  have hgb (n : ℕ) (p : Point) : |g n p| ≤ C := by
    rw [abs_of_nonneg (hgn n p)]
    by_cases hz : g n p = 0
    · simpa only [hz] using hC
    · have hp := hgD n (subset_tsupport _ hz)
      have hv : p.position 0 ∈ H.carrier := by
        simpa only [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, sub_zero,
          intervalDomain,
          PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier] using hp.2
      exact (mul_le_of_le_one_left (hkn _) (hb n _).2).trans (hkb _ hv)
  let F (n : ℕ) : BoundedBorel Point :=
    ⟨g n ∘ sectionTwoPoint,
      (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable,
      ⟨C, hC, fun p => hgb n _⟩⟩
  let K : BoundedBorel Point :=
    ⟨fun p => if p.velocity 0 ∈ H.carrier then k (p.velocity 0) else 0,
      (hk.continuous.measurable.comp ((continuous_apply 0).comp
        continuous_velocity).measurable).piecewise
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable) measurable_const,
      ⟨C, hC, fun p => by
        dsimp only
        split_ifs with hp
        · rw [abs_of_nonneg (hkn _)]
          exact hkb _ hp
        · simpa using hC⟩⟩
  have hlim : ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
      Tendsto (fun n => F n p) atTop (𝓝 (K p)) := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    have hnp : sectionTwoPoint p ∈ D := by
      refine ⟨hp.1, ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
      simpa only [U, mem_preimage, Equiv.symm_apply_apply] using hnp
    obtain ⟨N, hN⟩ := hcover _ hnU
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    change K p = χ n (KineticPoint.equivProd 1 (sectionTwoPoint p)) *
      k ((sectionTwoPoint p).position 0)
    change (if p.velocity 0 ∈ H.carrier then k (p.velocity 0) else 0) =
      χ n (KineticPoint.equivProd 1 (sectionTwoPoint p)) * k (p.velocity 0)
    rw [ite_eq_left hp.2, hN n hn, one_mul]
  have hI := stripPotentialOfKernel_tendsto H E.2 T e F K C
    (fun n p => hgb n _) hlim
  have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ q (e.1.velocity 0) := by
    have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
    let p := sectionTwoPoint e.1
    have hp : p ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
    have hcmp := reconstruction_duhamel_le_barrier hH hlam hLam A H E hE T (g n)
      (reconstructionProfile q) (hgn n) (hgs n) (hgc n) (hgD n)
      (reconstructionProfile_continuous hq.continuous)
      (reconstructionProfile_regular (hq.of_le (by simp)))
      (fun z hz => by
        have hv := intervalDomain_closure_bounds H
          (by simpa only [mem_closure_movingDomain_iff, sub_zero] using hz.2)
        exact hqn _ hv.1 hv.2)
      (fun z _ => (hqo z).trans (neg_le_neg
        (mul_le_of_le_one_left (hkn _) (hb n _).2))) p hp
    have hpot := duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H)
      continuous_const T (g n) (hgn n) (hgcont n) (hgc n)
      e.1.time heT (stripPoleState H T e)
    have hIeq : stripPotentialOfKernel H E.2 T (F n) e = duhamelPotential E.2 T (g n) p := by
      rw [stripPotentialOfKernel, stripGreenOfKernel,
        integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
          (F n).measurable.aestronglyMeasurable]
      exact hpot.symm
    rw [hIeq]
    exact hcmp
  have hle := le_of_tendsto hI (Eventually.of_forall hbound)
  have heq : stripPotentialOfKernel H E.2 T K e =
      ∫ p, k (p.velocity 0) ∂stripGreenOfKernel H E.2 T e := by
    apply integral_congr_ae
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    change (if p.velocity 0 ∈ H.carrier then k (p.velocity 0) else 0) = _
    exact ite_eq_left hp.2
  rwa [heq] at hle

/-- Exponential collar occupation is uniformly quadratic in the collar width. -/
theorem reconstruction_green_collar_bound
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ p, reconstructionCollarWeight H δ (p.velocity 0) ∂stripGreenOfKernel H E.2 T e ≤
      2 * δ ^ 2 / lam := by
  have h := reconstruction_green_le_profile hH hlam hLam A H E hE T e
    (reconstructionCollarWeight H δ) (reconstructionCollarProfile H lam δ) 2 (by norm_num)
    (reconstructionCollarWeight_smooth H δ) (reconstructionCollarWeight_nonneg H δ)
    (fun v hv => reconstructionCollarWeight_le_two H hδ ⟨hv.1.le, hv.2.le⟩)
    (reconstructionCollarProfile_smooth H lam δ)
    (fun v hlo hhi => (reconstructionCollarProfile_bounds H hlam hδ ⟨hlo, hhi⟩).1)
    (reconstructionCollarProfile_operator_le hlam A H hδ)
  exact h.trans (reconstructionCollarProfile_bounds H hlam hδ ⟨e.2.2.1.le, e.2.2.2.le⟩).2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
