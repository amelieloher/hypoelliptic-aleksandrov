module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformOperator
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyGeometry
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization

/-! # Positive-source norm recovery on the one fixed kinetic cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal

/-- Spatial smoothing of each fixed flattened cutoff recovers the positive source in
finite-exponent norm on the fixed cylinder, without an analytic premise. -/
theorem construction_positiveSource_error_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun P =>
      max (backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P) 0 -
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0)
      p (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)))
      atTop (𝓝 0) := by
  let Q := backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S
  let nu := volume.restrict Q
  have hQm : MeasurableSet Q := (isOpen_backwardCylinder _ _ hS).measurableSet
  have : IsFiniteMeasure nu := ⟨by
    simpa only [nu, Measure.restrict_apply_univ] using
      (backwardCylinder_volume_lt_top (⟨T, 0, 0⟩ : KineticPoint d) S hS)⟩
  let F := fun n P => backwardOperator (fun _t x v => profileMatrix h (x, v))
    (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P
  let g := fun P => constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)
  have hA := (selectedProfile_spec h).2.2.2.2.1
  have hF (n : ℕ) : Measurable (F n) :=
    measurable_backwardOperator_of_joint_smooth (profileMatrix h) hA _
      (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
        (fun q hq => (hmargin q hq).trans hm) (standardMollifierSequence n))
  have hg : Measurable g := (construction_indicatorSource_measurable h r mu R).comp
    (KineticPoint.measurable_equivProd d)
  let AC := 3 * (|profileLowerEllipticity h| + |profileUpperEllipticity h|)
  have hAC : 0 ≤ AC := mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hAb q i k : |profileMatrix h q i k| ≤ AC :=
    coefficient_entry_abs_le_of_ellipticity
      ((selectedProfile_spec h).2.2.2.2.2.1 q).1
      ((selectedProfile_spec h).2.2.2.2.2.1 q).2 i k
  obtain ⟨C, hC, hb⟩ := construction_smoothedOperator_uniform_bound hd ha ha1 h
    r mu R m (T - S ^ 2) T S hr hmu hR hm hS.le hscale hmargin
    (profileMatrix h) AC hAC hAb
  have hFb (n : ℕ) : ∀ᵐ P ∂nu, |F n P| ≤ C := by
    filter_upwards [ae_restrict_mem hQm] with P hP
    have hh := (construction_mem_cylinder_iff T S hS P).mp hP
    exact hb (standardMollifierSequence n) P ⟨hh.1.le, hh.2.1.le⟩
      (fun i => (PDE.abs_apply_le_vecEuclideanNorm P.velocity i).trans hh.2.2.1.le)
  have hl : ∀ᵐ P ∂nu, Tendsto (fun n => F n P) atTop (𝓝 (g P)) :=
    ae_restrict_of_ae (construction_smoothedOperator_tendsto_ae_spacetime hd ha ha1 h
      r mu R m hr hmu hR hm hscale hmargin)
  have hgb : ∀ᵐ P ∂nu, |g P| ≤ C := by
    filter_upwards [hl, ae_all_iff.mpr hFb] with P hP hbP
    exact le_of_tendsto' hP.abs hbP
  exact construction_positive_part_error_tendsto nu p hp0 hpTop F g
    (fun n => (hF n).aestronglyMeasurable) hg.aestronglyMeasurable C hC hFb hgb hl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
