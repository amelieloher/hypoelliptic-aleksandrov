module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionInterface
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionNormRecovery
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceNormDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionHeight
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionDiagonal
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # The unconditional measurable family from flattening and spatial smoothing -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- For any fixed internally justified geometry, the literal measurable family is
constructed by a separate spatial smoothing scale for each flattening scale. -/
theorem construction_measurableFamily_of_geometry {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (p R mu S : ℝ)
    (hp : 1 ≤ p) (he : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (hR : 0 < R) (hmu : 0 < mu) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hTS : barrierTime mu < S ^ 2)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (hgeom : ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) :
    MeasurableFamilyStatement d p (profileLowerEllipticity h) (profileUpperEllipticity h)
      ⟨barrierTime mu, 0, 0⟩ S := by
  obtain ⟨m, hm, hmargin⟩ := construction_exists_strict_velocity_margin ha h R hvel
  obtain ⟨r0, hr0, hsmall⟩ := construction_small_scale_threshold alpha ha
  obtain ⟨r, hr, hlim⟩ := construction_exists_scales r0 hr0
  have hscale (j : ℕ) : 2 * Real.rpow (r j) alpha ≤ 1 :=
    ((hsmall (r j) (hr j).1 (hr j).2).2).trans (by norm_num)
  have hheight (j : ℕ) : flatteningOffset * Real.rpow (r j) alpha ≤ 1 / 4 :=
    (hsmall (r j) (hr j).1 (hr j).2).1
  let T := barrierTime mu
  let Q := backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S
  let nu := volume.restrict Q
  let pE := ENNReal.ofReal p
  have hpE : 1 ≤ pE := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hp0 : pE ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
  have hpTop : pE ≠ ∞ := ENNReal.ofReal_ne_top
  let U := fun j n => smoothedZeroExtendedProfile h (r j) mu R (standardMollifierSequence n)
  let g := fun j P => max (constructionIndicatorSource h (r j) mu R
    (KineticPoint.equivProd d P)) 0
  let f := fun j n P => max (backwardOperator (fun _t x v => profileMatrix h (x, v))
    (U j n) P) 0
  let error := fun j n => eLpNorm (fun P => f j n P - g j P) pE nu
  have herr (j : ℕ) : Tendsto (error j) atTop (𝓝 0) :=
    construction_positiveSource_error_tendsto hd ha ha1 h (r j) mu R m T S
      (hr j).1 hmu hR hm hS (hscale j) hmargin pE hp0 hpTop
  let good := fun j n =>
    (∀ P, P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S → U j n P = 0) ∧
    (∃ P ∈ Q, (1 / 4 : ℝ) ≤ U j n P)
  have hgood (j : ℕ) : ∀ᶠ n in atTop, good j n := by
    obtain ⟨P, hP, hh⟩ := construction_smoothed_interior_height_eventually h (r j) mu R S
      (hr j).1 hmu hR hS hTS (hscale j) (hheight j) hvel
    filter_upwards [construction_smoothed_boundary_eventually ha h T S hS hTS hgeom
      (r j) mu R, hh] with n hn hhP
    exact ⟨hn, P, hP, hhP⟩
  obtain ⟨scale, hs, heLim⟩ := construction_diagonal_choice error herr good hgood
  refine ⟨profileMatrix h, fun j => U j (scale j),
    (selectedProfile_spec h).2.2.2.2.1, (selectedProfile_spec h).2.2.2.2.2.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact smoothedZeroExtendedProfile_contDiff ha h (r j) mu R (hr j).1 hmu hR hvel _
  · intro j P
    exact smoothedZeroExtendedProfile_nonneg h (r j) mu R _ P
  · intro j P hP
    exact (hs j).1.1 P hP
  · intro j
    exact (hs j).1.2
  · have hgLim : Tendsto (fun j => eLpNorm (g j) pE nu) atTop (𝓝 0) :=
      construction_indicatorSource_norm_tendsto hd ha ha1 h mu R m T S p hmu hR hm hS
        hrate hmargin hp he r (fun j => (hr j).1) hscale hlim
    have hu : Tendsto (fun j => error j (scale j) + eLpNorm (g j) pE nu)
        atTop (𝓝 0) := by
      simpa only [add_zero] using heLim.add hgLim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => bot_le)
    intro j
    have hn := eLpNorm_add_le (p := pE) (μ := nu)
      (f := fun P => f j (scale j) P - g j P) (g := g j) hpE
    have heq : (fun P => f j (scale j) P - g j P) + g j = f j (scale j) := by
      funext P
      simp only [Pi.add_apply, sub_add_cancel]
    rw [heq] at hn
    exact hn

/-- The measurable family holds at the exact parameters already published to the
smooth-coefficient lane; all choices are those made in `counterParameters`. -/
theorem measurableFamily_holds (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    MeasurableFamilyStatement d p (counterParameters d p).1 (counterParameters d p).2.1
      (counterParameters d p).2.2.1 (counterParameters d p).2.2.2 := by
  classical
  let h := counterProfileFor d hd p hp hpd
  have ha := counterAlpha_spec d hd p hp hpd
  let geom := construction_fixed_geometry_of_profile hd ha.1 h
  let R := geom.choose
  let mu := geom.choose_spec.choose
  let S := geom.choose_spec.choose_spec.choose
  have hg := geom.choose_spec.choose_spec.choose_spec
  have hh := construction_measurableFamily_of_geometry hd ha.1 ha.2.1 h p R mu S hp ha.2.2
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1
  simpa only [counterParameters, dite_eq_left (And.intro hd (And.intro hp hpd))] using! hh

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
