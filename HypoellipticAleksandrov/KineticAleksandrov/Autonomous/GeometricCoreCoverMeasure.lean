module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic

/-! # Gluing local density bounds through a countable measurable cover -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- A finite absolutely continuous measure has a nonnegative measurable real density. -/
theorem density_of_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν] (hac : ν ≪ m) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = m.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let g := fun x => (ν.rnDeriv m x).toReal
  refine ⟨g,
    (Measure.measurable_rnDeriv ν m).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν m hac]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top ν m] with x hx
  exact (ENNReal.ofReal_toReal hx.ne).symm

/-- A local density dominates the same restriction of any global nonnegative density. -/
theorem density_local_norm_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) [SigmaFinite m] (g f : X → ℝ)
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (_hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (S : Set X) (hS : MeasurableSet S) (p : ℝ≥0∞)
    (hle : (m.withDensity (fun x => ENNReal.ofReal (g x))).restrict S ≤
      m.withDensity (fun x => ENNReal.ofReal (f x))) :
    eLpNorm g p (m.restrict S) ≤ eLpNorm f p m := by
  have hle' : (m.restrict S).withDensity (fun x => ENNReal.ofReal (g x)) ≤
      (m.restrict S).withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← restrict_withDensity hS, ← restrict_withDensity hS]
    simpa only [Measure.restrict_restrict hS, inter_self] using
      Measure.restrict_mono_measure hle S
  have hgf : ∀ᵐ x ∂m.restrict S, ENNReal.ofReal (g x) ≤ ENNReal.ofReal (f x) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀
      hgm.ennreal_ofReal.aemeasurable.restrict
    intro E hE _
    have h := Measure.le_iff.1 hle' E hE
    rwa [withDensity_apply _ hE, withDensity_apply _ hE] at h
  have hn : ∀ᵐ x ∂m.restrict S, ‖g x‖ ≤ ‖f x‖ := by
    filter_upwards [hgf] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 x), abs_of_nonneg (hf0 x)]
      using (ENNReal.ofReal_le_ofReal_iff (hf0 x)).mp hx
  exact (eLpNorm_mono_ae hgm.aestronglyMeasurable.restrict hn).trans
    (eLpNorm_restrict_le f p m S)

/-- A source real norm bound gives the equivalent bound for its q-power integral. -/
theorem density_power_integral_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) (f : X → ℝ) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hf : MemLp f (ENNReal.ofReal q) m)
    (hn : (eLpNorm f (ENNReal.ofReal q) m).toReal ≤ K ^ (1 / q)) :
    ∫⁻ x, ‖f x‖ₑ ^ q ∂m ≤ ENNReal.ofReal K := by
  have hnorm : eLpNorm f (ENNReal.ofReal q) m ≤ ENNReal.ofReal (K ^ (1 / q)) :=
    (ENNReal.le_ofReal_iff_toReal_le hf.ne (Real.rpow_nonneg hK _)).2 hn
  have he : ∫⁻ x, ‖f x‖ₑ ^ q ∂m = eLpNorm f (ENNReal.ofReal q) m ^ q := by
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hq
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (K ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow hnorm hq.le
    _ = ENNReal.ofReal K := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hK _) hq.le,
        ← Real.rpow_mul hK, one_div_mul_cancel hq.ne', Real.rpow_one]

/-- Local densities on a countable cover glue, with a bound by the sum of power integrals. -/
theorem density_of_countable_cover {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hcover : ν (⋃ i, S i)ᶜ = 0)
    (f : ι → X → ℝ) (hfm : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (q : ℝ) (hq : 0 < q)
    (hle : ∀ i, ν.restrict (S i) ≤ m.withDensity (fun x => ENNReal.ofReal (f i x))) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = m.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∫⁻ x, ‖g x‖ₑ ^ q ∂m) ≤ ∑' i, ∫⁻ x, ‖f i x‖ₑ ^ q ∂m := by
  have hac : ν ≪ m := by
    intro E hE
    have hz : ∀ i, ν (E ∩ S i) = 0 := by
      intro i
      have hi := (hle i).absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
      have hi0 := hi hE
      simpa only [Measure.restrict_apply' (hS i)] using hi0
    have hu : ν (E ∩ ⋃ i, S i) = 0 := by
      rw [inter_iUnion]
      exact measure_iUnion_null hz
    apply measure_mono_null (t := (E ∩ ⋃ i, S i) ∪ (⋃ i, S i)ᶜ)
    · intro x hx
      by_cases hs : x ∈ ⋃ i, S i
      · exact Or.inl ⟨hx, hs⟩
      · exact Or.inr hs
    · exact measure_union_null hu hcover
  obtain ⟨g, hgm, hg0, hgd⟩ := density_of_absolutelyContinuous m ν hac
  have hout : ∀ᵐ x ∂m.restrict (⋃ i, S i)ᶜ, g x = 0 := by
    have hz : ∫⁻ x in (⋃ i, S i)ᶜ, ENNReal.ofReal (g x) ∂m = 0 := by
      rw [← withDensity_apply _ (MeasurableSet.iUnion hS).compl, ← hgd, hcover]
    have hz' := (lintegral_eq_zero_iff' hgm.ennreal_ofReal.aemeasurable.restrict).mp hz
    filter_upwards [hz'] with x hx
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (hg0 x)
  have hpout : ∫⁻ x in (⋃ i, S i)ᶜ, ‖g x‖ₑ ^ q ∂m = 0 := by
    rw [← lintegral_zero (μ := m.restrict (⋃ i, S i)ᶜ)]
    apply lintegral_congr_ae
    filter_upwards [hout] with x hx
    simp only [hx, enorm_zero, ENNReal.zero_rpow_of_pos hq]
  refine ⟨g, hgm, hg0, hgd, ?_⟩
  have hint : ∫⁻ x, ‖g x‖ₑ ^ q ∂m = ∫⁻ x in ⋃ i, S i, ‖g x‖ₑ ^ q ∂m := by
    rw [← lintegral_add_compl _ (MeasurableSet.iUnion hS), hpout, add_zero]
  rw [hint]
  apply (lintegral_iUnion_le S _).trans
  apply ENNReal.tsum_le_tsum
  intro i
  have hn := density_local_norm_le m g (f i) hgm hg0 (hfm i) (hf0 i)
    (S i) (hS i) (ENNReal.ofReal q) (hgd ▸ hle i)
  have hgme := hgm.aestronglyMeasurable (μ := m.restrict (S i))
  have hfme := (hfm i).aestronglyMeasurable (μ := m)
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' hq]
  have he (u : X → ℝ) (μ : Measure X) (hu : AEStronglyMeasurable u μ) :
      eLpNorm u (ENNReal.ofReal q) μ = eLpNorm' u q μ := by
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top hu,
      ENNReal.toReal_ofReal hq.le]
  rw [he g _ hgme, he (f i) _ hfme] at hn
  exact ENNReal.rpow_le_rpow hn hq.le

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
