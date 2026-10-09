module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel
import Mathlib.Topology.Order.Compact

/-! # Uniform Duhamel bounds for sources with a finite time support window -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set

/-- Source-time integration vanishes outside the source's time support window. -/
theorem duhamelIntegrand_eq_zero_of_time_not_mem {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (a b : ℝ) (hgt : ∀ p, p.time ∉ Icc a b → g p = 0)
    (p : KineticPoint d) (r : ℝ) (hr : r ∉ Icc a b) :
    duhamelIntegrand K g p r = 0 := by
  unfold duhamelIntegrand
  split
  · unfold duhamelSourceIntegral
    have hf : (fun w : EvolutionAmbientState d => g ⟨r, w.1, w.2⟩) = 0 := by
      funext w
      exact hgt ⟨r, w.1, w.2⟩ hr
    rw [hf]
    exact integral_zero' _ _
  · rfl

/-- A finite source time window gives a uniform bound on the entire Duhamel potential. -/
theorem duhamelPotential_le_time_window {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ p, g p ≤ C)
    (a b : ℝ) (hab : a ≤ b) (hgt : ∀ p, p.time ∉ Icc a b → g p = 0)
    (p : KineticPoint d) : duhamelPotential K τplus g p ≤ (b - a) * C := by
  let f : ℝ → ℝ := (Icc a b).indicator (fun _ => C)
  have hf : Integrable f :=
    (integrableOn_const (C := C) (s := Icc a b)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hfn : ∀ r, 0 ≤ f r := by
    intro r
    exact indicator_nonneg (fun _ _ => hC) r
  have hn : ∀ r, ‖duhamelIntegrand K g p r‖ ≤ f r := by
    intro r
    by_cases hr : r ∈ Icc a b
    · rw [Real.norm_eq_abs, abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
      exact (duhamelIntegrand_le K g hgn C hC hgb p r).trans_eq
        (indicator_of_mem hr (fun _ => C)).symm
    · rw [duhamelIntegrand_eq_zero_of_time_not_mem K g a b hgt p r hr]
      simp only [norm_zero, f, indicator_of_notMem hr, le_refl]
  have hnorm := norm_integral_le_of_norm_le
    (μ := volume.restrict (Ioc p.time τplus)) (f := duhamelIntegrand K g p)
    (hf.mono_measure Measure.restrict_le_self) (Filter.Eventually.of_forall hn)
  have hnon : 0 ≤ duhamelPotential K τplus g p :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hgn p r)
  calc
    duhamelPotential K τplus g p ≤ ∫ r in Ioc p.time τplus, f r := by
      change |duhamelPotential K τplus g p| ≤ _ at hnorm
      rwa [abs_of_nonneg hnon] at hnorm
    _ ≤ ∫ r, f r := integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hfn) hf
    _ = (b - a) * C := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const]
      simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
        smul_eq_mul]

/-- Compact spacetime support is contained in a finite absolute-time window. -/
theorem exists_time_window_of_hasCompactSupport {d : ℕ}
    (g : KineticPoint d → ℝ) (hg : HasCompactSupport g) :
    ∃ a b : ℝ, a ≤ b ∧ ∀ p, p.time ∉ Icc a b → g p = 0 := by
  have ht := hg.image continuous_time
  obtain ⟨a, ha⟩ := ht.bddBelow
  obtain ⟨b, hb⟩ := ht.bddAbove
  refine ⟨min a b, max a b, min_le_max, ?_⟩
  intro p hp
  apply image_eq_zero_of_notMem_tsupport
  intro hpg
  apply hp
  have hpt : p.time ∈ KineticPoint.time '' tsupport g := ⟨p, hpg, rfl⟩
  exact ⟨(min_le_left a b).trans (ha hpt), (hb hpt).trans (le_max_right a b)⟩

/-- Continuous compact nonnegative sources give a globally bounded Duhamel potential. -/
theorem duhamelPotential_exists_bound {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ p, 0 ≤ g p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |duhamelPotential K τplus g p| ≤ C := by
  obtain ⟨C, hC⟩ := hg.bddAbove_range_of_hasCompactSupport hgc
  obtain ⟨a, b, hab, hgt⟩ := exists_time_window_of_hasCompactSupport g hgc
  refine ⟨(b - a) * max C 0, mul_nonneg (sub_nonneg.mpr hab) (le_max_right C 0), ?_⟩
  intro p
  have hnon : 0 ≤ duhamelPotential K τplus g p :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hgn p r)
  rw [abs_of_nonneg hnon]
  exact duhamelPotential_le_time_window K τplus g hgn (max C 0) (le_max_right C 0)
    (fun q => (hC (mem_range_self q)).trans (le_max_left C 0)) a b hab hgt p

/-- The source potential is bounded Borel for continuous compact nonnegative sources. -/
theorem duhamelPotential_boundedBorel {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (hγ : Continuous γ) (τplus : ℝ) (g : KineticPoint d → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgn : ∀ p, 0 ≤ g p) :
    Measurable (duhamelPotential K τplus g) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |duhamelPotential K τplus g p| ≤ C :=
  ⟨measurable_duhamelPotential K hΩ hγ τplus g hg.measurable,
    duhamelPotential_exists_bound K τplus g hg hgc hgn⟩

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
