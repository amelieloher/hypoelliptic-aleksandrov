module

public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Globalization of compactly supported weak derivatives

Raw weak derivative relations globalize when the exact representatives have
topological support inside an open carrier. Restricted `Lᵖ` membership has a
corresponding pointwise-support globalization.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory
open Set
open scoped ENNReal Topology

private theorem value_eq_zero_of_not_mem_tsupport
    {X E : Type*} [TopologicalSpace X] [Zero E] {f : X → E} {x : X}
    (hx : x ∉ tsupport f) : f x = 0 := by
  by_contra hzero
  exact hx (subset_closure (Function.mem_support.mpr hzero))

private theorem weakFDerivApply_univ_of_tsupport_subset
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {u du : TimeVelocity d → ℝ} (q : TimeVelocity d)
    (h : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, u z * fderiv ℝ φ z q ∂(volume : Measure (TimeVelocity d))) =
        -∫ z in U, du z * φ z ∂(volume : Measure (TimeVelocity d)))
    (hu : tsupport u ⊆ U) (hdu : tsupport du ⊆ U) :
    ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Set.univ →
      (∫ z in Set.univ, u z * fderiv ℝ φ z q
        ∂(volume : Measure (TimeVelocity d))) =
        -∫ z in Set.univ, du z * φ z ∂(volume : Measure (TimeVelocity d)) := by
  intro φ hφ hφCompact _
  let K : Set (TimeVelocity d) :=
    (tsupport u ∪ tsupport du) ∩ tsupport φ
  have hKCompact : IsCompact K := by
    exact hφCompact.isCompact.of_isClosed_subset
      ((isClosed_closure.union isClosed_closure).inter isClosed_closure)
      inter_subset_right
  have hKU : K ⊆ U := by
    rintro z ⟨hz, -⟩
    exact hz.elim (fun hzu => hu hzu) (fun hzdu => hdu hzdu)
  obtain ⟨δ, hδ, b, hb, hbCompact, hbU, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset hU hKCompact hKU
  let ψ : TimeVelocity d → ℝ := b * φ
  have hψSmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hb.mul hφ
  have hψCompact : HasCompactSupport ψ := by
    simpa only [ψ] using hφCompact.mul_left (f := b)
  have hψU : tsupport ψ ⊆ U :=
    (tsupport_mul_subset_left (f := b) (g := φ)).trans hbU
  have hbFDerivZero {z : TimeVelocity d} (hz : z ∈ K) : fderiv ℝ b z = 0 := by
    have hlocal : b =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
      apply hbOne
      exact Metric.mem_cthickening_of_dist_le y z δ K hz (le_of_lt hy)
    rw [hlocal.fderiv_eq]
    simp
  have hleftPoint (z : TimeVelocity d) :
      u z * fderiv ℝ ψ z q = u z * fderiv ℝ φ z q := by
    by_cases huz : u z = 0
    · simp [huz]
    have hzu : z ∈ tsupport u := subset_tsupport u (by simpa [Function.mem_support])
    rw [show fderiv ℝ ψ z = fderiv ℝ (b * φ) z by rfl,
      fderiv_mul (x := z) (hb.contDiffAt.differentiableAt (by simp))
        (hφ.contDiffAt.differentiableAt (by simp))]
    by_cases hzφ : z ∈ tsupport φ
    · have hzK : z ∈ K := ⟨Or.inl hzu, hzφ⟩
      have hbz : b z = 1 := hbOne (Metric.self_subset_cthickening K hzK)
      have hdb : fderiv ℝ b z = 0 := hbFDerivZero hzK
      simp [hbz, hdb]
    · have hdφ : fderiv ℝ φ z = 0 := by
        apply value_eq_zero_of_not_mem_tsupport
        exact fun hzderiv => hzφ ((tsupport_fderiv_subset ℝ) hzderiv)
      have hφz : φ z = 0 := value_eq_zero_of_not_mem_tsupport hzφ
      simp [hdφ, hφz]
  have hrightPoint (z : TimeVelocity d) : du z * ψ z = du z * φ z := by
    by_cases hduz : du z = 0
    · simp [hduz]
    by_cases hφz : φ z = 0
    · simp [ψ, hφz]
    have hzdu : z ∈ tsupport du := subset_tsupport du (by simpa [Function.mem_support])
    have hzφ : z ∈ tsupport φ := subset_tsupport φ (by simpa [Function.mem_support])
    have hzK : z ∈ K := ⟨Or.inr hzdu, hzφ⟩
    have hbz : b z = 1 := hbOne (Metric.self_subset_cthickening K hzK)
    simp [ψ, hbz]
  have hweak := h ψ hψSmooth hψCompact hψU
  have hleftRestrict :
      (∫ z in U, u z * fderiv ℝ ψ z q ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in U, u z * fderiv ℝ φ z q
          ∂(volume : Measure (TimeVelocity d)) := by
    exact integral_congr_ae (Eventually.of_forall hleftPoint)
  have hrightRestrict :
      (∫ z in U, du z * ψ z ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in U, du z * φ z ∂(volume : Measure (TimeVelocity d)) := by
    exact integral_congr_ae (Eventually.of_forall hrightPoint)
  have hleftUniv :
      (∫ z in Set.univ, u z * fderiv ℝ φ z q
        ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in U, u z * fderiv ℝ φ z q
          ∂(volume : Measure (TimeVelocity d)) := by
    rw [setIntegral_univ, ← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp [hz]
      · have huz : u z = 0 := by
          apply value_eq_zero_of_not_mem_tsupport
          exact fun hzts => hz (hu hzts)
        simp [hz, huz]
  have hrightUniv :
      (∫ z in Set.univ, du z * φ z ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in U, du z * φ z ∂(volume : Measure (TimeVelocity d)) := by
    rw [setIntegral_univ, ← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp [hz]
      · have hduz : du z = 0 := by
          apply value_eq_zero_of_not_mem_tsupport
          exact fun hzts => hz (hdu hzts)
        simp [hz, hduz]
  rw [hleftUniv, hrightUniv, ← hleftRestrict, ← hrightRestrict]
  exact hweak

/-- A raw weak time derivative whose topological supports lie in an open
carrier is
also the ambient raw weak time derivative. -/
theorem HasWeakTimeDerivOn.univ_of_tsupport_subset
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {u du : TimeVelocity d → ℝ}
    (h : HasWeakTimeDerivOn U u du)
    (hu : tsupport u ⊆ U)
    (hdu : tsupport du ⊆ U) :
    HasWeakTimeDerivOn Set.univ u du := by
  exact weakFDerivApply_univ_of_tsupport_subset hU (1, 0) h hu hdu

/-- A raw weak velocity derivative whose topological supports lie in an open
carrier is also the ambient raw weak velocity derivative. -/
theorem HasWeakVelocityPartialDerivOn.univ_of_tsupport_subset
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {i : Fin d} {u dui : TimeVelocity d → ℝ}
    (h : HasWeakVelocityPartialDerivOn U i u dui)
    (hu : tsupport u ⊆ U)
    (hdui : tsupport dui ⊆ U) :
    HasWeakVelocityPartialDerivOn Set.univ i u dui := by
  exact weakFDerivApply_univ_of_tsupport_subset hU (0, Pi.single i 1) h hu hdui

/-- Restricted `Lᵖ` membership globalizes when the selected representative
vanishes pointwise off the measurable carrier. -/
theorem ParabolicMemLpOn.memLp_of_support_subset
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : MeasurableSet U)
    {p : ℝ≥0∞} {f : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn U p f)
    (hsupp : Function.support f ⊆ U) :
    MeasureTheory.MemLp f p
      (volume : Measure (TimeVelocity d)) := by
  have hindicator : U.indicator f = f := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · have hfz : f z = 0 := by
        by_contra hfz
        exact hz (hsupp (by simpa [Function.mem_support]))
      simp [hz, hfz]
  rw [← hindicator]
  exact (memLp_indicator_iff_restrict hU).2 hf

end HypoellipticAleksandrov.Parabolic
