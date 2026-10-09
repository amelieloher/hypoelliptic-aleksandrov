module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffOperator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic

/-! # Measurability and finite localized source norm for the near-full cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open MeasureTheory Set Parabolic
open scoped ENNReal

/-- The full Borel coefficient and smooth jets give a measurable cutoff operator. -/
theorem measurable_scaledUnitCutoff_backwardOperator {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {A : FullKineticCoefficient d}
    (hA : Measurable (fullKineticCoefficientAt A))
    (P₀ : KineticPoint d) (R ell : ℝ) :
    Measurable (backwardOperator A (scaledUnitCutoff f P₀ R ell)) := by
  have hT := ((continuous_unitCutoffTransport hf).comp
    (continuous_kineticAffineInverse P₀ R)).measurable
  have hH := ((continuous_unitCutoffVelocityHessian hf).comp
    (continuous_kineticAffineInverse P₀ R)).measurable
  have hC : Measurable (fun P => matrixContraction (fullKineticCoefficientAt A P)
      (sliceHessian (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
        (kineticAffineInverse P₀ R P).velocity)) := by
    unfold matrixContraction
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH))
  have h := (measurable_const (a := ell * (R ^ 2)⁻¹)).mul (hT.sub hC)
  convert h using 1
  funext P
  exact scaledUnitCutoff_backwardOperator hf A P₀ P R ell

/-- Smooth tests with a measurable operator have measurable localized sources on open sets. -/
theorem localizedSource_aestronglyMeasurable {d : ℕ} (A : FullKineticCoefficient d)
    {psi u : KineticPoint d → ℝ} {Q : Set (KineticPoint d)} (hQ : IsOpen Q)
    (hpsi : ContinuousOn psi Q) (hu : ContinuousOn u Q)
    (hop : Measurable (backwardOperator A psi)) :
    AEStronglyMeasurable (localizedSource A psi u) (volume.restrict Q) := by
  have hE : MeasurableSet (Q ∩ {P | u P < psi P}) := by
    simpa only [Set.preimage, mem_Ioi, Pi.sub_apply, sub_pos] using
      ((hpsi.sub hu).isOpen_inter_preimage hQ (isOpen_Ioi (a := 0))).measurableSet
  have hm : AEStronglyMeasurable
      ((Q ∩ {P | u P < psi P}).indicator
        (fun P => max (backwardOperator A psi P) 0)) volume :=
    ((hop.max measurable_const).aestronglyMeasurable).indicator hE
  apply hm.restrict.congr
  filter_upwards [ae_restrict_mem hQ.measurableSet] with P hP
  simp only [localizedSource, indicator, mem_inter_iff, mem_ofPred_eq, hP, true_and]

/-- The localized cutoff norm is finite under the proved operator bound. -/
theorem scaledUnitCutoff_source_memLp {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {A : FullKineticCoefficient d}
    (hA : Measurable (fullKineticCoefficientAt A))
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (ell : ℝ)
    {u : KineticPoint d → ℝ} (hu : ContinuousOn u (backwardCylinder P₀ R))
    (p : ℝ≥0∞) (B : ℝ) (hB : 0 ≤ B)
    (hop : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
      |backwardOperator A (scaledUnitCutoff f P₀ R ell) P| ≤ B) :
    MemLp (localizedSource A (scaledUnitCutoff f P₀ R ell) u) p
      (volume.restrict (backwardCylinder P₀ R)) := by
  have hQ := isOpen_backwardCylinder P₀ R hR
  have hpsi := (scaledUnitCutoff_isSmoothNear hf P₀ R ell (backwardCylinder P₀ R)).continuousOn
  have hm := localizedSource_aestronglyMeasurable A hQ hpsi hu
    (measurable_scaledUnitCutoff_backwardOperator hf hA P₀ R ell)
  let : IsFiniteMeasure (volume.restrict (backwardCylinder P₀ R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (volume_backwardCylinder_lt_top P₀ hR)⟩
  apply MemLp.of_bound hm B
  filter_upwards [hop] with P hP
  simp only [localizedSource, indicator]
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (hP.trans' (le_abs_self _)) hB
  · simpa only [norm_zero] using hB

end HypoellipticAleksandrov.KineticAleksandrov.Holder
