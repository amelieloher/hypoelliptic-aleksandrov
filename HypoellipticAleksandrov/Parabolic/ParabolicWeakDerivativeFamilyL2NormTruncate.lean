module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm

/-!
# Squared L2 energy under weak-derivative-family truncation
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open MeasureTheory
open scoped BigOperators ENNReal

private def castLEEmbedding {d M L : ℕ} (hML : M ≤ L) :
    ParabolicDerivativeIndex d M ↪ ParabolicDerivativeIndex d L where
  toFun := ParabolicDerivativeIndex.castLE hML
  inj' := by
    intro beta gamma h
    apply Subtype.ext
    exact congrArg
      (fun delta : ParabolicDerivativeIndex d L ↦ delta.1) h

/-- Truncating the parabolic weight bound cannot increase the squared
finite-family `L²` norm. -/
theorem squaredL2Norm_truncate_le
    {d M L : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (hML : M ≤ L) :
    squaredL2Norm (F.truncate hML) ≤ squaredL2Norm F := by
  classical
  unfold squaredL2Norm
  let e : ParabolicDerivativeIndex d M ↪ ParabolicDerivativeIndex d L :=
    castLEEmbedding hML
  let component : ParabolicDerivativeIndex d L → ℝ := fun beta ↦
    (ENNReal.toReal
      (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U))) ^ 2
  calc
    ∑ beta : ParabolicDerivativeIndex d M,
        (ENNReal.toReal
          (eLpNorm ((F.truncate hML).representative beta) 2
            (timeVelocityVolumeOn U))) ^ 2 =
        ∑ beta ∈ Finset.univ.map e, component beta := by
          rw [Finset.sum_map]
          rfl
    _ ≤ ∑ beta ∈ Finset.univ, component beta := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro beta _ _
        exact sq_nonneg _
    _ = ∑ beta : ParabolicDerivativeIndex d L,
        (ENNReal.toReal
          (eLpNorm (F.representative beta) 2
            (timeVelocityVolumeOn U))) ^ 2 := rfl

end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
