module

public import HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm

/-!
# Squared aggregation of proper commutator residuals

This module aggregates the componentwise proper-commutator estimate,
retaining the exact number of active atoms at each derivative index.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

/-- Number of splits of `beta` whose coefficient-side multi-index is nonzero. -/
noncomputable def properSplitCard
    {d M : ℕ} (beta : ParabolicDerivativeIndex d M) : ℕ :=
  Fintype.card
    {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0}

private abbrev ProperSplit {d M : ℕ} (beta : ParabolicDerivativeIndex d M) :=
  {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0}

private abbrev ProperAtom {d M : ℕ} (beta : ParabolicDerivativeIndex d M) :=
  Unit ⊕ ((Fin d × Fin d × ProperSplit beta) ⊕
    ((Fin d × ProperSplit beta) ⊕ ProperSplit beta))

private theorem properAtom_card {d M : ℕ} (beta : ParabolicDerivativeIndex d M) :
    Fintype.card (ProperAtom beta) =
      1 + (d ^ 2 + d + 1) * properSplitCard beta := by
  simp only [ProperAtom, properSplitCard, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_prod, Fintype.card_fin]
  ring

private theorem sum_dite_eq_sum_proper
    {d M : ℕ} (beta : ParabolicDerivativeIndex d M)
    (f : (gamma : TimeVelocityMultiIndex.Split beta.1) → gamma.left ≠ 0 → ℝ) :
    (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then f gamma hproper else 0) =
      ∑ gamma : ProperSplit beta, f gamma.1 gamma.2 := by
  classical
  calc
    _ = (∑ gamma : ProperSplit beta,
          if hproper : gamma.1.left ≠ 0 then f gamma.1 hproper else 0) +
        ∑ gamma : {gamma : TimeVelocityMultiIndex.Split beta.1 //
            ¬ gamma.left ≠ 0},
          if hproper : gamma.1.left ≠ 0 then f gamma.1 hproper else 0 :=
      (Fintype.sum_subtype_add_sum_subtype
        (fun gamma : TimeVelocityMultiIndex.Split beta.1 => gamma.left ≠ 0)
        (fun gamma => if hproper : gamma.left ≠ 0 then f gamma hproper else 0)).symm
    _ = _ := by
      have hzero :
          (∑ gamma : {gamma : TimeVelocityMultiIndex.Split beta.1 //
              ¬ gamma.left ≠ 0},
            if hproper : gamma.1.left ≠ 0 then f gamma.1 hproper else 0) = 0 :=
        Finset.sum_eq_zero fun gamma _ => dif_neg gamma.2
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl ?_
      intro gamma hgamma
      exact dif_pos gamma.2

private theorem properAtom_nonneg
    {d M : ℕ} {beta : ParabolicDerivativeIndex d M}
    (E0 : ℝ)
    (A : Fin d → Fin d → ProperSplit beta → ℝ)
    (B : Fin d → ProperSplit beta → ℝ)
    (C : ProperSplit beta → ℝ)
    (hE0 : 0 ≤ E0) (hA : ∀ i j gamma, 0 ≤ A i j gamma)
    (hB : ∀ j gamma, 0 ≤ B j gamma) (hC : ∀ gamma, 0 ≤ C gamma) :
    ∀ atom : ProperAtom beta,
      0 ≤ Sum.elim (fun _ : Unit => E0)
        (Sum.elim (fun p => A p.1 p.2.1 p.2.2)
          (Sum.elim (fun p => B p.1 p.2) C)) atom := by
  intro atom
  rcases atom with (_ | atom)
  · exact hE0
  · rcases atom with (p | atom)
    · exact hA p.1 p.2.1 p.2.2
    · rcases atom with (p | gamma)
      · exact hB p.1 p.2
      · exact hC gamma

/-- Summed squared `L²` control of all proper commutator residuals, retaining
the exact number of active atoms at each derivative index. -/
theorem properDifferentiatedScalarCommutatorResidual_memLp_and_sum_sq_le
    {d M : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (u : TimeVelocity d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d => c z.1 z.2) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) :
    (∀ beta : ParabolicDerivativeIndex d M,
      ParabolicMemLpOn U 2
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)) ∧
    (∑ beta : ParabolicDerivativeIndex d M,
      (ENNReal.toReal (eLpNorm
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)
        2 (timeVelocityVolumeOn U))) ^ 2) ≤
      ∑ beta : ParabolicDerivativeIndex d M,
        ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ) *
          ((ENNReal.toReal (eLpNorm (E.representative beta) 2
            (timeVelocityVolumeOn U))) ^ 2 +
          (∑ i, ∑ j,
            ∑ gamma :
                {gamma : TimeVelocityMultiIndex.Split beta.1 //
                  gamma.left ≠ 0},
              ((beta.1.choose gamma.1.left : ℝ) *
                Ba i j
                  (ParabolicDerivativeIndex.splitLeft beta gamma.1) *
                ENNReal.toReal (eLpNorm
                  (D.representative
                    (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                      beta gamma.1 gamma.2 j i))
                  2 (timeVelocityVolumeOn U))) ^ 2) +
          (∑ j,
            ∑ gamma :
                {gamma : TimeVelocityMultiIndex.Split beta.1 //
                  gamma.left ≠ 0},
              ((beta.1.choose gamma.1.left : ℝ) *
                Bb j
                  (ParabolicDerivativeIndex.splitLeft beta gamma.1) *
                ENNReal.toReal (eLpNorm
                  (D.representative
                    (ParabolicDerivativeIndex.properSplitRightVelocity
                      beta gamma.1 gamma.2 j))
                  2 (timeVelocityVolumeOn U))) ^ 2) +
          (∑ gamma :
              {gamma : TimeVelocityMultiIndex.Split beta.1 //
                gamma.left ≠ 0},
            ((beta.1.choose gamma.1.left : ℝ) *
              Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1) *
              ENNReal.toReal (eLpNorm
                (D.representative
                  (ParabolicDerivativeIndex.properSplitRightValue
                    beta gamma.1 gamma.2))
                2 (timeVelocityVolumeOn U))) ^ 2)) := by
  classical
  have hcomponent (beta : ParabolicDerivativeIndex d M) :=
    properDifferentiatedScalarCommutatorResidual_memLp_and_eLpNorm_toReal_le
      U hU a b c u F D E Ba Bb Bc hBa hBb hBc ha hb hc
      haBound hbBound hcBound beta
  refine ⟨fun beta => (hcomponent beta).1, ?_⟩
  apply Finset.sum_le_sum
  intro beta hbeta
  let E0 : ℝ := ENNReal.toReal
    (eLpNorm (E.representative beta) 2 (timeVelocityVolumeOn U))
  let A : Fin d → Fin d → ProperSplit beta → ℝ := fun i j gamma =>
    (beta.1.choose gamma.1.left : ℝ) *
      Ba i j (ParabolicDerivativeIndex.splitLeft beta gamma.1) *
      ENNReal.toReal (eLpNorm
        (D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocityTwo
            beta gamma.1 gamma.2 j i)) 2 (timeVelocityVolumeOn U))
  let B : Fin d → ProperSplit beta → ℝ := fun j gamma =>
    (beta.1.choose gamma.1.left : ℝ) *
      Bb j (ParabolicDerivativeIndex.splitLeft beta gamma.1) *
      ENNReal.toReal (eLpNorm
        (D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity
            beta gamma.1 gamma.2 j)) 2 (timeVelocityVolumeOn U))
  let C : ProperSplit beta → ℝ := fun gamma =>
    (beta.1.choose gamma.1.left : ℝ) *
      Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1) *
      ENNReal.toReal (eLpNorm
        (D.representative
          (ParabolicDerivativeIndex.properSplitRightValue
            beta gamma.1 gamma.2)) 2 (timeVelocityVolumeOn U))
  let atomValue : ProperAtom beta → ℝ :=
    Sum.elim (fun _ : Unit => E0)
      (Sum.elim (fun p => A p.1 p.2.1 p.2.2)
        (Sum.elim (fun p => B p.1 p.2) C))
  have hA_nonneg : ∀ i j gamma, 0 ≤ A i j gamma := by
    intro i j gamma
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hBa _ _ _))
      ENNReal.toReal_nonneg
  have hB_nonneg : ∀ j gamma, 0 ≤ B j gamma := by
    intro j gamma
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hBb _ _))
      ENNReal.toReal_nonneg
  have hC_nonneg : ∀ gamma, 0 ≤ C gamma := by
    intro gamma
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hBc _))
      ENNReal.toReal_nonneg
  have hatom_nonneg : ∀ atom, 0 ≤ atomValue atom :=
    properAtom_nonneg E0 A B C ENNReal.toReal_nonneg
      hA_nonneg hB_nonneg hC_nonneg
  have hcomponent' :
      ENNReal.toReal (eLpNorm
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)
        2 (timeVelocityVolumeOn U)) ≤ ∑ atom, atomValue atom := by
    calc
      _ ≤ E0 +
          (∑ i, ∑ j, ∑ gamma : ProperSplit beta, A i j gamma) +
          (∑ j, ∑ gamma : ProperSplit beta, B j gamma) +
          ∑ gamma : ProperSplit beta, C gamma := by
        simpa only [E0, A, B, C, sum_dite_eq_sum_proper] using (hcomponent beta).2
      _ = ∑ atom, atomValue atom := by
        simp [atomValue, ProperAtom, Fintype.sum_prod_type]
        ring
  have hsum_nonneg : 0 ≤ ∑ atom, atomValue atom :=
    Finset.sum_nonneg fun atom _ => hatom_nonneg atom
  calc
    (ENNReal.toReal (eLpNorm
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)
        2 (timeVelocityVolumeOn U))) ^ 2 ≤ (∑ atom, atomValue atom) ^ 2 := by
      nlinarith [ENNReal.toReal_nonneg (a := eLpNorm
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)
        2 (timeVelocityVolumeOn U))]
    _ ≤ (Fintype.card (ProperAtom beta) : ℝ) *
        ∑ atom, (atomValue atom) ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := atomValue))
    _ = _ := by
      rw [properAtom_card]
      congr 1
      simp [atomValue, ProperAtom, E0, A, B, C, Fintype.sum_prod_type]
      ring

end HypoellipticAleksandrov.Parabolic
