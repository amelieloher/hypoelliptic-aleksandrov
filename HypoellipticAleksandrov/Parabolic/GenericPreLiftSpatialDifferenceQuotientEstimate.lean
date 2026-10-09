module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquation
public import HypoellipticAleksandrov.Parabolic.ProperCommutatorSquaredAggregation
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedCore
public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm

/-!
# Generic pre-lift spatial difference-quotient estimate

This module assembles the differentiated pre-lift equation into the fixed
divergence-form difference-quotient estimate.  The private residual API below
keeps the literal proper commutator, coefficient-gradient, drift-gradient,
and zeroth-order terms in one finite `L²` sum.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal MatrixOrder

private def singletonCoefficientIndex {d M : ℕ} (hM : 1 ≤ M) (i : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.castLE (by omega)
    (ParabolicDerivativeIndex.velocityOne i)

private def diffusionGradientMajorant
    {d M : ℕ} (hM : 1 ≤ M)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ) : ℝ :=
  ∑ k, ∑ i, ∑ j, Ba i j (singletonCoefficientIndex hM k)

private theorem singletonCoefficientIndex_coe
    {d M : ℕ} (hM : 1 ≤ M) (i : Fin d) :
    (singletonCoefficientIndex hM i).1 = Pi.single (velocityCoord i) 1 := by
  funext c
  rcases c with _ | k
  · change 0 = 0
    rfl
  · change Function.update (0 : Fin d → ℕ) i 1 k =
      (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr k)
    by_cases hik : i = k
    · subst k
      simp
    · simp [Function.update, Ne.symm hik]

private def driftValueMajorant
    {d M : ℕ} (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  ∑ j, Bb j (ParabolicDerivativeIndex.zero d M)

private def potentialValueMajorant
    {d M : ℕ} (Bc : ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  Bc (ParabolicDerivativeIndex.zero d M)

private theorem diffusionGradientMajorant_nonneg
    {d M : ℕ} (hM : 1 ≤ M)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha) :
    0 ≤ diffusionGradientMajorant hM Ba := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => hBa j k (singletonCoefficientIndex hM i)

private theorem driftValueMajorant_nonneg
    {d M : ℕ} (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha) :
    0 ≤ driftValueMajorant Bb := by
  exact Finset.sum_nonneg fun j _ => hBb j (ParabolicDerivativeIndex.zero d M)

private theorem potentialValueMajorant_nonneg
    {d M : ℕ} (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBc : ∀ alpha, 0 ≤ Bc alpha) :
    0 ≤ potentialValueMajorant Bc :=
  hBc (ParabolicDerivativeIndex.zero d M)

private theorem diffusionGradient_abs_le_majorant
    {d M : ℕ} {U : Set (TimeVelocity d)} (hM : 1 ≤ M)
    (a : CoefficientField d)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha) :
    ∀ i j k z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM k).1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤
        diffusionGradientMajorant hM Ba := by
  intro i j k z hz
  have hij : Ba i j (singletonCoefficientIndex hM k) ≤
      ∑ l, Ba i l (singletonCoefficientIndex hM k) :=
    Finset.single_le_sum (fun l _ => hBa i l _) (Finset.mem_univ j)
  have hi : (∑ l, Ba i l (singletonCoefficientIndex hM k)) ≤
      ∑ r, ∑ l, Ba r l (singletonCoefficientIndex hM k) := by
    exact Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg fun l _ => hBa r l _) (Finset.mem_univ i)
  have hk : (∑ r, ∑ l, Ba r l (singletonCoefficientIndex hM k)) ≤
      diffusionGradientMajorant hM Ba := by
    unfold diffusionGradientMajorant
    exact Finset.single_le_sum
      (fun s _ => Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun l _ =>
        hBa r l (singletonCoefficientIndex hM s)) (Finset.mem_univ k)
  exact (haBound i j (singletonCoefficientIndex hM k) z hz).trans
    (hij.trans (hi.trans hk))

private theorem spatialPartial_coefficient_eq_singletonDerivative
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) (hM : 1 ≤ M)
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U) :
    ∀ k i j z, z ∈ U →
      spatialPartial k (fun y => a z.1 y i j) z.2 =
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (singletonCoefficientIndex hM k).1
          (fun x : TimeVelocity d => a x.1 x.2 i j) z := by
  intro k i j z hz
  have hadd := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex d) (velocityCoord k)
    (fun x : TimeVelocity d => a x.1 x.2 i j) z
    (by
      have hregular := (ha i j).contDiffAt (hU.mem_nhds hz)
      apply hregular.of_le
      simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
        TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order])
  simp only [zero_add, timeVelocityBasis_velocity] at hadd
  rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex d) (fun x : TimeVelocity d => a x.1 x.2 i j) =
        (fun x : TimeVelocity d => a x.1 x.2 i j) by
    funext x
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero _ _] at hadd
  rw [singletonCoefficientIndex_coe hM k, hadd]
  unfold spatialPartial
  have hdiff := ((ha i j).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by norm_num)
  have hslice : HasFDerivAt (fun y : PDE.Vec d => a z.1 y i j)
      ((fderiv ℝ (fun x : TimeVelocity d => a x.1 x.2 i j) z).comp
        (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 := by
    simpa only [Function.comp_def] using! hdiff.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [hslice.fderiv]
  rfl

private theorem spatialPartial_coefficient_abs_le_majorant
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) (hM : 1 ≤ M)
    (a : CoefficientField d)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha) :
    ∀ i j k z, z ∈ U →
      |spatialPartial k (fun y => a z.1 y i j) z.2| ≤
        diffusionGradientMajorant hM Ba := by
  intro i j k z hz
  rw [spatialPartial_coefficient_eq_singletonDerivative hU hM a ha k i j z hz]
  exact diffusionGradient_abs_le_majorant hM a Ba hBa haBound i j k z hz

private theorem driftValue_abs_le_majorant
    {d M : ℕ} {U : Set (TimeVelocity d)}
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha) :
    ∀ j z, z ∈ U → |b z.1 z.2 j| ≤ driftValueMajorant Bb := by
  intro j z hz
  have hj : Bb j (ParabolicDerivativeIndex.zero d M) ≤
      driftValueMajorant Bb := by
    unfold driftValueMajorant
    exact Finset.single_le_sum
      (fun k _ => hBb k (ParabolicDerivativeIndex.zero d M))
      (Finset.mem_univ j)
  have hv : |b z.1 z.2 j| ≤ Bb j (ParabolicDerivativeIndex.zero d M) := by
    simpa using hbBound j (ParabolicDerivativeIndex.zero d M) z hz
  exact hv.trans hj

private theorem potentialValue_abs_le_majorant
    {d M : ℕ} {U : Set (TimeVelocity d)}
    (c : ℝ → PDE.Vec d → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) :
    ∀ z, z ∈ U → |c z.1 z.2| ≤ potentialValueMajorant Bc := by
  intro z hz
  simpa [potentialValueMajorant] using
    hcBound (ParabolicDerivativeIndex.zero d M) z hz

private theorem singletonCoefficientDerivative_continuousOn
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) (hM : 1 ≤ M)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ (M + 1) q U)
    (i : Fin d) :
    ContinuousOn (TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (singletonCoefficientIndex hM i).1 q) U := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have horder : (singletonCoefficientIndex hM i).1.order ≤ M + 1 := by
    calc
      _ ≤ (singletonCoefficientIndex hM i).1.parabolicWeight := by
        simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.parabolicWeight,
          TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
          VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order]
        omega
      _ ≤ M + 1 := (singletonCoefficientIndex hM i).2
  have hi := (hq.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right
    (m := 0) (i := (singletonCoefficientIndex hM i).1.coordinateList.length)
    (by
      rw [TimeVelocityMultiIndex.length_coordinateList, zero_add]
      exact_mod_cast horder)
  exact (contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun k ↦ timeVelocityBasis
      ((singletonCoefficientIndex hM i).1.coordinateList.get k)))).clm_apply hi
    |>.continuousAt

private theorem diffusionGradient_aestronglyMeasurable
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U) (hM : 1 ≤ M)
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U) (i j : Fin d) :
    AEStronglyMeasurable
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM i).1
        (fun z : TimeVelocity d => a z.1 z.2 i j))
      (timeVelocityVolumeOn U) := by
  exact (singletonCoefficientDerivative_continuousOn hU hM _ (ha i j) i)
    |>.aestronglyMeasurable hU.measurableSet

private theorem driftValue_aestronglyMeasurable
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U) (j : Fin d) :
    AEStronglyMeasurable (fun z : TimeVelocity d => b z.1 z.2 j)
      (timeVelocityVolumeOn U) :=
  (hb j).continuousOn.aestronglyMeasurable hU.measurableSet

private theorem potentialValue_aestronglyMeasurable
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (c : ℝ → PDE.Vec d → ℝ)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) U) :
    AEStronglyMeasurable (fun z : TimeVelocity d => c z.1 z.2)
      (timeVelocityVolumeOn U) :=
  hc.continuousOn.aestronglyMeasurable hU.measurableSet

private noncomputable def properResidualCoarseConstant
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  ∑ beta : ParabolicDerivativeIndex d M,
    ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ) *
      (1 +
        (∑ i, ∑ j, ∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Ba i j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2) +
        (∑ j, ∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Bb j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2) +
        (∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2))

private theorem properResidualCoarseConstant_nonneg
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) :
    0 ≤ properResidualCoarseConstant Ba Bb Bc := by
  unfold properResidualCoarseConstant
  exact Finset.sum_nonneg fun beta _ => mul_nonneg (by positivity) (by positivity)

private theorem properResidual_memLp_and_sum_sq_le_coarse
    {d M : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ)
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
    (ha : ∀ i j, ContDiffOn ℝ M (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) :
    (∀ beta : ParabolicDerivativeIndex d M, ParabolicMemLpOn U 2
      (properDifferentiatedScalarCommutatorResidual a b c D E beta)) ∧
    (∑ beta : ParabolicDerivativeIndex d M,
      (ENNReal.toReal (eLpNorm
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)
        2 (timeVelocityVolumeOn U))) ^ 2) ≤
      properResidualCoarseConstant Ba Bb Bc *
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
  classical
  obtain ⟨hmem, hsum⟩ :=
    properDifferentiatedScalarCommutatorResidual_memLp_and_sum_sq_le
      U hU a b c u F D E Ba Bb Bc hBa hBb hBc ha hb hc
        haBound hbBound hcBound
  refine ⟨hmem, hsum.trans ?_⟩
  unfold properResidualCoarseConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro beta hbeta
  have hD := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D
  have hE := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
  have htotal : 0 ≤ ParabolicWeakDerivativeFamily.squaredL2Norm D +
      ParabolicWeakDerivativeFamily.squaredL2Norm E := add_nonneg hD hE
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E) +
        (∑ i, ∑ j, ∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Ba i j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2 *
              (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E)) +
        (∑ j, ∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Bb j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2 *
              (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E)) +
        (∑ gamma :
            {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
          ((beta.1.choose gamma.1.left : ℝ) *
            Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2 *
              (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E)) := by
      gcongr
      · exact (ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm E beta).trans
          (le_add_of_nonneg_left hD)
      ·
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          ((ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _).trans
            (le_add_of_nonneg_right hE)) (sq_nonneg _)
      ·
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          ((ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _).trans
            (le_add_of_nonneg_right hE)) (sq_nonneg _)
      ·
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          ((ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _).trans
            (le_add_of_nonneg_right hE)) (sq_nonneg _)
    _ = _ := by
      simp_rw [add_mul, Finset.sum_mul]
      ring

private def preliftValueIndex {d M : ℕ}
    (beta : ParabolicDerivativeIndex d M) : ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta

private def preliftGradientIndex {d M : ℕ}
    (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.velocitySucc (preliftValueIndex beta) j (by
    change beta.1.parabolicWeight + 1 ≤ M + 1
    omega)

private theorem preliftValue_component_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (beta : ParabolicDerivativeIndex d M) :
    (ENNReal.toReal (eLpNorm (D.representative (preliftValueIndex beta)) 2
      (timeVelocityVolumeOn U))) ^ 2 ≤
      ParabolicWeakDerivativeFamily.squaredL2Norm D :=
  ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _

private theorem preliftGradient_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (beta : ParabolicDerivativeIndex d M) :
    (∑ j : Fin d, (ENNReal.toReal (eLpNorm
      (D.representative (preliftGradientIndex beta j)) 2
      (timeVelocityVolumeOn U))) ^ 2) ≤
      (d : ℝ) * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _j : Fin d, ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun j _ =>
        ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _
    _ = _ := by simp

private theorem preliftGradient_double_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (beta : ParabolicDerivativeIndex d M) :
    (∑ _i : Fin d, ∑ j : Fin d, (ENNReal.toReal (eLpNorm
      (D.representative (preliftGradientIndex beta j)) 2
      (timeVelocityVolumeOn U))) ^ 2) ≤
      (d : ℝ) ^ 2 * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _i : Fin d,
        (d : ℝ) * ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun _ _ => preliftGradient_component_sum_sq_le D beta
    _ = _ := by simp; ring

private theorem allPreliftValue_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u) :
    (∑ beta : ParabolicDerivativeIndex d M,
      (ENNReal.toReal (eLpNorm (D.representative (preliftValueIndex beta)) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
        ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _beta : ParabolicDerivativeIndex d M,
        ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun beta _ => preliftValue_component_sq_le D beta
    _ = _ := by simp

private theorem allPreliftGradient_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u) :
    (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d,
      (ENNReal.toReal (eLpNorm (D.representative (preliftGradientIndex beta j)) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) *
        ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _beta : ParabolicDerivativeIndex d M,
        (d : ℝ) * ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun beta _ => preliftGradient_component_sum_sq_le D beta
    _ = _ := by simp; ring

private theorem allPreliftGradient_double_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u) :
    (∑ beta : ParabolicDerivativeIndex d M, ∑ _i : Fin d, ∑ j : Fin d,
      (ENNReal.toReal (eLpNorm (D.representative (preliftGradientIndex beta j)) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) ^ 2 *
        ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _beta : ParabolicDerivativeIndex d M,
        (d : ℝ) ^ 2 * ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun beta _ =>
        preliftGradient_double_component_sum_sq_le D beta
    _ = _ := by simp; ring

private abbrev FullResidualTermIndex (d : ℕ) :=
  Unit ⊕ ((Fin d × Fin d) ⊕ (Fin d ⊕ Unit))

private def genericPreliftFullResidualTerm
    {d : ℕ} (Rproper : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ) :
    FullResidualTermIndex d → TimeVelocity d → ℝ
  | Sum.inl _ => Rproper
  | Sum.inr (Sum.inl (i, j)) => fun z => da i j z * G j z
  | Sum.inr (Sum.inr (Sum.inl j)) => fun z => -(b j z * G j z)
  | Sum.inr (Sum.inr (Sum.inr _)) => fun z => -(c z * q z)

private def genericPreliftFullResidual
    {d : ℕ} (Rproper : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  Rproper z + (∑ i, ∑ j, da i j z * G j z) -
    (∑ j, b j z * G j z) - c z * q z

private theorem sum_genericPreliftFullResidualTerm
    {d : ℕ} (Rproper : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ) :
    (∑ s : FullResidualTermIndex d,
      genericPreliftFullResidualTerm Rproper da b c q G s) =
        genericPreliftFullResidual Rproper da b c q G := by
  funext z
  simp [FullResidualTermIndex, genericPreliftFullResidualTerm,
    genericPreliftFullResidual, Fintype.sum_prod_type]
  abel

private theorem card_fullResidualTermIndex (d : ℕ) :
    (Fintype.card (FullResidualTermIndex d) : ℝ) =
      (d : ℝ) ^ 2 + (d : ℝ) + 2 := by
  simp [FullResidualTermIndex]
  ring

private theorem genericPreliftFullResidual_memLp_and_sq_le
    {d : ℕ} {U : Set (TimeVelocity d)}
    (Rproper : TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c q : TimeVelocity d → ℝ)
    (G : Fin d → TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn U 2 Rproper)
    (hq : ParabolicMemLpOn U 2 q) (hG : ∀ j, ParabolicMemLpOn U 2 (G j))
    (Ada Ab Ac : ℝ) (hAda : 0 ≤ Ada) (hAb : 0 ≤ Ab) (hAc : 0 ≤ Ac)
    (hdaMeas : ∀ i j, AEStronglyMeasurable (da i j) (timeVelocityVolumeOn U))
    (hbMeas : ∀ j, AEStronglyMeasurable (b j) (timeVelocityVolumeOn U))
    (hcMeas : AEStronglyMeasurable c (timeVelocityVolumeOn U))
    (hdaBound : ∀ i j, ∀ᵐ z ∂timeVelocityVolumeOn U, |da i j z| ≤ Ada)
    (hbBound : ∀ j, ∀ᵐ z ∂timeVelocityVolumeOn U, |b j z| ≤ Ab)
    (hcBound : ∀ᵐ z ∂timeVelocityVolumeOn U, |c z| ≤ Ac) :
    ParabolicMemLpOn U 2
        (genericPreliftFullResidual Rproper da b c q G) ∧
      (ENNReal.toReal (eLpNorm
        (genericPreliftFullResidual Rproper da b c q G) 2
        (timeVelocityVolumeOn U))) ^ 2 ≤
        ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
          ((ENNReal.toReal (eLpNorm Rproper 2
            (timeVelocityVolumeOn U))) ^ 2 +
          Ada ^ 2 * ∑ _i : Fin d, ∑ j : Fin d,
            (ENNReal.toReal (eLpNorm (G j) 2
              (timeVelocityVolumeOn U))) ^ 2 +
          Ab ^ 2 * ∑ j : Fin d,
            (ENNReal.toReal (eLpNorm (G j) 2
              (timeVelocityVolumeOn U))) ^ 2 +
          Ac ^ 2 * (ENNReal.toReal (eLpNorm q 2
            (timeVelocityVolumeOn U))) ^ 2) := by
  classical
  let term := genericPreliftFullResidualTerm Rproper da b c q G
  have hterm : ∀ s : FullResidualTermIndex d,
      MemLp (term s) 2 (timeVelocityVolumeOn U) := by
    intro s
    rcases s with (_ | (⟨i, j⟩ | (j | _)))
    · exact hR
    · exact (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
        hAda (hdaMeas i j) (hG j) (hdaBound i j)).1
    · simpa [term, genericPreliftFullResidualTerm, Pi.neg_def] using
        (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
          hAb (hbMeas j) (hG j) (hbBound j)).1.neg
    · simpa [term, genericPreliftFullResidualTerm, Pi.neg_def] using
        (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
          hAc hcMeas hq hcBound).1.neg
  have hsum := HypoellipticAleksandrov.Analysis.eLpNorm_sum_toReal_sq_le_card_mul
    term hterm
  rw [sum_genericPreliftFullResidualTerm] at hsum
  refine ⟨by
    rw [← sum_genericPreliftFullResidualTerm]
    have hm := memLp_finset_sum Finset.univ (fun s _ => hterm s)
    convert hm using 1
    ext z
    simp [term], ?_⟩
  rw [card_fullResidualTermIndex] at hsum
  calc
    _ ≤ ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
        ∑ s : FullResidualTermIndex d,
          (ENNReal.toReal (eLpNorm (term s) 2
            (timeVelocityVolumeOn U))) ^ 2 := hsum
    _ ≤ ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
        ((ENNReal.toReal (eLpNorm Rproper 2
          (timeVelocityVolumeOn U))) ^ 2 +
        Ada ^ 2 * ∑ _i : Fin d, ∑ j : Fin d,
          (ENNReal.toReal (eLpNorm (G j) 2
            (timeVelocityVolumeOn U))) ^ 2 +
        Ab ^ 2 * ∑ j : Fin d,
          (ENNReal.toReal (eLpNorm (G j) 2
            (timeVelocityVolumeOn U))) ^ 2 +
        Ac ^ 2 * (ENNReal.toReal (eLpNorm q 2
          (timeVelocityVolumeOn U))) ^ 2) := by
      gcongr
      have hda (i j : Fin d) :=
        (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
          hAda (hdaMeas i j) (hG j) (hdaBound i j)).2
      have hb' (j : Fin d) :=
        (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
          hAb (hbMeas j) (hG j) (hbBound j)).2
      have hc' :=
        (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
          hAc hcMeas hq hcBound).2
      have hdaSq (i j : Fin d) :
          (ENNReal.toReal (eLpNorm (fun z => da i j z * G j z) 2
            (timeVelocityVolumeOn U))) ^ 2 ≤
            Ada ^ 2 * (ENNReal.toReal (eLpNorm (G j) 2
              (timeVelocityVolumeOn U))) ^ 2 := by
        simpa only [mul_pow] using
          (pow_le_pow_left₀ ENNReal.toReal_nonneg (hda i j) 2)
      have hbSq (j : Fin d) :
          (ENNReal.toReal (eLpNorm (fun z => b j z * G j z) 2
            (timeVelocityVolumeOn U))) ^ 2 ≤
            Ab ^ 2 * (ENNReal.toReal (eLpNorm (G j) 2
              (timeVelocityVolumeOn U))) ^ 2 := by
        simpa only [mul_pow] using
          (pow_le_pow_left₀ ENNReal.toReal_nonneg (hb' j) 2)
      have hcSq :
          (ENNReal.toReal (eLpNorm (fun z => c z * q z) 2
            (timeVelocityVolumeOn U))) ^ 2 ≤
            Ac ^ 2 * (ENNReal.toReal (eLpNorm q 2
              (timeVelocityVolumeOn U))) ^ 2 := by
        simpa only [mul_pow] using
          (pow_le_pow_left₀ ENNReal.toReal_nonneg hc' 2)
      let boundTerm : FullResidualTermIndex d → ℝ
        | Sum.inl _ => (ENNReal.toReal (eLpNorm Rproper 2
            (timeVelocityVolumeOn U))) ^ 2
        | Sum.inr (Sum.inl (i, j)) => Ada ^ 2 *
            (ENNReal.toReal (eLpNorm (G j) 2
              (timeVelocityVolumeOn U))) ^ 2
        | Sum.inr (Sum.inr (Sum.inl j)) => Ab ^ 2 *
            (ENNReal.toReal (eLpNorm (G j) 2
              (timeVelocityVolumeOn U))) ^ 2
        | Sum.inr (Sum.inr (Sum.inr _)) => Ac ^ 2 *
            (ENNReal.toReal (eLpNorm q 2
              (timeVelocityVolumeOn U))) ^ 2
      have htermSq (s : FullResidualTermIndex d) :
          (ENNReal.toReal (eLpNorm (term s) 2
            (timeVelocityVolumeOn U))) ^ 2 ≤ boundTerm s := by
        rcases s with (_ | (⟨i, j⟩ | (j | _)))
        · exact le_rfl
        · exact hdaSq i j
        · change (ENNReal.toReal (eLpNorm
              (fun z => -(b j z * G j z)) 2
              (timeVelocityVolumeOn U))) ^ 2 ≤ _
          rw [show (fun z => -(b j z * G j z)) =
            -(fun z => b j z * G j z) by rfl, eLpNorm_neg]
          exact hbSq j
        · change (ENNReal.toReal (eLpNorm
              (fun z => -(c z * q z)) 2
              (timeVelocityVolumeOn U))) ^ 2 ≤ _
          rw [show (fun z => -(c z * q z)) =
            -(fun z => c z * q z) by rfl, eLpNorm_neg]
          exact hcSq
      calc
        (∑ s : FullResidualTermIndex d,
            (ENNReal.toReal (eLpNorm (term s) 2
              (timeVelocityVolumeOn U))) ^ 2) ≤ ∑ s, boundTerm s :=
          Finset.sum_le_sum fun s _ => htermSq s
        _ = _ := by
          simp [FullResidualTermIndex, boundTerm, Fintype.sum_prod_type]
          simp_rw [Finset.mul_sum]
          ring_nf

private noncomputable def fullResidualCoarseConstant
    {d M : ℕ} (hM : 1 ≤ M)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
    (properResidualCoarseConstant
        (fun i j alpha => Ba i j (ParabolicDerivativeIndex.castLE
          (Nat.le_succ M) alpha)) Bb Bc +
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
        (diffusionGradientMajorant hM Ba ^ 2 * (d : ℝ) ^ 2 +
          driftValueMajorant Bb ^ 2 * (d : ℝ) +
          potentialValueMajorant Bc ^ 2))

private theorem fullResidualCoarseConstant_nonneg
    {d M : ℕ} (hM : 1 ≤ M)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) :
    0 ≤ fullResidualCoarseConstant hM Ba Bb Bc := by
  unfold fullResidualCoarseConstant
  have hproper := properResidualCoarseConstant_nonneg
    (fun i j alpha => Ba i j (ParabolicDerivativeIndex.castLE
      (Nat.le_succ M) alpha)) Bb Bc
  positivity

private theorem sum_le_coarse_product_of_pointwise_four_term
    {ι : Type*} [Fintype ι]
    (r p doubleG singleG q : ι → ℝ)
    (N Cp K Ada Ab Ac d Dnorm Enorm : ℝ)
    (hN : 0 ≤ N) (_hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (_hAda : 0 ≤ Ada) (_hAb : 0 ≤ Ab) (_hAc : 0 ≤ Ac)
    (hd : 0 ≤ d) (_hD : 0 ≤ Dnorm) (hE : 0 ≤ Enorm)
    (hpoint : ∀ beta,
      r beta ≤ N * (p beta + Ada ^ 2 * doubleG beta +
        Ab ^ 2 * singleG beta + Ac ^ 2 * q beta))
    (hp : (∑ beta, p beta) ≤ Cp * (Dnorm + Enorm))
    (hdoubleG : (∑ beta, doubleG beta) ≤ K * d ^ 2 * Dnorm)
    (hsingleG : (∑ beta, singleG beta) ≤ K * d * Dnorm)
    (hq : (∑ beta, q beta) ≤ K * Dnorm) :
    (∑ beta, r beta) ≤
      N * (Cp + K * (Ada ^ 2 * d ^ 2 + Ab ^ 2 * d + Ac ^ 2)) *
        (Dnorm + Enorm) := by
  have hDtoTotal : Dnorm ≤ Dnorm + Enorm := le_add_of_nonneg_right hE
  calc
    (∑ beta, r beta) ≤ ∑ beta,
        N * (p beta + Ada ^ 2 * doubleG beta +
          Ab ^ 2 * singleG beta + Ac ^ 2 * q beta) :=
      Finset.sum_le_sum fun beta _ => hpoint beta
    _ = N * ((∑ beta, p beta) + Ada ^ 2 * (∑ beta, doubleG beta) +
        Ab ^ 2 * (∑ beta, singleG beta) + Ac ^ 2 * (∑ beta, q beta)) := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ N * (Cp * (Dnorm + Enorm) +
        Ada ^ 2 * (K * d ^ 2 * Dnorm) +
        Ab ^ 2 * (K * d * Dnorm) + Ac ^ 2 * (K * Dnorm)) := by
      apply mul_le_mul_of_nonneg_left _ hN
      exact add_le_add (add_le_add (add_le_add hp
        (mul_le_mul_of_nonneg_left hdoubleG (sq_nonneg Ada)))
        (mul_le_mul_of_nonneg_left hsingleG (sq_nonneg Ab)))
        (mul_le_mul_of_nonneg_left hq (sq_nonneg Ac))
    _ ≤ N * (Cp * (Dnorm + Enorm) +
        Ada ^ 2 * (K * d ^ 2 * (Dnorm + Enorm)) +
        Ab ^ 2 * (K * d * (Dnorm + Enorm)) +
        Ac ^ 2 * (K * (Dnorm + Enorm))) := by
      apply mul_le_mul_of_nonneg_left _ hN
      have htail := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hDtoTotal
              (mul_nonneg hK (sq_nonneg d))) (sq_nonneg Ada))
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hDtoTotal (mul_nonneg hK hd)) (sq_nonneg Ab)))
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hDtoTotal hK) (sq_nonneg Ac))
      calc
        _ = Cp * (Dnorm + Enorm) +
            (Ada ^ 2 * (K * d ^ 2 * Dnorm) +
              Ab ^ 2 * (K * d * Dnorm) + Ac ^ 2 * (K * Dnorm)) := by ring
        _ ≤ Cp * (Dnorm + Enorm) +
            (Ada ^ 2 * (K * d ^ 2 * (Dnorm + Enorm)) +
              Ab ^ 2 * (K * d * (Dnorm + Enorm)) +
              Ac ^ 2 * (K * (Dnorm + Enorm))) := add_le_add le_rfl htail
        _ = _ := by ring
    _ = N * (Cp + K *
        (Ada ^ 2 * d ^ 2 + Ab ^ 2 * d + Ac ^ 2)) *
          (Dnorm + Enorm) := by ring

private theorem genericPreliftFullResidual_family_memLp_and_sum_sq_le
    {ι : Type*} [Fintype ι] {d : ℕ} {U : Set (TimeVelocity d)}
    (Rproper q : ι → TimeVelocity d → ℝ)
    (G : ι → Fin d → TimeVelocity d → ℝ)
    (da : Fin d → Fin d → TimeVelocity d → ℝ)
    (b : Fin d → TimeVelocity d → ℝ) (c : TimeVelocity d → ℝ)
    (Cp Ada Ab Ac Dnorm Enorm : ℝ)
    (hCp : 0 ≤ Cp) (hAda : 0 ≤ Ada) (hAb : 0 ≤ Ab) (hAc : 0 ≤ Ac)
    (hD : 0 ≤ Dnorm) (hE : 0 ≤ Enorm)
    (hproperMem : ∀ beta, ParabolicMemLpOn U 2 (Rproper beta))
    (hproperSum : (∑ beta, (ENNReal.toReal (eLpNorm
      (Rproper beta) 2 (timeVelocityVolumeOn U))) ^ 2) ≤
        Cp * (Dnorm + Enorm))
    (hqMem : ∀ beta, ParabolicMemLpOn U 2 (q beta))
    (hGMem : ∀ beta j, ParabolicMemLpOn U 2 (G beta j))
    (hdaMeas : ∀ i j,
      AEStronglyMeasurable (da i j) (timeVelocityVolumeOn U))
    (hbMeas : ∀ j,
      AEStronglyMeasurable (b j) (timeVelocityVolumeOn U))
    (hcMeas : AEStronglyMeasurable c (timeVelocityVolumeOn U))
    (hdaBound : ∀ i j, ∀ᵐ z ∂timeVelocityVolumeOn U, |da i j z| ≤ Ada)
    (hbBound : ∀ j, ∀ᵐ z ∂timeVelocityVolumeOn U, |b j z| ≤ Ab)
    (hcBound : ∀ᵐ z ∂timeVelocityVolumeOn U, |c z| ≤ Ac)
    (hdoubleG : (∑ beta, ∑ _i : Fin d, ∑ j : Fin d,
      (ENNReal.toReal (eLpNorm (G beta j) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card ι : ℝ) * (d : ℝ) ^ 2 * Dnorm)
    (hsingleG : (∑ beta, ∑ j : Fin d,
      (ENNReal.toReal (eLpNorm (G beta j) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card ι : ℝ) * (d : ℝ) * Dnorm)
    (hqSum : (∑ beta, (ENNReal.toReal (eLpNorm (q beta) 2
      (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card ι : ℝ) * Dnorm) :
    (∀ beta, ParabolicMemLpOn U 2
      (genericPreliftFullResidual (Rproper beta) da b c (q beta) (G beta))) ∧
    (∑ beta, (ENNReal.toReal (eLpNorm
      (genericPreliftFullResidual (Rproper beta) da b c (q beta) (G beta))
      2 (timeVelocityVolumeOn U))) ^ 2) ≤
      ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
        (Cp + (Fintype.card ι : ℝ) *
          (Ada ^ 2 * (d : ℝ) ^ 2 + Ab ^ 2 * (d : ℝ) + Ac ^ 2)) *
        (Dnorm + Enorm) := by
  classical
  have hbeta (beta : ι) := genericPreliftFullResidual_memLp_and_sq_le
    (Rproper beta) da b c (q beta) (G beta)
    (hproperMem beta) (hqMem beta) (hGMem beta)
    Ada Ab Ac hAda hAb hAc hdaMeas hbMeas hcMeas hdaBound hbBound hcBound
  refine ⟨fun beta => (hbeta beta).1, ?_⟩
  exact sum_le_coarse_product_of_pointwise_four_term
    (fun beta => (ENNReal.toReal (eLpNorm
      (genericPreliftFullResidual (Rproper beta) da b c (q beta) (G beta))
      2 (timeVelocityVolumeOn U))) ^ 2)
    (fun beta => (ENNReal.toReal (eLpNorm
      (Rproper beta) 2 (timeVelocityVolumeOn U))) ^ 2)
    (fun beta => ∑ _i : Fin d, ∑ j : Fin d,
      (ENNReal.toReal (eLpNorm (G beta j) 2
        (timeVelocityVolumeOn U))) ^ 2)
    (fun beta => ∑ j : Fin d, (ENNReal.toReal (eLpNorm (G beta j) 2
      (timeVelocityVolumeOn U))) ^ 2)
    (fun beta => (ENNReal.toReal (eLpNorm
      (q beta) 2 (timeVelocityVolumeOn U))) ^ 2)
    ((d : ℝ) ^ 2 + (d : ℝ) + 2) Cp (Fintype.card ι : ℝ)
      Ada Ab Ac (d : ℝ) Dnorm Enorm
      (by positivity) hCp (by positivity) hAda hAb hAc
      (by positivity) hD hE (fun beta => (hbeta beta).2)
      hproperSum hdoubleG hsingleG hqSum

private def sourceSpecificFullResidual
    {d M : ℕ} (hM : 1 ≤ M)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M) : TimeVelocity d → ℝ :=
  genericPreliftFullResidual
    (properDifferentiatedScalarCommutatorResidual a b c D E beta)
    (fun i j z => TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (singletonCoefficientIndex hM i).1
      (fun x : TimeVelocity d => a x.1 x.2 i j) z)
    (fun j z => b z.1 z.2 j) (fun z => c z.1 z.2)
    (D.representative (preliftValueIndex beta))
    (fun j => D.representative (preliftGradientIndex beta j))

private theorem sourceSpecificFullResidual_memLp_and_sum_sq_le
    {d M : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U) (hM : 1 ≤ M)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ)
    (F : ℝ → PDE.Vec d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) :
    (∀ beta : ParabolicDerivativeIndex d M, ParabolicMemLpOn U 2
      (sourceSpecificFullResidual hM a b c D E beta)) ∧
    (∑ beta : ParabolicDerivativeIndex d M,
      (ENNReal.toReal (eLpNorm
        (sourceSpecificFullResidual hM a b c D E beta)
        2 (timeVelocityVolumeOn U))) ^ 2) ≤
      fullResidualCoarseConstant hM Ba Bb Bc *
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
  classical
  let BaM : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ :=
    fun i j alpha => Ba i j
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
  have hproper := properResidual_memLp_and_sum_sq_le_coarse
    U hU a b c u F D E BaM Bb Bc
    (fun i j alpha => hBa i j
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha))
    hBb hBc (fun i j => (ha i j).of_le (by
      exact_mod_cast Nat.le_succ M)) hb hc
    (fun i j alpha z hz => haBound i j
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z hz)
    hbBound hcBound
  have hdaBound : ∀ i j, ∀ᵐ z ∂timeVelocityVolumeOn U,
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM i).1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤
          diffusionGradientMajorant hM Ba := by
    intro i j
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact diffusionGradient_abs_le_majorant hM a Ba hBa haBound i j i z hz
  have hbBoundAE : ∀ j, ∀ᵐ z ∂timeVelocityVolumeOn U,
      |b z.1 z.2 j| ≤ driftValueMajorant Bb := by
    intro j
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact driftValue_abs_le_majorant b Bb hBb hbBound j z hz
  have hcBoundAE : ∀ᵐ z ∂timeVelocityVolumeOn U,
      |c z.1 z.2| ≤ potentialValueMajorant Bc := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact potentialValue_abs_le_majorant c Bc hcBound z hz
  have hfull := genericPreliftFullResidual_family_memLp_and_sum_sq_le
    (fun beta : ParabolicDerivativeIndex d M =>
      properDifferentiatedScalarCommutatorResidual a b c D E beta)
    (fun beta : ParabolicDerivativeIndex d M =>
      D.representative (preliftValueIndex beta))
    (fun beta j => D.representative (preliftGradientIndex beta j))
    (fun i j z => TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (singletonCoefficientIndex hM i).1
      (fun x : TimeVelocity d => a x.1 x.2 i j) z)
    (fun j z => b z.1 z.2 j) (fun z => c z.1 z.2)
    (properResidualCoarseConstant BaM Bb Bc)
    (diffusionGradientMajorant hM Ba) (driftValueMajorant Bb)
    (potentialValueMajorant Bc)
    (ParabolicWeakDerivativeFamily.squaredL2Norm D)
    (ParabolicWeakDerivativeFamily.squaredL2Norm E)
    (properResidualCoarseConstant_nonneg BaM Bb Bc)
    (diffusionGradientMajorant_nonneg hM Ba hBa)
    (driftValueMajorant_nonneg Bb hBb)
    (potentialValueMajorant_nonneg Bc hBc)
    (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D)
    (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E)
    hproper.1 hproper.2 (fun beta => D.memLp (preliftValueIndex beta))
    (fun beta j => D.memLp (preliftGradientIndex beta j))
    (fun i j => diffusionGradient_aestronglyMeasurable hU hM a ha i j)
    (fun j => driftValue_aestronglyMeasurable hU b hb j)
    (potentialValue_aestronglyMeasurable hU c hc)
    hdaBound hbBoundAE hcBoundAE
    (allPreliftGradient_double_component_sum_sq_le D)
    (allPreliftGradient_component_sum_sq_le D)
    (allPreliftValue_component_sum_sq_le D)
  simpa only [sourceSpecificFullResidual, fullResidualCoarseConstant, BaM] using hfull

private theorem integrable_mul_test_of_memLp
    {d : ℕ} {U : Set (TimeVelocity d)} {f φ : TimeVelocity d → ℝ}
    (hf : ParabolicMemLpOn U 2 f) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Integrable (fun z => f z * φ z) (timeVelocityVolumeOn U) := by
  have hφLp : MemLp φ (2 : ℝ≥0∞) (timeVelocityVolumeOn U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict U
  simpa only [Pi.mul_def] using hf.integrable_mul hφLp

private theorem sourceSpecific_testedEquation
    {d M : ℕ} (hM : 1 ≤ M) (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha) (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) U)
    (haBound : ∀ i j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha)
    (hEq :
      (fun z =>
        D.representative (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
            (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j, a z.1 z.2 i j * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j, b z.1 z.2 j * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.zeroTwo d)) z) =ᵐ[timeVelocityVolumeOn U]
        (fun z => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M)
    (hproper : ParabolicMemLpOn U 2
      (properDifferentiatedScalarCommutatorResidual a b c D E beta)) :
    ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      -(∫ z in U, D.representative (preliftValueIndex beta) z *
          timeDerivative φ z) -
        (∑ i, ∑ j, ∫ z in U, a z.1 z.2 i j *
          D.representative (preliftGradientIndex beta j) z *
          velocityGradient φ z i) =
        ∫ z in U, sourceSpecificFullResidual hM a b c D E beta z * φ z := by
  classical
  intro φ hφ hφc hφU
  have hraw := integral_genericPreliftDifferentiatedScalarEquation hM U hU
    a b c F u D E ha hb hc hEq beta φ hφ hφc hφU
  let da : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
    TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (singletonCoefficientIndex hM i).1
      (fun x : TimeVelocity d => a x.1 x.2 i j) z
  let q := D.representative (preliftValueIndex beta)
  let G : Fin d → TimeVelocity d → ℝ := fun j =>
    D.representative (preliftGradientIndex beta j)
  have hdaLp (i j : Fin d) : ParabolicMemLpOn U 2 (fun z => da i j z * G j z) := by
    apply (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (diffusionGradientMajorant_nonneg hM Ba hBa)
      (diffusionGradient_aestronglyMeasurable hU hM a ha i j)
      (D.memLp (preliftGradientIndex beta j)) ?_).1
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact diffusionGradient_abs_le_majorant hM a Ba hBa haBound i j i z hz
  have hbLp (j : Fin d) : ParabolicMemLpOn U 2 (fun z => b z.1 z.2 j * G j z) := by
    apply (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (driftValueMajorant_nonneg Bb hBb)
      (driftValue_aestronglyMeasurable hU b hb j)
      (D.memLp (preliftGradientIndex beta j)) ?_).1
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact driftValue_abs_le_majorant b Bb hBb hbBound j z hz
  have hcLp : ParabolicMemLpOn U 2 (fun z => c z.1 z.2 * q z) := by
    apply (HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
      (potentialValueMajorant_nonneg Bc hBc)
      (potentialValue_aestronglyMeasurable hU c hc)
      (D.memLp (preliftValueIndex beta)) ?_).1
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact potentialValue_abs_le_majorant c Bc hcBound z hz
  have hproperInt := integrable_mul_test_of_memLp hproper hφ hφc
  have hdaInt (i j : Fin d) := integrable_mul_test_of_memLp (hdaLp i j) hφ hφc
  have hbInt (j : Fin d) := integrable_mul_test_of_memLp (hbLp j) hφ hφc
  have hcInt := integrable_mul_test_of_memLp hcLp hφ hφc
  have hdaSumInt : Integrable (fun z => ∑ i, ∑ j, da i j z * G j z * φ z)
      (timeVelocityVolumeOn U) :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hdaInt i j
  have hbSumInt : Integrable (fun z => ∑ j, b z.1 z.2 j * G j z * φ z)
      (timeVelocityVolumeOn U) :=
    integrable_finset_sum _ fun j _ => hbInt j
  have hcombinedInt := (hproperInt.add hdaSumInt).sub hbSumInt
  have hproperDaInt : Integrable (fun z =>
      properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z +
        (∑ i, ∑ j, da i j z * G j z * φ z)) (timeVelocityVolumeOn U) := by
    simpa only [Pi.add_def] using hproperInt.add hdaSumInt
  have hcombinedInt' : Integrable (fun z =>
      properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z +
          (∑ i, ∑ j, da i j z * G j z * φ z) -
          (∑ j, b z.1 z.2 j * G j z * φ z)) (timeVelocityVolumeOn U) := by
    simpa only [Pi.add_def, Pi.sub_def] using hcombinedInt
  have hRexpand :
      (∫ z in U, sourceSpecificFullResidual hM a b c D E beta z * φ z) =
        ∫ z in U,
          properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z +
            (∑ i, ∑ j, da i j z * G j z * φ z) -
            (∑ j, b z.1 z.2 j * G j z * φ z) -
            c z.1 z.2 * q z * φ z := by
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [sourceSpecificFullResidual, genericPreliftFullResidual, da, q, G]
    simp only [add_mul, sub_mul, Finset.sum_mul]
  have hlinear :
      (∫ z in U,
          properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z +
            (∑ i, ∑ j, da i j z * G j z * φ z) -
            (∑ j, b z.1 z.2 j * G j z * φ z) -
            c z.1 z.2 * q z * φ z) =
        (∫ z in U, properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z) +
          (∑ i, ∑ j, ∫ z in U, da i j z * G j z * φ z) -
          (∑ j, ∫ z in U, b z.1 z.2 j * G j z * φ z) -
          ∫ z in U, c z.1 z.2 * q z * φ z := by
    change (∫ z,
      properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z +
          (∑ i, ∑ j, da i j z * G j z * φ z) -
          (∑ j, b z.1 z.2 j * G j z * φ z) -
          c z.1 z.2 * q z * φ z ∂timeVelocityVolumeOn U) = _
    rw [integral_sub hcombinedInt' hcInt,
      integral_sub hproperDaInt hbSumInt,
      integral_add hproperInt hdaSumInt,
      integral_finset_sum Finset.univ (fun i _ =>
        integrable_finset_sum _ fun j _ => hdaInt i j)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hdaInt _ j)]
    rw [integral_finset_sum Finset.univ (fun j _ => hbInt j)]
  rw [hRexpand]
  rw [hlinear]
  dsimp only [preliftValueIndex, preliftGradientIndex, da, q, G] at hraw ⊢
  simp_rw [singletonCoefficientIndex_coe hM] at ⊢
  linear_combination hraw

/-- Uniform interior spatial-difference-quotient control of every selected
gradient in the generic tested pre-lift equation. -/
theorem exists_genericPrelift_gradient_spatialDifferenceQuotient_estimate
    (d M : ℕ) (hM : 1 ≤ M)
    (t₀ t₁ t₂ t₃ : ℝ)
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀) (hO₁ : IsOpen O₁) (hO₁ne : O₁.Nonempty)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ)
        (u : TimeVelocity d → ℝ)
        (D : ParabolicWeakDerivativeFamily d (M + 1)
          (Set.Ioo t₀ t₃ ×ˢ O₀) u)
        (E : ParabolicWeakDerivativeFamily d M
          (Set.Ioo t₀ t₃ ×ˢ O₀)
          (fun z : TimeVelocity d => F z.1 z.2)),
        (∀ z ∈ Set.Ioo t₀ t₃ ×ˢ O₀, (a z.1 z.2).IsSymm) →
        (∀ z ∈ Set.Ioo t₀ t₃ ×ˢ O₀,
          lam • (1 : PDE.Mat d) ≤ a z.1 z.2 ∧
            a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)) →
        (∀ i j, ContDiffOn ℝ (M + 1)
          (fun z : TimeVelocity d => a z.1 z.2 i j)
          (Set.Ioo t₀ t₃ ×ˢ O₀)) →
        (∀ j, ContDiffOn ℝ M
          (fun z : TimeVelocity d => b z.1 z.2 j)
          (Set.Ioo t₀ t₃ ×ˢ O₀)) →
        ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2)
          (Set.Ioo t₀ t₃ ×ˢ O₀) →
        (∀ i j alpha z, z ∈ Set.Ioo t₀ t₃ ×ˢ O₀ →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
            (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha) →
        (∀ j alpha z, z ∈ Set.Ioo t₀ t₃ ×ˢ O₀ →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
            (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha) →
        (∀ alpha z, z ∈ Set.Ioo t₀ t₃ ×ˢ O₀ →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
            (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha) →
        ((fun z =>
          D.representative
              (ParabolicDerivativeIndex.castLE
                (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.timeOne d)) z +
            (∑ i, ∑ j, a z.1 z.2 i j *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.velocityTwo j i)) z) +
            (∑ j, b z.1 z.2 j *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.velocityOne j)) z) +
            c z.1 z.2 *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.zeroTwo d)) z)
          =ᵐ[timeVelocityVolumeOn (Set.Ioo t₀ t₃ ×ˢ O₀)]
            fun z => F z.1 z.2) →
        ∀ h : ℝ, 0 < h → h < δ →
          (∀ (beta : ParabolicDerivativeIndex d M) (j i : Fin d),
            ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
              (spatialDifferenceQuotient i h
                (D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE
                      (Nat.le_succ M) beta) j
                    (by
                      change beta.1.parabolicWeight + 1 ≤ M + 1
                      omega))))) ∧
          (∑ beta : ParabolicDerivativeIndex d M,
            ∑ j : Fin d, ∑ i : Fin d,
              (ENNReal.toReal (eLpNorm
                (spatialDifferenceQuotient i h
                  (D.representative
                    (ParabolicDerivativeIndex.velocitySucc
                      (ParabolicDerivativeIndex.castLE
                        (Nat.le_succ M) beta) j
                      (by
                        change beta.1.parabolicWeight + 1 ≤ M + 1
                        omega))))
                2 (timeVelocityVolumeOn
                  (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C *
              (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
  classical
  let Ma := diffusionGradientMajorant hM Ba
  obtain ⟨Ccore, δ, hCcore, hδ, hcore⟩ :=
    exists_gradient_spatialDifferenceQuotient_estimate_of_testedEquation
      d t₀ t₁ t₂ t₃ ht₀₁ ht₁₂ ht₂₃ O₀ O₁ hO₀ hO₁ hO₁ne
      hO₁compact hO₁O₀ lam Lam Ma hlam hlamLam
      (diffusionGradientMajorant_nonneg hM Ba hBa)
  let K := (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (1 + (d : ℝ)) +
    fullResidualCoarseConstant hM Ba Bb Bc
  refine ⟨Ccore * K, δ, mul_nonneg hCcore ?_, hδ, ?_⟩
  · dsimp only [K]
    exact add_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (fullResidualCoarseConstant_nonneg hM Ba Bb Bc)
  · intro a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
    let U : Set (TimeVelocity d) := Set.Ioo t₀ t₃ ×ˢ O₀
    have hU : IsOpen U := isOpen_Ioo.prod hO₀
    have hres := sourceSpecificFullResidual_memLp_and_sum_sq_le U hU hM
      a b c u F D E Ba Bb Bc hBa hBb hBc ha hb hc haBound hbBound hcBound
    let BaM : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ :=
      fun i j alpha => Ba i j
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
    have hproper := properResidual_memLp_and_sum_sq_le_coarse U hU
      a b c u F D E BaM Bb Bc
      (fun i j alpha => hBa i j
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha))
      hBb hBc (fun i j => (ha i j).of_le (by
        exact_mod_cast Nat.le_succ M)) hb hc
      (fun i j alpha z hz => haBound i j
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z hz)
      hbBound hcBound
    have hbeta (beta : ParabolicDerivativeIndex d M) :=
      hcore (fun z => a z.1 z.2)
        (D.representative (preliftValueIndex beta))
        (fun j => D.representative (preliftGradientIndex beta j))
        (sourceSpecificFullResidual hM a b c D E beta)
        hSymm hEll
        (fun i j => (ha i j).of_le (by
          exact_mod_cast (show 1 ≤ M + 1 by omega)))
        (fun i j k z hz =>
          spatialPartial_coefficient_abs_le_majorant hU hM a Ba hBa ha haBound
            i j k z hz)
        (D.memLp (preliftValueIndex beta))
        (fun j => D.memLp (preliftGradientIndex beta j))
        (hres.1 beta)
        (fun j => D.hasWeakVelocitySucc (preliftValueIndex beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega))
        (sourceSpecific_testedEquation hM U hU a b c F u D E Ba Bb Bc
          hBa hBb hBc ha hb hc haBound hbBound hcBound hEq beta (hproper.1 beta))
    intro h hh hhd
    have hbetaH (beta : ParabolicDerivativeIndex d M) := hbeta beta h hh hhd
    constructor
    · intro beta j i
      exact (hbetaH beta).1 j i
    · have hsum := Finset.sum_le_sum fun beta (_hbeta : beta ∈ Finset.univ) =>
        (hbetaH beta).2
      have hq := allPreliftValue_component_sum_sq_le D
      have hG := allPreliftGradient_component_sum_sq_le D
      have hD := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D
      have hE := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
      calc
        _ ≤ ∑ beta : ParabolicDerivativeIndex d M, Ccore *
            ((ENNReal.toReal (eLpNorm
                (D.representative (preliftValueIndex beta)) 2
                (timeVelocityVolumeOn U))) ^ 2 +
              (∑ j : Fin d, (ENNReal.toReal (eLpNorm
                (D.representative (preliftGradientIndex beta j)) 2
                (timeVelocityVolumeOn U))) ^ 2) +
              (ENNReal.toReal (eLpNorm
                (sourceSpecificFullResidual hM a b c D E beta) 2
                (timeVelocityVolumeOn U))) ^ 2) := by
            simpa only [U, preliftGradientIndex] using! hsum
        _ = Ccore *
            ((∑ beta : ParabolicDerivativeIndex d M,
                (ENNReal.toReal (eLpNorm
                  (D.representative (preliftValueIndex beta)) 2
                  (timeVelocityVolumeOn U))) ^ 2) +
              (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d,
                (ENNReal.toReal (eLpNorm
                  (D.representative (preliftGradientIndex beta j)) 2
                  (timeVelocityVolumeOn U))) ^ 2) +
              ∑ beta : ParabolicDerivativeIndex d M,
                (ENNReal.toReal (eLpNorm
                  (sourceSpecificFullResidual hM a b c D E beta) 2
                  (timeVelocityVolumeOn U))) ^ 2) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        _ ≤ Ccore *
            (((Fintype.card (ParabolicDerivativeIndex d M) : ℝ) +
                (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ)) *
                ParabolicWeakDerivativeFamily.squaredL2Norm D +
              fullResidualCoarseConstant hM Ba Bb Bc *
                (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                  ParabolicWeakDerivativeFamily.squaredL2Norm E)) := by
            apply mul_le_mul_of_nonneg_left _ hCcore
            have hqG := add_le_add hq hG
            have hqG' :
                (∑ beta : ParabolicDerivativeIndex d M,
                    (ENNReal.toReal (eLpNorm
                      (D.representative (preliftValueIndex beta)) 2
                      (timeVelocityVolumeOn U))) ^ 2) +
                  (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d,
                    (ENNReal.toReal (eLpNorm
                      (D.representative (preliftGradientIndex beta j)) 2
                      (timeVelocityVolumeOn U))) ^ 2) ≤
                ((Fintype.card (ParabolicDerivativeIndex d M) : ℝ) +
                    (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ)) *
                  ParabolicWeakDerivativeFamily.squaredL2Norm D := by
              dsimp only [U]
              calc
                _ ≤ (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
                      ParabolicWeakDerivativeFamily.squaredL2Norm D +
                    (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) *
                      ParabolicWeakDerivativeFamily.squaredL2Norm D := hqG
                _ = _ := by ring
            exact add_le_add hqG' hres.2
        _ ≤ Ccore * K *
            (ParabolicWeakDerivativeFamily.squaredL2Norm D +
              ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
            dsimp only [K]
            have hcard : 0 ≤ (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) :=
              by positivity
            have hd : 0 ≤ (d : ℝ) := by positivity
            have hcoarse := fullResidualCoarseConstant_nonneg hM Ba Bb Bc
            rw [mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hCcore
            have hDtotal : ParabolicWeakDerivativeFamily.squaredL2Norm D ≤
                ParabolicWeakDerivativeFamily.squaredL2Norm D +
                  ParabolicWeakDerivativeFamily.squaredL2Norm E :=
              le_add_of_nonneg_right hE
            calc
              _ = ((Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
                    (1 + (d : ℝ))) *
                    ParabolicWeakDerivativeFamily.squaredL2Norm D +
                  fullResidualCoarseConstant hM Ba Bb Bc *
                    (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                      ParabolicWeakDerivativeFamily.squaredL2Norm E) := by ring
              _ ≤ ((Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
                    (1 + (d : ℝ))) *
                    (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                      ParabolicWeakDerivativeFamily.squaredL2Norm E) +
                  fullResidualCoarseConstant hM Ba Bb Bc *
                    (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                      ParabolicWeakDerivativeFamily.squaredL2Norm E) :=
                add_le_add
                  (mul_le_mul_of_nonneg_left hDtotal
                    (mul_nonneg hcard (add_nonneg zero_le_one hd))) le_rfl
              _ = _ := by ring


end HypoellipticAleksandrov.Parabolic
