module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftHessianRecovery
public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1WeakLeibniz
public import HypoellipticAleksandrov.Parabolic.ProperCommutatorSquaredAggregation
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm

/-! # Generic pre-lift time-successor recovery -/

@[expose] public section

noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory Set
open scoped BigOperators ENNReal MatrixOrder

private theorem setIntegral_mul_eq_of_tsupport_subset
    {d : ℕ} {V U : Set (TimeVelocity d)} (hU : MeasurableSet U)
    (hVU : V ⊆ U) (f g : TimeVelocity d → ℝ) (hgV : tsupport g ⊆ V) :
    (∫ z in U, f z * g z ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in V, f z * g z ∂(volume : Measure (TimeVelocity d)) := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hU hVU
  intro z hz
  have hgz : g z = 0 := by
    by_contra hn
    exact hz.2 (hgV (subset_closure hn))
  simp [hgz]

private theorem coordinateIteratedFDeriv_tsupport_subset
    {d : ℕ} (gamma : TimeVelocityMultiIndex d) (f : TimeVelocity d → ℝ) :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply support_iteratedFDeriv_subset (f := f) (𝕜 := ℝ) gamma.coordinateList.length
  intro hzero
  exact hz (by
    unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    rw [hzero]
    exact ContinuousMultilinearMap.zero_apply _)

private theorem timeDerivative_tsupport_subset
    {d : ℕ} (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  have heq : timeDerivative f =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) f := by
    funext z
    have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) (timeCoord d) f z
        (by
          simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
            TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using
            hf.contDiffAt.of_le
              (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp))
    simp only [zero_add, timeVelocityBasis_time] at h
    rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (0 : TimeVelocityMultiIndex d) f = f by
      funext x
      exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f x] at h
    exact h.symm
  rw [heq]
  exact coordinateIteratedFDeriv_tsupport_subset _ f

private theorem velocityGradient_tsupport_subset
    {d : ℕ} (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) :
    tsupport (fun z ↦ velocityGradient f z i) ⊆ tsupport f := by
  have heq : (fun z ↦ velocityGradient f z i) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord i) 1) f := by
    funext z
    have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) (velocityCoord i) f z
        (by
          simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
            TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using
            hf.contDiffAt.of_le
              (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by simp))
    simp only [zero_add, timeVelocityBasis_velocity] at h
    rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (0 : TimeVelocityMultiIndex d) f = f by
      funext x
      exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f x] at h
    simpa [velocityGradient, PDE.basisVec] using h.symm
  rw [heq]
  exact coordinateIteratedFDeriv_tsupport_subset _ f

private def singletonCoefficientIndex {d M : ℕ} (hM : 1 ≤ M) (i : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.castLE (by omega)
    (ParabolicDerivativeIndex.velocityOne i)

private theorem singletonCoefficientIndex_coe
    {d M : ℕ} (hM : 1 ≤ M) (i : Fin d) :
    (singletonCoefficientIndex hM i).1 = Pi.single (velocityCoord i) 1 := by
  funext c
  rcases c with _ | k
  · rfl
  · change Function.update (0 : Fin d → ℕ) i 1 k =
      (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr k)
    by_cases hik : i = k
    · subst k
      simp
    · simp [Function.update, Ne.symm hik]

private theorem residual_memLp
    {d m n : ℕ} {V : Set (TimeVelocity d)}
    (R : TimeVelocity d → ℝ)
    (AH : Fin m → Fin n → TimeVelocity d → ℝ)
    (BG : Fin n → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn V 2 R)
    (hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j))
    (hBG : ∀ j, ParabolicMemLpOn V 2 (BG j))
    (hCQ : ParabolicMemLpOn V 2 CQ) :
    ParabolicMemLpOn V 2 (fun z ↦
      R z - (∑ i, ∑ j, AH i j z) - (∑ j, BG j z) - CQ z) := by
  classical
  have hAHsum : ParabolicMemLpOn V 2 (fun z ↦ ∑ i, ∑ j, AH i j z) := by
    simpa only using memLp_finset_sum Finset.univ (fun i _ ↦
      memLp_finset_sum Finset.univ (fun j _ ↦ hAH i j))
  have hBGsum : ParabolicMemLpOn V 2 (fun z ↦ ∑ j, BG j z) := by
    simpa only using memLp_finset_sum Finset.univ (fun j _ ↦ hBG j)
  exact ((hR.sub hAHsum).sub hBGsum).sub hCQ

private abbrev TimeSuccessorAtom (d : ℕ) :=
  Unit ⊕ ((Fin d × Fin d) ⊕ (Fin d ⊕ Unit))

private def timeSuccessorAtomTerm
    {d : ℕ} (R : TimeVelocity d → ℝ)
    (AH : Fin d → Fin d → TimeVelocity d → ℝ)
    (BG : Fin d → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ) :
    TimeSuccessorAtom d → TimeVelocity d → ℝ
  | Sum.inl _ => R
  | Sum.inr (Sum.inl (i, j)) => fun z => -AH i j z
  | Sum.inr (Sum.inr (Sum.inl j)) => fun z => -BG j z
  | Sum.inr (Sum.inr (Sum.inr _)) => fun z => -CQ z

private theorem sum_timeSuccessorAtomTerm
    {d : ℕ} (R : TimeVelocity d → ℝ)
    (AH : Fin d → Fin d → TimeVelocity d → ℝ)
    (BG : Fin d → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ) :
    (∑ s : TimeSuccessorAtom d, timeSuccessorAtomTerm R AH BG CQ s) =
      fun z => R z - (∑ i, ∑ j, AH i j z) - (∑ j, BG j z) - CQ z := by
  funext z
  simp [TimeSuccessorAtom, timeSuccessorAtomTerm, Fintype.sum_prod_type]
  ring

private theorem card_timeSuccessorAtom (d : ℕ) :
    (Fintype.card (TimeSuccessorAtom d) : ℝ) =
      (d : ℝ) ^ 2 + (d : ℝ) + 2 := by
  simp [TimeSuccessorAtom]
  ring

private theorem timeSuccessorResidual_memLp_and_sq_le
    {d : ℕ} {V : Set (TimeVelocity d)}
    (R : TimeVelocity d → ℝ)
    (AH : Fin d → Fin d → TimeVelocity d → ℝ)
    (BG : Fin d → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ)
    (hR : ParabolicMemLpOn V 2 R)
    (hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j))
    (hBG : ∀ j, ParabolicMemLpOn V 2 (BG j))
    (hCQ : ParabolicMemLpOn V 2 CQ) :
    ParabolicMemLpOn V 2 (fun z =>
      R z - (∑ i, ∑ j, AH i j z) - (∑ j, BG j z) - CQ z) ∧
    (ENNReal.toReal (eLpNorm (fun z =>
      R z - (∑ i, ∑ j, AH i j z) - (∑ j, BG j z) - CQ z)
      2 (timeVelocityVolumeOn V))) ^ 2 ≤
      ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
        ((ENNReal.toReal (eLpNorm R 2 (timeVelocityVolumeOn V))) ^ 2 +
          (∑ i, ∑ j, (ENNReal.toReal
            (eLpNorm (AH i j) 2 (timeVelocityVolumeOn V))) ^ 2) +
          (∑ j, (ENNReal.toReal
            (eLpNorm (BG j) 2 (timeVelocityVolumeOn V))) ^ 2) +
          (ENNReal.toReal (eLpNorm CQ 2 (timeVelocityVolumeOn V))) ^ 2) := by
  classical
  let term := timeSuccessorAtomTerm R AH BG CQ
  have hterm : ∀ s : TimeSuccessorAtom d,
      MemLp (term s) 2 (timeVelocityVolumeOn V) := by
    intro s
    rcases s with (_ | (⟨i, j⟩ | (j | _)))
    · exact hR
    · simpa [term, timeSuccessorAtomTerm, Pi.neg_def] using (hAH i j).neg
    · simpa [term, timeSuccessorAtomTerm, Pi.neg_def] using (hBG j).neg
    · simpa [term, timeSuccessorAtomTerm, Pi.neg_def] using hCQ.neg
  have hsum := HypoellipticAleksandrov.Analysis.eLpNorm_sum_toReal_sq_le_card_mul
    term hterm
  rw [sum_timeSuccessorAtomTerm] at hsum
  refine ⟨residual_memLp R AH BG CQ hR hAH hBG hCQ, ?_⟩
  rw [card_timeSuccessorAtom] at hsum
  calc
    _ ≤ ((d : ℝ) ^ 2 + (d : ℝ) + 2) *
        ∑ s : TimeSuccessorAtom d,
          (ENNReal.toReal (eLpNorm (term s) 2
            (timeVelocityVolumeOn V))) ^ 2 := hsum
    _ = _ := by
      have hAHneg (i j : Fin d) :
          eLpNorm (fun z => -AH i j z) 2 (timeVelocityVolumeOn V) =
            eLpNorm (AH i j) 2 (timeVelocityVolumeOn V) := by
        rw [show (fun z => -AH i j z) = -(AH i j) by rfl, eLpNorm_neg]
      have hBGneg (j : Fin d) :
          eLpNorm (fun z => -BG j z) 2 (timeVelocityVolumeOn V) =
            eLpNorm (BG j) 2 (timeVelocityVolumeOn V) := by
        rw [show (fun z => -BG j z) = -(BG j) by rfl, eLpNorm_neg]
      have hCQneg : eLpNorm (fun z => -CQ z) 2 (timeVelocityVolumeOn V) =
          eLpNorm CQ 2 (timeVelocityVolumeOn V) := by
        rw [show (fun z => -CQ z) = -CQ by rfl, eLpNorm_neg]
      simp [TimeSuccessorAtom, term, timeSuccessorAtomTerm,
        Fintype.sum_prod_type, hAHneg, hBGneg, hCQneg]
      left
      ring

private theorem sum_sq_le_of_four_family_bounds
    {beta : Type*} [Fintype beta]
    (W R AH BG CQ : beta → ℝ) (N CR CA CB CC Etotal : ℝ)
    (hN : 0 ≤ N) (_hCR : 0 ≤ CR) (_hCA : 0 ≤ CA)
    (_hCB : 0 ≤ CB) (_hCC : 0 ≤ CC) (_hE : 0 ≤ Etotal)
    (hW : ∀ b, W b ≤ N * (R b + AH b + BG b + CQ b))
    (hR : (∑ b, R b) ≤ CR * Etotal)
    (hAH : (∑ b, AH b) ≤ CA * Etotal)
    (hBG : (∑ b, BG b) ≤ CB * Etotal)
    (hCQ : (∑ b, CQ b) ≤ CC * Etotal) :
    (∑ b, W b) ≤ N * (CR + CA + CB + CC) * Etotal := by
  calc
    (∑ b, W b) ≤ ∑ b, N * (R b + AH b + BG b + CQ b) :=
      Finset.sum_le_sum fun b _ => hW b
    _ = N * ((∑ b, R b) + (∑ b, AH b) + (∑ b, BG b) +
        ∑ b, CQ b) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ ≤ N * (CR * Etotal + CA * Etotal + CB * Etotal + CC * Etotal) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add hR hAH) hBG) hCQ) hN
    _ = N * (CR + CA + CB + CC) * Etotal := by ring

private noncomputable def timeSuccessorProperCoefficientEnergy
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (beta : ParabolicDerivativeIndex d M) : ℝ :=
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
      Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2)

private noncomputable def timeSuccessorProperResidualCoarseConstant
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) : ℝ :=
  ∑ beta : ParabolicDerivativeIndex d M,
    ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ) *
      (1 + timeSuccessorProperCoefficientEnergy Ba Bb Bc beta)

private theorem timeSuccessorProperCoefficientEnergy_nonneg
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (beta : ParabolicDerivativeIndex d M) :
    0 ≤ timeSuccessorProperCoefficientEnergy Ba Bb Bc beta := by
  unfold timeSuccessorProperCoefficientEnergy
  positivity

private theorem timeSuccessorProperResidualCoarseConstant_nonneg
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ) :
    0 ≤ timeSuccessorProperResidualCoarseConstant Ba Bb Bc := by
  unfold timeSuccessorProperResidualCoarseConstant
  exact Finset.sum_nonneg fun beta _ => mul_nonneg (by positivity)
    (add_nonneg zero_le_one
      (timeSuccessorProperCoefficientEnergy_nonneg Ba Bb Bc beta))

private theorem weighted_component_sum_le_coarse
    {beta : Type*} [Fintype beta]
    (r weight coefficientEnergy : beta → ℝ)
    (Dnorm Enorm : ℝ) (_hD : 0 ≤ Dnorm) (_hE : 0 ≤ Enorm)
    (hr : ∀ b, r b ≤ weight b * (1 + coefficientEnergy b) *
      (Dnorm + Enorm)) :
    (∑ b, r b) ≤
      (∑ b, weight b * (1 + coefficientEnergy b)) *
        (Dnorm + Enorm) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun b _ => hr b

private theorem properResidual_sum_sq_le_coarse_of_pointwise
    {d M : ℕ}
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (r : ParabolicDerivativeIndex d M → ℝ)
    (Dnorm Enorm : ℝ) (hD : 0 ≤ Dnorm) (hE : 0 ≤ Enorm)
    (hr : ∀ beta, r beta ≤
      ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ) *
        (1 + timeSuccessorProperCoefficientEnergy Ba Bb Bc beta) *
          (Dnorm + Enorm)) :
    (∑ beta, r beta) ≤
      timeSuccessorProperResidualCoarseConstant Ba Bb Bc *
        (Dnorm + Enorm) := by
  exact weighted_component_sum_le_coarse r
    (fun beta =>
      ((1 + (d ^ 2 + d + 1) * properSplitCard beta : ℕ) : ℝ))
    (timeSuccessorProperCoefficientEnergy Ba Bb Bc) Dnorm Enorm hD hE hr

private def timeSuccessorValueIndex {d M : ℕ}
    (beta : ParabolicDerivativeIndex d M) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta

private def timeSuccessorGradientIndex {d M : ℕ}
    (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
    ParabolicDerivativeIndex d (M + 1) :=
  ParabolicDerivativeIndex.velocitySucc (timeSuccessorValueIndex beta) j (by
    change beta.1.parabolicWeight + 1 ≤ M + 1
    omega)

private theorem allTimeSuccessorValue_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u) :
    (∑ beta : ParabolicDerivativeIndex d M,
      (ENNReal.toReal (eLpNorm
        (D.representative (timeSuccessorValueIndex beta)) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) *
        ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _beta : ParabolicDerivativeIndex d M,
        ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun beta _ =>
        ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _
    _ = _ := by simp

private theorem allTimeSuccessorGradient_component_sum_sq_le
    {d M : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u) :
    (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d,
      (ENNReal.toReal (eLpNorm
        (D.representative (timeSuccessorGradientIndex beta j)) 2
        (timeVelocityVolumeOn U))) ^ 2) ≤
      (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) *
        ParabolicWeakDerivativeFamily.squaredL2Norm D := by
  calc
    _ ≤ ∑ _beta : ParabolicDerivativeIndex d M, ∑ _j : Fin d,
        ParabolicWeakDerivativeFamily.squaredL2Norm D :=
      Finset.sum_le_sum fun beta _ => Finset.sum_le_sum fun j _ =>
        ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D _
    _ = _ := by simp; ring

private theorem bounded_mul_memLp
    {d : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (q f : TimeVelocity d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hq : ContinuousOn q V) (hqBound : ∀ z ∈ V, |q z| ≤ C)
    (hf : ParabolicMemLpOn V 2 f) :
    ParabolicMemLpOn V 2 (fun z ↦ q z * f z) := by
  have hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn V) :=
    hq.aestronglyMeasurable hV.measurableSet
  have hqBoundAE : ∀ᵐ z ∂timeVelocityVolumeOn V, |q z| ≤ C := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
    exact hqBound z hz
  have hprodMeas : AEStronglyMeasurable (fun z ↦ q z * f z)
      (timeVelocityVolumeOn V) := hqMeas.mul hf.aestronglyMeasurable
  apply MemLp.of_le_mul hf hprodMeas
  filter_upwards [hqBoundAE] with z hz
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul hz le_rfl (abs_nonneg (f z)) hC

private theorem spatialPartial_coefficient_eq_singletonDerivative
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (hM : 1 ≤ M) (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (k i j : Fin d) (z : TimeVelocity d) (hz : z ∈ U) :
    spatialPartial k (fun y => a z.1 y i j) z.2 =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM k).1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z := by
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
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [hslice.fderiv]
  rfl

private theorem velocityGradient_coefficient_eq_singletonDerivative
    {d M : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (hM : 1 ≤ M) (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (k i j : Fin d) (z : TimeVelocity d) (hz : z ∈ U) :
    velocityGradient (fun x : TimeVelocity d => a x.1 x.2 i j) z k =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (singletonCoefficientIndex hM k).1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z := by
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
  rfl

private theorem hasWeakTimeDerivOn_of_testedEquation_cancellation
    {d n : ℕ} {V : Set (TimeVelocity d)}
    (q R W : TimeVelocity d → ℝ)
    (P DA AH : Fin d → Fin n → TimeVelocity d → ℝ)
    (BG : Fin n → TimeVelocity d → ℝ)
    (CQ : TimeVelocity d → ℝ)
    (hPweak : ∀ i j, HasWeakVelocityPartialDerivOn V
      i (P i j) (fun z ↦ DA i j z + AH i j z))
    (hR : ParabolicMemLpOn V 2 R)
    (hDA : ∀ i j, ParabolicMemLpOn V 2 (DA i j))
    (hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j))
    (hBG : ∀ j, ParabolicMemLpOn V 2 (BG j))
    (hCQ : ParabolicMemLpOn V 2 CQ)
    (hW : ∀ z, W z = R z - (∑ i, ∑ j, AH i j z) -
      (∑ j, BG j z) - CQ z)
    (htested : ∀ φ : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
      -(∫ z in V, q z * timeDerivative φ z ∂(volume : Measure (TimeVelocity d))) -
          (∑ i, ∑ j, ∫ z in V, P i j z *
            velocityGradient φ z i ∂(volume : Measure (TimeVelocity d))) -
          (∑ i, ∑ j, ∫ z in V, DA i j z * φ z
            ∂(volume : Measure (TimeVelocity d))) +
          (∑ j, ∫ z in V, BG j z * φ z
            ∂(volume : Measure (TimeVelocity d))) +
          (∫ z in V, CQ z * φ z ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in V, R z * φ z ∂(volume : Measure (TimeVelocity d))) :
    HasWeakTimeDerivOn V q W := by
  classical
  intro φ hφ hφCompact hφV
  have hraw := htested φ hφ hφCompact hφV
  have hweak (i : Fin d) (j : Fin n) :=
    hPweak i j φ hφ hφCompact hφV
  simp_rw [hweak] at hraw
  have hφTwo : MemLp φ 2 (volume : Measure (TimeVelocity d)) :=
    hφ.continuous.memLp_of_hasCompactSupport hφCompact
  have hRint : Integrable (fun z ↦ R z * φ z) (timeVelocityVolumeOn V) :=
    hR.integrable_mul (hφTwo.restrict V)
  have hDAint (i : Fin d) (j : Fin n) :
      Integrable (fun z ↦ DA i j z * φ z) (timeVelocityVolumeOn V) :=
    (hDA i j).integrable_mul (hφTwo.restrict V)
  have hAHint (i : Fin d) (j : Fin n) :
      Integrable (fun z ↦ AH i j z * φ z) (timeVelocityVolumeOn V) :=
    (hAH i j).integrable_mul (hφTwo.restrict V)
  have hBGint (j : Fin n) :
      Integrable (fun z ↦ BG j z * φ z) (timeVelocityVolumeOn V) :=
    (hBG j).integrable_mul (hφTwo.restrict V)
  have hCQint : Integrable (fun z ↦ CQ z * φ z) (timeVelocityVolumeOn V) :=
    hCQ.integrable_mul (hφTwo.restrict V)
  have hAHsumInt : Integrable
      (fun z ↦ (∑ i, ∑ j, AH i j z) * φ z) (timeVelocityVolumeOn V) := by
    simpa only [Finset.sum_mul] using integrable_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ (fun j _ ↦ hAHint i j))
  have hBGsumInt : Integrable
      (fun z ↦ (∑ j, BG j z) * φ z) (timeVelocityVolumeOn V) := by
    simpa only [Finset.sum_mul] using
      integrable_finset_sum Finset.univ (fun j _ ↦ hBGint j)
  rw [show (∫ z in V, W z * φ z ∂(volume : Measure (TimeVelocity d))) =
      (((∫ z in V, R z * φ z ∂(volume : Measure (TimeVelocity d))) -
        ∑ i, ∑ j, ∫ z in V, AH i j z * φ z
          ∂(volume : Measure (TimeVelocity d))) -
        ∑ j, ∫ z in V, BG j z * φ z
          ∂(volume : Measure (TimeVelocity d))) -
        ∫ z in V, CQ z * φ z ∂(volume : Measure (TimeVelocity d)) from by
    calc
      _ = ∫ z in V, (((R z * φ z - (∑ i, ∑ j, AH i j z) * φ z) -
          (∑ j, BG j z) * φ z) - CQ z * φ z)
          ∂(volume : Measure (TimeVelocity d)) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun z ↦ by
              change W z * φ z = _
              rw [hW z]
              ring
      _ = _ := by
        let fR : TimeVelocity d → ℝ := fun z ↦ R z * φ z
        let fA : TimeVelocity d → ℝ := fun z ↦ (∑ i, ∑ j, AH i j z) * φ z
        let fB : TimeVelocity d → ℝ := fun z ↦ (∑ j, BG j z) * φ z
        let fC : TimeVelocity d → ℝ := fun z ↦ CQ z * φ z
        have hfR : Integrable fR (timeVelocityVolumeOn V) := hRint
        have hfA : Integrable fA (timeVelocityVolumeOn V) := hAHsumInt
        have hfB : Integrable fB (timeVelocityVolumeOn V) := hBGsumInt
        have hfC : Integrable fC (timeVelocityVolumeOn V) := hCQint
        change (∫ z, (((fR - fA) - fB) - fC) z ∂timeVelocityVolumeOn V) = _
        calc
          _ = (∫ z, ((fR - fA) - fB) z ∂timeVelocityVolumeOn V) -
              ∫ z, fC z ∂timeVelocityVolumeOn V := by
                simpa only [Pi.sub_apply] using
                  integral_sub ((hfR.sub hfA).sub hfB) hfC
          _ = ((∫ z, (fR - fA) z ∂timeVelocityVolumeOn V) -
              ∫ z, fB z ∂timeVelocityVolumeOn V) -
              ∫ z, fC z ∂timeVelocityVolumeOn V := by
                simpa only [Pi.sub_apply] using congrArg
                  (fun x : ℝ ↦ x - ∫ z, fC z ∂timeVelocityVolumeOn V)
                  (integral_sub (hfR.sub hfA) hfB)
          _ = (((∫ z, fR z ∂timeVelocityVolumeOn V) -
              ∫ z, fA z ∂timeVelocityVolumeOn V) -
              ∫ z, fB z ∂timeVelocityVolumeOn V) -
              ∫ z, fC z ∂timeVelocityVolumeOn V := by
                simpa only [Pi.sub_apply] using congrArg
                  (fun x : ℝ ↦ (x - ∫ z, fB z ∂timeVelocityVolumeOn V) -
                    ∫ z, fC z ∂timeVelocityVolumeOn V)
                  (integral_sub hfR hfA)
          _ = _ := by
            have hAIntegral : (∫ z, fA z ∂timeVelocityVolumeOn V) =
                ∑ i, ∑ j, ∫ z in V, AH i j z * φ z
                  ∂(volume : Measure (TimeVelocity d)) := by
              dsimp only [fA]
              simp_rw [Finset.sum_mul]
              rw [integral_finset_sum Finset.univ (fun i _ ↦
                integrable_finset_sum Finset.univ (fun j _ ↦ hAHint i j))]
              apply Finset.sum_congr rfl
              intro i hi
              exact integral_finset_sum Finset.univ (fun j _ ↦ hAHint i j)
            have hBIntegral : (∫ z, fB z ∂timeVelocityVolumeOn V) =
                ∑ j, ∫ z in V, BG j z * φ z
                  ∂(volume : Measure (TimeVelocity d)) := by
              dsimp only [fB]
              simp_rw [Finset.sum_mul]
              exact integral_finset_sum Finset.univ (fun j _ ↦ hBGint j)
            rw [hAIntegral, hBIntegral]
    ]
  simp_rw [add_mul, integral_add (hDAint _ _) (hAHint _ _)] at hraw
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hraw
  linarith

/-- Canonical weak time-successor candidate obtained after recovering every
spatial derivative of the selected generic pre-lift gradients. -/
def genericPreliftTimeSuccessorResidual
    {d M : ℕ} (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ)
    (beta : ParabolicDerivativeIndex d M) (z : TimeVelocity d) : ℝ :=
  properDifferentiatedScalarCommutatorResidual a b c D E beta z -
    (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * H z beta j i) -
    (∑ j : Fin d, b z.1 z.2 j *
      D.representative
        (ParabolicDerivativeIndex.velocitySucc
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
          (by
            change beta.1.parabolicWeight + 1 ≤ M + 1
            omega)) z) -
    c z.1 z.2 *
      D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z

/-- Exact joint weak spatial-and-time conclusion of generic pre-lift
time-successor recovery. -/
def GenericPreliftTimeSuccessorConclusion
    {d M : ℕ} (V : Set (TimeVelocity d))
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (C_HW : ℝ) : Prop :=
  ∃ H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ,
    (∀ beta j i, ParabolicMemLpOn V 2
      (fun z => H z beta j i)) ∧
    (∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z =>
        D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) j
            (by
              change beta.1.parabolicWeight + 1 ≤ M + 1
              omega)) z)
      (fun z => H z beta j i)) ∧
    (∀ beta, ParabolicMemLpOn V 2
      (genericPreliftTimeSuccessorResidual a b c D E H beta)) ∧
    (∀ beta, HasWeakTimeDerivOn V
      (fun z =>
        D.representative
          (ParabolicDerivativeIndex.castLE
            (Nat.le_succ M) beta) z)
      (genericPreliftTimeSuccessorResidual a b c D E H beta)) ∧
    ((∑ beta : ParabolicDerivativeIndex d M,
        ∑ j : Fin d, ∑ i : Fin d,
          (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
            (timeVelocityVolumeOn V))) ^ 2) +
      ∑ beta : ParabolicDerivativeIndex d M,
        (ENNReal.toReal (eLpNorm
          (genericPreliftTimeSuccessorResidual a b c D E H beta) 2
          (timeVelocityVolumeOn V))) ^ 2) ≤
      C_HW *
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E)

/-- The generic pre-lift Hessian determines all selected weak time successors
on the interior cylinder, with a joint spatial-and-time `L²` estimate. -/
theorem exists_genericPrelift_hessian_timeSuccessor_family_estimate
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
    ∃ C_HW : ℝ, 0 ≤ C_HW ∧
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
        GenericPreliftTimeSuccessorConclusion
          (Set.Ioo t₁ t₂ ×ˢ O₁) a b c D E C_HW := by
  classical
  obtain ⟨C_H, hC_H, hHessian⟩ :=
    exists_genericPrelift_gradient_velocityPartialDeriv_family_estimate
      d M hM t₀ t₁ t₂ t₃ ht₀₁ ht₁₂ ht₂₃ O₀ O₁ hO₀ hO₁ hO₁ne
        hO₁compact hO₁O₀ lam Lam hlam hlamLam Ba Bb Bc hBa hBb hBc
  let BaM : Fin d → Fin d → ParabolicDerivativeIndex d M → ℝ :=
    fun i j alpha => Ba i j
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
  let C_R := timeSuccessorProperResidualCoarseConstant BaM Bb Bc
  let B_b : ℝ := ∑ j : Fin d, (Bb j (ParabolicDerivativeIndex.zero d M)) ^ 2
  let B_c : ℝ := (Bc (ParabolicDerivativeIndex.zero d M)) ^ 2
  let N : ℝ := (d : ℝ) ^ 2 + (d : ℝ) + 2
  let K : ℝ := (Fintype.card (ParabolicDerivativeIndex d M) : ℝ)
  let C_W : ℝ := N * (C_R + Lam ^ 2 * C_H + B_b * K + B_c * K)
  let C_HW : ℝ := C_H + C_W
  have hLam : 0 ≤ Lam := le_trans (le_of_lt hlam) hlamLam
  have hBaM : ∀ i j alpha, 0 ≤ BaM i j alpha := fun i j alpha => hBa _ _ _
  have hCR : 0 ≤ C_R := timeSuccessorProperResidualCoarseConstant_nonneg BaM Bb Bc
  have hBbEnergy : 0 ≤ B_b := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hBcEnergy : 0 ≤ B_c := sq_nonneg _
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCW : 0 ≤ C_W := by
    dsimp [C_W]
    positivity
  refine ⟨C_HW, add_nonneg hC_H hCW, ?_⟩
  intro a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
  obtain ⟨H, hHmem, hHweak, hHsq⟩ :=
    hHessian a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
  let U := Set.Ioo t₀ t₃ ×ˢ O₀
  let V := Set.Ioo t₁ t₂ ×ˢ O₁
  have hVopen : IsOpen V := isOpen_Ioo.prod hO₁
  have hVU : V ⊆ U := Set.prod_mono
    (Set.Ioo_subset_Ioo ht₀₁.le ht₂₃.le) (subset_closure.trans hO₁O₀)
  have haV : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) V := fun i j => (ha i j).mono hVU
  have hbV : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) V := fun j => (hb j).mono hVU
  have hcV : ContDiffOn ℝ M (fun z : TimeVelocity d => c z.1 z.2) V := hc.mono hVU
  have hDlocal (alpha : ParabolicDerivativeIndex d (M + 1)) :
      ParabolicMemLpOn V 2 (D.representative alpha) :=
    (D.memLp alpha).mono_measure (Measure.restrict_mono_set volume hVU)
  have hR := properDifferentiatedScalarCommutatorResidual_memLp_and_sum_sq_le
    V hVopen a b c u F (D.restrict hVU) (E.restrict hVU) BaM Bb Bc
      hBaM hBb hBc (fun i j => (haV i j).of_le (by
        exact_mod_cast Nat.le_succ M)) hbV hcV
      (fun i j alpha z hz => by
        simpa only [BaM, ParabolicWeakDerivativeFamily.restrict_representative,
          ParabolicDerivativeIndex.coe_castLE] using
          haBound i j (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z (hVU hz))
      (fun j alpha z hz => hbBound j alpha z (hVU hz))
      (fun alpha z hz => hcBound alpha z (hVU hz))
  simp only [ParabolicWeakDerivativeFamily.restrict_representative] at hR
  -- The semantic and quantitative assembly follows from the localized equation.
  refine ⟨H, hHmem, hHweak, ?_, ?_, ?_⟩
  · intro beta
    let R := properDifferentiatedScalarCommutatorResidual a b c D E beta
    let AH : Fin d → Fin d → TimeVelocity d → ℝ :=
      fun i j z => a z.1 z.2 i j * H z beta j i
    let BG : Fin d → TimeVelocity d → ℝ := fun j z =>
      b z.1 z.2 j * D.representative (timeSuccessorGradientIndex beta j) z
    let CQ : TimeVelocity d → ℝ := fun z =>
      c z.1 z.2 * D.representative (timeSuccessorValueIndex beta) z
    have hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j) := by
      intro i j
      apply bounded_mul_memLp hVopen _ _ Lam hLam (haV i j).continuousOn
        (fun z hz => HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
          (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j)
      exact hHmem beta j i
    have hBG : ∀ j, ParabolicMemLpOn V 2 (BG j) := by
      intro j
      apply bounded_mul_memLp hVopen _ _ (Bb j (ParabolicDerivativeIndex.zero d M))
        (hBb _ _) (hbV j).continuousOn
      · intro z hz
        simpa [ParabolicDerivativeIndex.zero] using
          hbBound j (ParabolicDerivativeIndex.zero d M) z (hVU hz)
      · exact hDlocal _
    have hCQ : ParabolicMemLpOn V 2 CQ := by
      apply bounded_mul_memLp hVopen _ _ (Bc (ParabolicDerivativeIndex.zero d M))
        (hBc _) hcV.continuousOn
      · intro z hz
        simpa [ParabolicDerivativeIndex.zero] using
          hcBound (ParabolicDerivativeIndex.zero d M) z (hVU hz)
      · exact hDlocal _
    convert residual_memLp R AH BG CQ (hR.1 beta) hAH hBG hCQ using 1
    funext z
    rfl
  · intro beta
    -- Product cancellation and localization are kept explicit to preserve signs.
    let R := properDifferentiatedScalarCommutatorResidual a b c D E beta
    let P : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
      a z.1 z.2 i j * D.representative (timeSuccessorGradientIndex beta j) z
    let DA : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
      velocityGradient (fun x : TimeVelocity d => a x.1 x.2 i j) z i *
        D.representative (timeSuccessorGradientIndex beta j) z
    let AH : Fin d → Fin d → TimeVelocity d → ℝ := fun i j z =>
      a z.1 z.2 i j * H z beta j i
    let BG : Fin d → TimeVelocity d → ℝ := fun j z =>
      b z.1 z.2 j * D.representative (timeSuccessorGradientIndex beta j) z
    let CQ : TimeVelocity d → ℝ := fun z =>
      c z.1 z.2 * D.representative (timeSuccessorValueIndex beta) z
    have hprod (i j : Fin d) :=
      velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le hVopen i
        Lam (Ba i j (singletonCoefficientIndex hM i)) hLam (hBa _ _ _)
        (fun z : TimeVelocity d => a z.1 z.2 i j)
        ((haV i j).of_le (by norm_num))
        (fun z hz => HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
          (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j)
        (fun z hz => by
          rw [velocityGradient_coefficient_eq_singletonDerivative
            hVopen hM a haV i i j z hz]
          exact haBound i j (singletonCoefficientIndex hM i) z (hVU hz))
        (fun z => D.representative (timeSuccessorGradientIndex beta j) z)
        (fun z => H z beta j i) (hDlocal _) (hHmem beta j i) (hHweak beta j i)
    have hPweak : ∀ i j, HasWeakVelocityPartialDerivOn V i (P i j)
        (fun z => DA i j z + AH i j z) := by
      intro i j
      simpa only [P, DA, AH, timeSuccessorGradientIndex, add_comm]
        using (hprod i j).2.2.2.1
    have hDA : ∀ i j, ParabolicMemLpOn V 2 (DA i j) := by
      intro i j
      have h := (hprod i j).2.2.1.sub (by
        apply bounded_mul_memLp hVopen _ _ Lam hLam (haV i j).continuousOn
          (fun z hz => HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
            (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j)
        exact hHmem beta j i)
      convert h using 1
      funext z
      dsimp only [DA, AH, Pi.sub_apply]
      ring
    have hAH : ∀ i j, ParabolicMemLpOn V 2 (AH i j) := fun i j => by
      apply bounded_mul_memLp hVopen _ _ Lam hLam (haV i j).continuousOn
        (fun z hz => HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
          (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j)
      exact hHmem beta j i
    have hBG : ∀ j, ParabolicMemLpOn V 2 (BG j) := by
      intro j
      apply bounded_mul_memLp hVopen _ _ (Bb j (ParabolicDerivativeIndex.zero d M))
        (hBb _ _) (hbV j).continuousOn
      · intro z hz
        simpa [ParabolicDerivativeIndex.zero] using
          hbBound j (ParabolicDerivativeIndex.zero d M) z (hVU hz)
      · exact hDlocal _
    have hCQ : ParabolicMemLpOn V 2 CQ := by
      apply bounded_mul_memLp hVopen _ _ (Bc (ParabolicDerivativeIndex.zero d M))
        (hBc _) hcV.continuousOn
      · intro z hz
        simpa [ParabolicDerivativeIndex.zero] using
          hcBound (ParabolicDerivativeIndex.zero d M) z (hVU hz)
      · exact hDlocal _
    apply hasWeakTimeDerivOn_of_testedEquation_cancellation
      _ R _ P DA AH BG CQ hPweak (hR.1 beta) hDA hAH hBG hCQ
    · intro z
      rfl
    · intro φ hφ hφc hφV
      have hout := integral_genericPreliftDifferentiatedScalarEquation hM U
        (isOpen_Ioo.prod hO₀) a b c F u D E ha hb hc hEq beta φ hφ hφc
          (hφV.trans hVU)
      have ht := setIntegral_mul_eq_of_tsupport_subset
        (isOpen_Ioo.prod hO₀).measurableSet hVU
        (D.representative
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta)) (timeDerivative φ)
        ((timeDerivative_tsupport_subset φ hφ).trans hφV)
      have hv (i j : Fin d) := setIntegral_mul_eq_of_tsupport_subset
        (isOpen_Ioo.prod hO₀).measurableSet hVU
        (fun z => a z.1 z.2 i j *
          D.representative
            (ParabolicDerivativeIndex.velocitySucc
              (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j (by
                change beta.1.parabolicWeight + 1 ≤ M + 1
                omega)) z)
        (fun z => velocityGradient φ z i)
        ((velocityGradient_tsupport_subset φ hφ i).trans hφV)
      have hzero (f : TimeVelocity d → ℝ) := setIntegral_mul_eq_of_tsupport_subset
        (isOpen_Ioo.prod hO₀).measurableSet hVU f φ hφV
      dsimp only [U] at hout
      rw [ht] at hout
      simp_rw [hv] at hout
      simp_rw [hzero] at hout
      have hDAint (i j : Fin d) :
          (∫ z in V, TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1)
              (fun x : TimeVelocity d => a x.1 x.2 i j) z *
                D.representative (timeSuccessorGradientIndex beta j) z * φ z) =
            ∫ z in V, velocityGradient
              (fun x : TimeVelocity d => a x.1 x.2 i j) z i *
                D.representative (timeSuccessorGradientIndex beta j) z * φ z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
        rw [velocityGradient_coefficient_eq_singletonDerivative
          hVopen hM a haV i i j z hz, singletonCoefficientIndex_coe]
      dsimp only [timeSuccessorGradientIndex, timeSuccessorValueIndex] at hDAint
      simp_rw [hDAint] at hout
      simpa only [P, DA, BG, CQ, R, timeSuccessorGradientIndex,
        timeSuccessorValueIndex] using hout
  · let Etotal := ParabolicWeakDerivativeFamily.squaredL2Norm D +
        ParabolicWeakDerivativeFamily.squaredL2Norm E
    have hDnorm := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D
    have hEnorm := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
    have hEtotal : 0 ≤ Etotal := add_nonneg hDnorm hEnorm
    have hDcomponent (alpha : ParabolicDerivativeIndex d (M + 1)) :
        (ENNReal.toReal (eLpNorm (D.representative alpha) 2
          (timeVelocityVolumeOn V))) ^ 2 ≤
            ParabolicWeakDerivativeFamily.squaredL2Norm D := by
      calc
        _ ≤ ParabolicWeakDerivativeFamily.squaredL2Norm (D.restrict hVU) :=
          ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm (D.restrict hVU) alpha
        _ ≤ _ := ParabolicWeakDerivativeFamily.squaredL2Norm_restrict_le D hVU
    have hEcomponent (alpha : ParabolicDerivativeIndex d M) :
        (ENNReal.toReal (eLpNorm (E.representative alpha) 2
          (timeVelocityVolumeOn V))) ^ 2 ≤
            ParabolicWeakDerivativeFamily.squaredL2Norm E := by
      calc
        _ ≤ ParabolicWeakDerivativeFamily.squaredL2Norm (E.restrict hVU) :=
          ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm (E.restrict hVU) alpha
        _ ≤ _ := ParabolicWeakDerivativeFamily.squaredL2Norm_restrict_le E hVU
    have hRcoarse :
        (∑ beta : ParabolicDerivativeIndex d M,
          (ENNReal.toReal (eLpNorm
            (properDifferentiatedScalarCommutatorResidual a b c D E beta) 2
            (timeVelocityVolumeOn V))) ^ 2) ≤ C_R * Etotal := by
      refine hR.2.trans ?_
      dsimp only [C_R, timeSuccessorProperResidualCoarseConstant]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro beta hbeta
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ Etotal +
            (∑ i, ∑ j, ∑ gamma :
                {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
              ((beta.1.choose gamma.1.left : ℝ) *
                BaM i j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2 *
                  Etotal) +
            (∑ j, ∑ gamma :
                {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
              ((beta.1.choose gamma.1.left : ℝ) *
                Bb j (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2 *
                  Etotal) +
            (∑ gamma :
                {gamma : TimeVelocityMultiIndex.Split beta.1 // gamma.left ≠ 0},
              ((beta.1.choose gamma.1.left : ℝ) *
                Bc (ParabolicDerivativeIndex.splitLeft beta gamma.1)) ^ 2 *
                  Etotal) := by
          gcongr
          · exact (hEcomponent beta).trans
              (le_add_of_nonneg_left hDnorm)
          · rw [mul_pow]
            exact mul_le_mul_of_nonneg_left
              ((hDcomponent _).trans
                (le_add_of_nonneg_right hEnorm)) (sq_nonneg _)
          · rw [mul_pow]
            exact mul_le_mul_of_nonneg_left
              ((hDcomponent _).trans
                (le_add_of_nonneg_right hEnorm)) (sq_nonneg _)
          · rw [mul_pow]
            exact mul_le_mul_of_nonneg_left
              ((hDcomponent _).trans
                (le_add_of_nonneg_right hEnorm)) (sq_nonneg _)
        _ = _ := by
          dsimp only [timeSuccessorProperCoefficientEnergy]
          simp_rw [add_mul, Finset.sum_mul]
          ring
    have hAHentry (beta : ParabolicDerivativeIndex d M) (i j : Fin d) :
        (ENNReal.toReal (eLpNorm (fun z => a z.1 z.2 i j * H z beta j i) 2
          (timeVelocityVolumeOn V))) ^ 2 ≤ Lam ^ 2 *
            (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
              (timeVelocityVolumeOn V))) ^ 2 := by
      have hp := HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
        hLam ((haV i j).continuousOn.aestronglyMeasurable hVopen.measurableSet)
        (hHmem beta j i) (ae_restrict_of_forall_mem hVopen.measurableSet
          (fun z hz => HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
            (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j))
      have hn := ENNReal.toReal_nonneg (a := eLpNorm
        (fun z => a z.1 z.2 i j * H z beta j i) 2 (timeVelocityVolumeOn V))
      have hh := ENNReal.toReal_nonneg (a := eLpNorm
        (fun z => H z beta j i) 2 (timeVelocityVolumeOn V))
      nlinarith [hp.2]
    have hBGentry (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
        (ENNReal.toReal (eLpNorm (fun z => b z.1 z.2 j *
          D.representative (timeSuccessorGradientIndex beta j) z) 2
          (timeVelocityVolumeOn V))) ^ 2 ≤
          (Bb j (ParabolicDerivativeIndex.zero d M)) ^ 2 *
            ParabolicWeakDerivativeFamily.squaredL2Norm D := by
      let Bj := Bb j (ParabolicDerivativeIndex.zero d M)
      have hp := HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
        (a := fun z => b z.1 z.2 j)
        (f := D.representative (timeSuccessorGradientIndex beta j))
        (hBb _ _) ((hbV j).continuousOn.aestronglyMeasurable hVopen.measurableSet)
        (hDlocal _) (ae_restrict_of_forall_mem hVopen.measurableSet (fun z hz => by
          simpa [ParabolicDerivativeIndex.zero] using
            hbBound j (ParabolicDerivativeIndex.zero d M) z (hVU hz)))
      have hs := hDcomponent (timeSuccessorGradientIndex beta j)
      have hn := ENNReal.toReal_nonneg (a := eLpNorm (fun z => b z.1 z.2 j *
        D.representative (timeSuccessorGradientIndex beta j) z) 2
        (timeVelocityVolumeOn V))
      have hg := ENNReal.toReal_nonneg (a := eLpNorm
        (D.representative (timeSuccessorGradientIndex beta j)) 2
        (timeVelocityVolumeOn V))
      have hsquare := (sq_le_sq₀ hn
        (mul_nonneg (hBb j (ParabolicDerivativeIndex.zero d M)) hg)).2 hp.2
      calc
        _ ≤ (Bb j (ParabolicDerivativeIndex.zero d M)) ^ 2 *
            (ENNReal.toReal (eLpNorm
              (D.representative (timeSuccessorGradientIndex beta j)) 2
              (timeVelocityVolumeOn V))) ^ 2 := by
                simpa only [mul_pow] using hsquare
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    have hCQentry (beta : ParabolicDerivativeIndex d M) :
        (ENNReal.toReal (eLpNorm (fun z => c z.1 z.2 *
          D.representative (timeSuccessorValueIndex beta) z) 2
          (timeVelocityVolumeOn V))) ^ 2 ≤ B_c *
            ParabolicWeakDerivativeFamily.squaredL2Norm D := by
      have hp := HypoellipticAleksandrov.Analysis.memLp_mul_eLpNorm_toReal_le_of_ae_abs_le
        (a := fun z => c z.1 z.2)
        (f := D.representative (timeSuccessorValueIndex beta))
        (hBc _) (hcV.continuousOn.aestronglyMeasurable hVopen.measurableSet)
        (hDlocal _) (ae_restrict_of_forall_mem hVopen.measurableSet (fun z hz => by
          simpa [ParabolicDerivativeIndex.zero] using
            hcBound (ParabolicDerivativeIndex.zero d M) z (hVU hz)))
      have hs := hDcomponent (timeSuccessorValueIndex beta)
      have hn := ENNReal.toReal_nonneg (a := eLpNorm (fun z => c z.1 z.2 *
        D.representative (timeSuccessorValueIndex beta) z) 2
        (timeVelocityVolumeOn V))
      have hq := ENNReal.toReal_nonneg (a := eLpNorm
        (D.representative (timeSuccessorValueIndex beta)) 2
        (timeVelocityVolumeOn V))
      have hsquare := (sq_le_sq₀ hn
        (mul_nonneg (hBc (ParabolicDerivativeIndex.zero d M)) hq)).2 hp.2
      calc
        _ ≤ (Bc (ParabolicDerivativeIndex.zero d M)) ^ 2 *
            (ENNReal.toReal (eLpNorm
              (D.representative (timeSuccessorValueIndex beta)) 2
              (timeVelocityVolumeOn V))) ^ 2 := by
                simpa only [mul_pow] using hsquare
        _ ≤ B_c * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
          dsimp only [B_c]
          exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    have hWpoint (beta : ParabolicDerivativeIndex d M) :=
      (timeSuccessorResidual_memLp_and_sq_le
        (properDifferentiatedScalarCommutatorResidual a b c D E beta)
        (fun i j z => a z.1 z.2 i j * H z beta j i)
        (fun j z => b z.1 z.2 j *
          D.representative (timeSuccessorGradientIndex beta j) z)
        (fun z => c z.1 z.2 * D.representative (timeSuccessorValueIndex beta) z)
        (hR.1 beta)
        (fun i j => bounded_mul_memLp hVopen
          (fun z => a z.1 z.2 i j) (fun z => H z beta j i)
          Lam hLam (haV i j).continuousOn
          (fun z hz => HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
            (hEll z (hVU hz)).1 (hEll z (hVU hz)).2 i j) (hHmem beta j i))
        (fun j => bounded_mul_memLp hVopen (fun z => b z.1 z.2 j)
          (D.representative (timeSuccessorGradientIndex beta j))
          (Bb j (ParabolicDerivativeIndex.zero d M)) (hBb _ _) (hbV j).continuousOn
          (fun z hz => by
            have hx := hbBound j (ParabolicDerivativeIndex.zero d M) z (hVU hz)
            simpa [ParabolicDerivativeIndex.zero] using hx) (hDlocal _))
        (bounded_mul_memLp hVopen (fun z => c z.1 z.2)
          (D.representative (timeSuccessorValueIndex beta))
          (Bc (ParabolicDerivativeIndex.zero d M))
          (hBc _) hcV.continuousOn (fun z hz => by
            simpa [ParabolicDerivativeIndex.zero] using
              hcBound (ParabolicDerivativeIndex.zero d M) z (hVU hz)) (hDlocal _))).2
    have hWsum : (∑ beta : ParabolicDerivativeIndex d M,
        (ENNReal.toReal (eLpNorm
          (genericPreliftTimeSuccessorResidual a b c D E H beta) 2
          (timeVelocityVolumeOn V))) ^ 2) ≤ C_W * Etotal := by
      apply (sum_sq_le_of_four_family_bounds
        (fun beta => (ENNReal.toReal (eLpNorm
          (genericPreliftTimeSuccessorResidual a b c D E H beta) 2
          (timeVelocityVolumeOn V))) ^ 2)
        (fun beta => (ENNReal.toReal (eLpNorm
          (properDifferentiatedScalarCommutatorResidual a b c D E beta) 2
          (timeVelocityVolumeOn V))) ^ 2)
        (fun beta => ∑ i, ∑ j, (ENNReal.toReal (eLpNorm
          (fun z => a z.1 z.2 i j * H z beta j i) 2
          (timeVelocityVolumeOn V))) ^ 2)
        (fun beta => ∑ j, (ENNReal.toReal (eLpNorm (fun z => b z.1 z.2 j *
          D.representative (timeSuccessorGradientIndex beta j) z) 2
          (timeVelocityVolumeOn V))) ^ 2)
        (fun beta => (ENNReal.toReal (eLpNorm (fun z => c z.1 z.2 *
          D.representative (timeSuccessorValueIndex beta) z) 2
          (timeVelocityVolumeOn V))) ^ 2)
        N C_R (Lam ^ 2 * C_H) (B_b * K) (B_c * K) Etotal
        hN hCR (mul_nonneg (sq_nonneg _) hC_H) (mul_nonneg hBbEnergy hK)
        (mul_nonneg hBcEnergy hK) hEtotal ?_ hRcoarse ?_ ?_ ?_).trans_eq ?_
      · intro beta
        convert hWpoint beta using 1
        congr 2
      · calc
          _ ≤ ∑ beta, ∑ i, ∑ j, Lam ^ 2 *
              (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
                (timeVelocityVolumeOn V))) ^ 2 := by
                gcongr
                exact hAHentry _ _ _
          _ = Lam ^ 2 * (∑ beta, ∑ j, ∑ i,
              (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
                (timeVelocityVolumeOn V))) ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro beta hbeta
                rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                simp_rw [Finset.mul_sum]
          _ ≤ Lam ^ 2 * C_H * Etotal := by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left hHsq (sq_nonneg _)
      · calc
          _ ≤ ∑ beta, ∑ j, (Bb j (ParabolicDerivativeIndex.zero d M)) ^ 2 *
              ParabolicWeakDerivativeFamily.squaredL2Norm D := by gcongr; exact hBGentry _ _
          _ = K * B_b * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
            simp only [Finset.sum_const, nsmul_eq_mul, K, B_b,
              Finset.card_univ]
            rw [← Finset.sum_mul]
            ac_rfl
          _ ≤ K * B_b * Etotal :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hEnorm)
              (mul_nonneg hK hBbEnergy)
          _ = B_b * K * Etotal := by ring
      · calc
          _ ≤ ∑ _beta : ParabolicDerivativeIndex d M,
              B_c * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
                gcongr; exact hCQentry _
          _ = K * B_c * ParabolicWeakDerivativeFamily.squaredL2Norm D := by
            simp only [Finset.sum_const, nsmul_eq_mul, K, Finset.card_univ]
            ring
          _ ≤ K * B_c * Etotal :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hEnorm)
              (mul_nonneg hK hBcEnergy)
          _ = B_c * K * Etotal := by ring
      · rfl
    calc
      _ ≤ C_H * Etotal + C_W * Etotal := add_le_add hHsq hWsum
      _ = C_HW * Etotal := by dsimp only [C_HW]; ring


end HypoellipticAleksandrov.Parabolic
