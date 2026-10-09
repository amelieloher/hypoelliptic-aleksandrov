module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEstimate
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientL2WeakDerivative

/-!
# Generic pre-lift Hessian recovery

This module recovers weak velocity partial derivatives of every selected
generic pre-lift gradient from the uniform spatial difference-quotient bound.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal MatrixOrder

/-- Every selected generic pre-lift gradient has all weak velocity partial
derivatives on the interior cylinder, with a joint `L²` estimate. -/
theorem exists_genericPrelift_gradient_velocityPartialDeriv_family_estimate
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
    ∃ C_H : ℝ, 0 ≤ C_H ∧
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
        ∃ H : TimeVelocity d → ParabolicDerivativeIndex d M →
            Fin d → Fin d → ℝ,
          (∀ beta j i, ParabolicMemLpOn (Set.Ioo t₁ t₂ ×ˢ O₁) 2
            (fun z => H z beta j i)) ∧
          (∀ beta j i, HasWeakVelocityPartialDerivOn
            (Set.Ioo t₁ t₂ ×ˢ O₁) i
            (fun z =>
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    change beta.1.parabolicWeight + 1 ≤ M + 1
                    omega)) z)
            (fun z => H z beta j i)) ∧
          (∑ beta : ParabolicDerivativeIndex d M,
            ∑ j : Fin d, ∑ i : Fin d,
              (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
                (timeVelocityVolumeOn
                  (Set.Ioo t₁ t₂ ×ˢ O₁)))) ^ 2) ≤
            C_H *
              (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
  classical
  obtain ⟨C_DQ, δ, hC_DQ, hδ, hmain⟩ :=
    exists_genericPrelift_gradient_spatialDifferenceQuotient_estimate
      d M hM t₀ t₁ t₂ t₃ ht₀₁ ht₁₂ ht₂₃ O₀ O₁ hO₀ hO₁ hO₁ne
        hO₁compact hO₁O₀ lam Lam hlam hlamLam Ba Bb Bc hBa hBb hBc
  let C_H : ℝ :=
    (Fintype.card (ParabolicDerivativeIndex d M) : ℝ) * (d : ℝ) ^ 2 * C_DQ
  refine ⟨C_H, mul_nonneg (mul_nonneg (by positivity) (by positivity)) hC_DQ, ?_⟩
  intro a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
  let V : Set (TimeVelocity d) := Set.Ioo t₁ t₂ ×ˢ O₁
  let Etotal : ℝ := ParabolicWeakDerivativeFamily.squaredL2Norm D +
    ParabolicWeakDerivativeFamily.squaredL2Norm E
  have hEtotal : 0 ≤ Etotal := add_nonneg
    (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D)
    (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E)
  have hDQ := hmain a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
  have hlocal (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
      ParabolicMemLpOn V 2
        (fun z => D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
            (by
              change beta.1.parabolicWeight + 1 ≤ M + 1
              omega)) z) := by
    exact (D.memLp _).mono_measure
      (Measure.restrict_mono_set volume (Set.prod_mono
        (Set.Ioo_subset_Ioo ht₀₁.le ht₂₃.le) (subset_closure.trans hO₁O₀)))
  have hclose : ∀ beta : ParabolicDerivativeIndex d M, ∀ j i : Fin d,
      ∃ g : TimeVelocity d → ℝ, ∃ hg : ParabolicMemLpOn V 2 g,
        HasWeakVelocityPartialDerivOn V i
          (fun z => D.representative
            (ParabolicDerivativeIndex.velocitySucc
              (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
              (by
                change beta.1.parabolicWeight + 1 ≤ M + 1
                omega)) z) g ∧
          ‖hg.toLp g‖ ≤ Real.sqrt (C_DQ * Etotal) := by
    intro beta j i
    let G : TimeVelocity d → ℝ := fun z => D.representative
      (ParabolicDerivativeIndex.velocitySucc
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
        (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)) z
    have hmem : ∀ h : ℝ, 0 < h → h < δ → ParabolicMemLpOn V 2
        (spatialDifferenceQuotient i h G) := by
      intro h hh hhd
      simpa only [G] using (hDQ h hh hhd).1 beta j i
    have hsq : ∀ (h : ℝ) (hh : 0 < h) (hhd : h < δ),
        ‖(hmem h hh hhd).toLp (spatialDifferenceQuotient i h G)‖ ^ 2 ≤
          C_DQ * Etotal := by
      intro h hh hhd
      have hjoint := (hDQ h hh hhd).2
      let q : ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ :=
        fun beta j i => (ENNReal.toReal (eLpNorm
          (spatialDifferenceQuotient i h
            (D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)))) 2 (timeVelocityVolumeOn V))) ^ 2
      have hi : q beta j i ≤ ∑ i : Fin d, q beta j i :=
        Finset.single_le_sum (fun i _ => by dsimp [q]; positivity) (Finset.mem_univ i)
      have hj : (∑ i : Fin d, q beta j i) ≤
          ∑ j : Fin d, ∑ i : Fin d, q beta j i :=
        Finset.single_le_sum
          (fun j _ => Finset.sum_nonneg fun i _ => by dsimp [q]; positivity)
          (Finset.mem_univ j)
      have hbeta : (∑ j : Fin d, ∑ i : Fin d, q beta j i) ≤
          ∑ beta : ParabolicDerivativeIndex d M,
            ∑ j : Fin d, ∑ i : Fin d, q beta j i :=
        Finset.single_le_sum
          (fun beta _ => Finset.sum_nonneg fun j _ =>
            Finset.sum_nonneg fun i _ => by dsimp [q]; positivity)
          (Finset.mem_univ beta)
      rw [Lp.norm_toLp]
      exact (hi.trans (hj.trans hbeta)).trans (by
        simpa only [q, V, Etotal] using hjoint)
    have hnorm : ∀ (h : ℝ) (hh : 0 < h) (hhd : h < δ),
        ‖(hmem h hh hhd).toLp (spatialDifferenceQuotient i h G)‖ ≤
          Real.sqrt (C_DQ * Etotal) := by
      intro h hh hhd
      calc
        _ = Real.sqrt
            (‖(hmem h hh hhd).toLp (spatialDifferenceQuotient i h G)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (C_DQ * Etotal) := Real.sqrt_le_sqrt (hsq h hh hhd)
    simpa only [G] using
      exists_hasWeakVelocityPartialDerivOn_norm_le_of_uniform_spatialDifferenceQuotient
        V (isOpen_Ioo.prod hO₁) i G (hlocal beta j) δ
          (Real.sqrt (C_DQ * Etotal)) hδ hmem hnorm
  choose g hg hweak hnorm using hclose
  let H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ :=
    fun z beta j i => g beta j i z
  refine ⟨H, (fun beta j i => hg beta j i), (fun beta j i => hweak beta j i), ?_⟩
  have hentry : ∀ beta j i,
      (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
        (timeVelocityVolumeOn V))) ^ 2 ≤ C_DQ * Etotal := by
    intro beta j i
    have hs := hnorm beta j i
    rw [Lp.norm_toLp] at hs
    have hCE : 0 ≤ C_DQ * Etotal := mul_nonneg hC_DQ hEtotal
    have hsquared := (sq_le_sq₀ (ENNReal.toReal_nonneg) (Real.sqrt_nonneg _)).2 hs
    simpa only [Real.sq_sqrt hCE, H] using hsquared
  calc
    _ ≤ ∑ beta : ParabolicDerivativeIndex d M,
        ∑ j : Fin d, ∑ i : Fin d, C_DQ * Etotal :=
      Finset.sum_le_sum fun beta _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun i _ => hentry beta j i
    _ = C_H * Etotal := by simp [C_H]; ring

end HypoellipticAleksandrov.Parabolic
