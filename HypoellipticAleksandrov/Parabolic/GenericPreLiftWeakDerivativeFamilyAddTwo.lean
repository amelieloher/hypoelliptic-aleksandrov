module

public import HypoellipticAleksandrov.Parabolic.GenericParabolicWeakDerivativeFamilyAddTwo
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftTimeSuccessorRecovery

/-!
# Generic pre-lift add-two weak-derivative family

This module assembles the recovered Hessian and canonical time-successor
representatives from one generic pre-lift step into a coherent parabolic
weak-derivative family through weight `M + 2`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal MatrixOrder

/-- Exact recovered-Hessian and coherent add-two-family conclusion of one
generic pre-lift bootstrap step. -/
def GenericPreliftAddTwoFamilyConclusion
    {d M : ℕ} (V : Set (TimeVelocity d))
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    {F : ℝ → PDE.Vec d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (Cnext : ℝ) : Prop :=
  ∃ H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ,
    ∃ Dnext : ParabolicWeakDerivativeFamily d (M + 2) V u,
      (∀ alpha : ParabolicDerivativeIndex d (M + 1),
        Dnext.representative
          (ParabolicDerivativeIndex.castLE (by omega) alpha) =
            D.representative alpha) ∧
      (∀ beta : ParabolicDerivativeIndex d M,
        Dnext.representative
          (ParabolicDerivativeIndex.sourceTime
            (L := M + 2) (by omega) beta) =ᵐ[timeVelocityVolumeOn V]
          genericPreliftTimeSuccessorResidual a b c D E H beta) ∧
      (∀ beta : ParabolicDerivativeIndex d M, ∀ j i : Fin d,
        Dnext.representative
          (ParabolicDerivativeIndex.sourceVelocityTwo
            (L := M + 2) (by omega) beta j i) =ᵐ[timeVelocityVolumeOn V]
          fun z => H z beta j i) ∧
      ParabolicWeakDerivativeFamily.squaredL2Norm Dnext ≤
        Cnext *
          (ParabolicWeakDerivativeFamily.squaredL2Norm D +
            ParabolicWeakDerivativeFamily.squaredL2Norm E)

/-- One generic pre-lift step assembles the recovered spatial and time
successors into a coherent family through weight `M + 2`. -/
theorem exists_genericPrelift_addTwo_weakDerivativeFamily_estimate
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
    ∃ Cnext : ℝ, 0 ≤ Cnext ∧
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
        GenericPreliftAddTwoFamilyConclusion
          (Set.Ioo t₁ t₂ ×ˢ O₁) a b c D E Cnext := by
  classical
  obtain ⟨C_HW, hC_HW, hpredecessor⟩ :=
    exists_genericPrelift_hessian_timeSuccessor_family_estimate
      d M hM t₀ t₁ t₂ t₃ ht₀₁ ht₁₂ ht₂₃ O₀ O₁ hO₀ hO₁ hO₁ne
        hO₁compact hO₁O₀ lam Lam hlam hlamLam Ba Bb Bc hBa hBb hBc
  let N : ℝ := Fintype.card (ParabolicDerivativeIndex d (M + 2))
  let Cnext : ℝ := N * (1 + C_HW)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hCnext : 0 ≤ Cnext := mul_nonneg hN (add_nonneg zero_le_one hC_HW)
  refine ⟨Cnext, hCnext, ?_⟩
  intro a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
  obtain ⟨H, hHmem, hHweak, hWmem, hWweak, hHWnorm⟩ :=
    hpredecessor a b c F u D E hSymm hEll ha hb hc haBound hbBound hcBound hEq
  let U := Set.Ioo t₀ t₃ ×ˢ O₀
  let V := Set.Ioo t₁ t₂ ×ˢ O₁
  have hVopen : IsOpen V := isOpen_Ioo.prod hO₁
  have hVU : V ⊆ U := Set.prod_mono
    (Set.Ioo_subset_Ioo ht₀₁.le ht₂₃.le) (subset_closure.trans hO₁O₀)
  obtain ⟨Dnext, hDold, hDtime, hDvelocity, hDnorm⟩ :=
    ParabolicDerivativeIndex.exists_parabolicWeakDerivativeFamily_add_two_of_hessian_timeSuccessors
      d M hM hVopen (D.restrict hVU) H
        (fun beta => genericPreliftTimeSuccessorResidual a b c D E H beta)
        hHmem (by
          intro beta j i
          simpa only [ParabolicWeakDerivativeFamily.restrict_representative] using
            hHweak beta j i)
        hWmem (by
          intro beta
          simpa only [ParabolicWeakDerivativeFamily.restrict_representative] using
            hWweak beta)
  refine ⟨H, Dnext, ?_, hDtime, hDvelocity, ?_⟩
  · intro alpha
    simpa only [ParabolicWeakDerivativeFamily.restrict_representative] using hDold alpha
  · have hDrestrict :=
      ParabolicWeakDerivativeFamily.squaredL2Norm_restrict_le D hVU
    have hEnorm : 0 ≤ ParabolicWeakDerivativeFamily.squaredL2Norm E :=
      ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg E
    have htotal : 0 ≤ ParabolicWeakDerivativeFamily.squaredL2Norm D +
        ParabolicWeakDerivativeFamily.squaredL2Norm E := add_nonneg
      (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D) hEnorm
    calc
      ParabolicWeakDerivativeFamily.squaredL2Norm Dnext ≤
          N * (ParabolicWeakDerivativeFamily.squaredL2Norm (D.restrict hVU) +
            ((∑ beta : ParabolicDerivativeIndex d M,
                ∑ j : Fin d, ∑ i : Fin d,
                  (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
                    (timeVelocityVolumeOn V))) ^ 2) +
              ∑ beta : ParabolicDerivativeIndex d M,
                (ENNReal.toReal (eLpNorm
                  (genericPreliftTimeSuccessorResidual a b c D E H beta) 2
                  (timeVelocityVolumeOn V))) ^ 2)) := by
        simpa only [N, add_assoc] using hDnorm
      _ ≤ N * (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          C_HW * (ParabolicWeakDerivativeFamily.squaredL2Norm D +
            ParabolicWeakDerivativeFamily.squaredL2Norm E)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hDrestrict hHWnorm) hN
      _ ≤ N * ((1 + C_HW) *
          (ParabolicWeakDerivativeFamily.squaredL2Norm D +
            ParabolicWeakDerivativeFamily.squaredL2Norm E)) := by
        apply mul_le_mul_of_nonneg_left _ hN
        calc
          _ ≤ (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E) +
              C_HW * (ParabolicWeakDerivativeFamily.squaredL2Norm D +
                ParabolicWeakDerivativeFamily.squaredL2Norm E) :=
            add_le_add (le_add_of_nonneg_right hEnorm) le_rfl
          _ = _ := by ring
      _ = Cnext * (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          ParabolicWeakDerivativeFamily.squaredL2Norm E) := by
        dsimp only [Cnext]
        rw [mul_assoc]

end HypoellipticAleksandrov.Parabolic
