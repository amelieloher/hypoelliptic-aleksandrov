module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Minorant
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Trimming
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
import Mathlib.MeasureTheory.Measure.Real

/-! # Integrating the source minorant and selecting common marginals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

private theorem marginal_query_eq {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (B : CoefficientField d)
    (K : MovingFiberKernel D γ)
    (hpar : HasParabolicMarginalBundle D γ hD (zIndependentCoefficient B) K)
    (s T : ℝ) (hsT : s ≤ T) (p : EvolutionState D γ s) :
    P K hD (scalarQuery s T hsT p.1.1 p.2.1) =
      (K.master (evolutionQueryOfState D γ s T hsT p)).map Prod.fst := by
  obtain ⟨Q, hfirst, _⟩ := hpar (fun _ _ _ _ => rfl)
  change Measure.map Subtype.val
    (parabolicMarginalKernel K hD s T hsT ⟨p.1.1, p.2.1⟩) = _
  rw [hfirst s T hsT ⟨p.1.1, p.2.1⟩ p.1.2,
    K.map_fiberFirstMarginal_eq_firstMarginal hD s T hsT]
  rfl

private theorem integrated_minorant {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel D γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState D γ s)) [IsFiniteMeasure R]
    (a h : ℝ) (ha : 0 < a) (hmass : R.real univ = a)
    (ν : Measure (PDE.Vec d))
    (hminor : ∀ᵐ p ∂R, ENNReal.ofReal h • ν ≤
      (K.master (evolutionQueryOfState D γ s T hsT p)).map Prod.fst) :
    ENNReal.ofReal (a * h) • ν ≤ (continuedMeasure K hsT R).map Prod.fst := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_fst hA, continuedMeasure_apply K hsT R (measurable_fst hA)]
  have hmass' : R univ = ENNReal.ofReal a := by
    rw [← hmass]
    exact (ofReal_measureReal (measure_ne_top _ _)).symm
  calc
    ENNReal.ofReal (a * h) * ν A =
        ∫⁻ _p, ENNReal.ofReal h * ν A ∂R := by
      rw [lintegral_const, hmass', ENNReal.ofReal_mul ha.le]
      ring
    _ ≤ _ := lintegral_mono_ae (by
      filter_upwards [hminor] with p hp
      have he := hp A
      simpa only [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply measurable_fst hA] using he)

/-- Integrating the source terminal minorant supplies two dominated portions
with exactly the same first marginal and the uniform source mass floor. -/
theorem continued_common_minorant_trimming (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ h q0 : ℝ, 0 < h ∧ 0 < q0 ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (v0 : PDE.Vec d) (ρ T : ℝ), v0 ∈ D → 0 < ρ →
        PDE.euclideanBall v0 (4 * ρ) ⊆ D →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * ρ)) stationary)
        (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary),
        RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) K →
        IsDomainMonotoneEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (zIndependentCoefficient B) b K →
      ∀ (s a η : ℝ), s = T - 4 * ρ ^ 2 →
      ∀ (hsT : s ≤ T), 0 < a → 0 < η → η < ρ →
      ∀ (R1 R2 : Measure (EvolutionState (PDE.euclideanBall v0 (4 * ρ)) stationary s)),
        IsFiniteMeasure R1 → IsFiniteMeasure R2 →
        R1.real univ = a → R2.real univ = a →
        (∀ᵐ p ∂R1, p.1.1 ∈ PDE.euclideanBall v0 η) →
        (∀ᵐ p ∂R2, p.1.1 ∈ PDE.euclideanBall v0 η) →
      ∀ (E1 E2 M : Measure (EvolutionAmbientState d)), IsFiniteMeasure M →
        (∀ A, MeasurableSet A → E1 A =
          ∫⁻ p, K.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1) →
        (∀ A, MeasurableSet A → E2 A =
          ∫⁻ p, K.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2) →
        E1 + E2 ≤ M →
      ∀ (qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
        qlate.1 = (T - ρ ^ 2, T, v0) →
        let Θ := ENNReal.ofReal (a * h) •
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
        Θ ≤ E1.map Prod.fst ∧ Θ ≤ E2.map Prod.fst ∧ a * h * q0 ≤ Θ.real univ ∧
        ∃ F1 F2 : Measure (EvolutionAmbientState d),
          F1 ≤ E1 ∧ F2 ≤ E2 ∧ F1 + F2 ≤ M ∧
          F1.map Prod.fst = Θ ∧ F2.map Prod.fst = Θ := by
  obtain ⟨h, q0, hh, hq0, hminor⟩ := common_terminal_minorant d hd lam Lam hlam hlamLam
  refine ⟨h, q0, hh, hq0, ?_⟩
  intro m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar hmono
    s a η hs hsT ha hη hηρ R1 R2 hf1 hf2 hmass1 hmass2 hsupport1 hsupport2
    E1 E2 M hfM hE1 hE2 hdom qlate hql
  let ν := P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
  let Θ := ENNReal.ofReal (a * h) • ν
  have hpoint (R : Measure (EvolutionState (PDE.euclideanBall v0 (4 * ρ)) stationary s))
      (hsupport : ∀ᵐ p ∂R, p.1.1 ∈ PDE.euclideanBall v0 η) :
      ∀ᵐ p ∂R, ENNReal.ofReal h • ν ≤
        (K.master (evolutionQueryOfState _ stationary s T hsT p)).map Prod.fst := by
    filter_upwards [hsupport] with p hp
    have hpρ : p.1.1 ∈ PDE.euclideanBall v0 ρ :=
      PDE.euclideanBall_mono hη.le hηρ.le hp
    have hh' := (hminor m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar
      hmono (scalarQuery s T hsT p.1.1 p.2.1) qlate
      (by simp only [scalarQuery]; exact Prod.ext hs (Prod.ext rfl rfl)) hql hpρ).1
    rw [marginal_query_eq (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
      B K hpar s T hsT p] at hh'
    exact hh'
  have heq1 : E1 = continuedMeasure K hsT R1 := eq_continuedMeasure_of_apply K hsT R1 hE1
  have heq2 : E2 = continuedMeasure K hsT R2 := eq_continuedMeasure_of_apply K hsT R2 hE2
  have hmin1 : Θ ≤ E1.map Prod.fst := by
    rw [heq1]
    exact integrated_minorant K hsT R1 a h ha hmass1 ν (hpoint R1 hsupport1)
  have hmin2 : Θ ≤ E2.map Prod.fst := by
    rw [heq2]
    exact integrated_minorant K hsT R2 a h ha hmass2 ν (hpoint R2 hsupport2)
  have hfE1 : IsFiniteMeasure E1 := heq1.symm ▸ inferInstance
  have hfE2 : IsFiniteMeasure E2 := heq2.symm ▸ inferInstance
  have hνmass : q0 ≤ ν.real univ := by
    let p : EvolutionPosition (PDE.euclideanBall v0 (4 * ρ)) stationary s :=
      ⟨v0, by
        rw [movingDomain_stationary]
        simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_self,
          PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
          using sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hρ)⟩
    have hpρ : v0 ∈ PDE.euclideanBall v0 ρ := by
      simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_self,
        PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
        using sq_pos_of_pos hρ
    have he := (hminor m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar
      hmono (scalarQuery s T hsT v0 p.2) qlate
      (by simp only [scalarQuery]; exact Prod.ext hs (Prod.ext rfl rfl)) hql hpρ).2
    have hfν : IsFiniteMeasure ν := inferInstance
    have h' := ENNReal.toReal_mono (measure_ne_top ν univ)
      (he.trans (measure_mono (subset_univ _)))
    simpa only [ENNReal.toReal_ofReal hq0.le, measureReal_def] using h'
  have hfloor : a * h * q0 ≤ Θ.real univ := by
    rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (mul_pos ha hh).le]
    exact mul_le_mul_of_nonneg_left hνmass (mul_pos ha hh).le
  obtain ⟨g1, hg1, hgle1, hΘ1, hmap1, hF1⟩ := exists_trimming_of_le_map_fst E1 Θ hmin1
  obtain ⟨g2, hg2, hgle2, hΘ2, hmap2, hF2⟩ := exists_trimming_of_le_map_fst E2 Θ hmin2
  exact ⟨hmin1, hmin2, hfloor, E1.withDensity (g1 ∘ Prod.fst),
    E2.withDensity (g2 ∘ Prod.fst), hF1, hF2, (add_le_add hF1 hF2).trans hdom,
    hmap1, hmap2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
