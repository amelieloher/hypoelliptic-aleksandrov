module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels

/-! # Nonzero-frequency blocks, conditional on the exact unit-block theorem -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Scaling

/-- Source scaled blocks in case W, relative only to the authorized source predecessors. -/
theorem nonzero_frequency_blocks_of_unitBlock (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (univ : Set (PDE.Vec d)) stationary)
        (K : MovingFiberKernel (univ : Set (PDE.Vec d)) stationary),
        RealizesTerminalEvolution univ stationary MeasurableSet.univ
          (zIndependentCoefficient B) id S K →
      ∀ (ξ : PDE.Vec d), ξ ≠ 0 →
      ∀ (s : ℝ) (v : PDE.Vec d) (q : EvolutionQuery (univ : Set (PDE.Vec d)) stationary),
        q.1 = (s, s + L * (PDE.vecEuclideanNorm ξ) ^ (-(2 / 3 : ℝ)), v, 0) →
      ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν → TV ν ≤ 1 - δ := by
  obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ := hblock
  refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
  intro B hB S K hreal ξ hξ s v q hq ν hν
  obtain ⟨hr, hr2, hrunit⟩ := frequency_radius_identities hξ
  let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ)), hr⟩
  let Φ := KineticAffineScaling.ofRadius s v 0 (identityDrift d) r
  let hm : Φ.MapsDomain univ stationary univ stationary :=
    KineticAffineScaling.mapsDomain_wholeSpace Φ
  let K' := KineticAffineScaling.pushKernel hm K
  let S' := fiberOperator K' MeasurableSet.univ
  have hB' := scaledCoefficient_sectionTwo lam Lam B hB s v r
  have hreal' : RealizesTerminalEvolution univ stationary MeasurableSet.univ
      (zIndependentCoefficient (scaledCoefficient B s v r)) (identityDrift d) S' K' :=
    realizes_ofRadius_wholeSpace s v 0 r hreal
  obtain ⟨hmono', hmargin', hcov'⟩ := iteration_evolution_clauses hEvol hd hlam hlamLam
    (scaledCoefficient B s v r) hB' S' K' hreal'
  let q' : EvolutionQuery univ stationary :=
    wholeSpaceQuery 0 L hL.le (0 : PDE.Vec d) 0
  let ν' := fourierKernel K' 0 L hL.le (r.1 ^ 3 • ξ) 0
  have hν' : IsFourierProjection K' q' (r.1 ^ 3 • ξ) ν' :=
    fourierKernel_spec K' 0 L hL.le _ 0
  have hsetting : SourceSetting lam Lam 1 1 univ (scaledCoefficient B s v r) id :=
    ⟨hB', identityDrift_smooth d, zero_lt_one, le_rfl, identityDrift_bounds d,
      Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  have hv' : (0 : PDE.Vec d) ∈ movingDomain univ stationary 0 := by
    change (0 : PDE.Vec d) ∈ movingDomain (wholeSpace d) (fun _ => 0) 0
    rw [movingDomain_wholeSpace]; exact mem_univ _
  have hL0 : (0 : ℝ) ≤ 0 + L := by linarith only [hL]
  have hq' : movingQuery 0 (0 + L) hL0 0 0 hv' = q' := by
    apply Subtype.ext
    simp only [movingQuery_val, zero_add]
    rfl
  have hνunit : IsFourierProjection K' (movingQuery 0 (0 + L) hL0 0 0 hv')
      (r.1 ^ 3 • ξ) ν' := by
    rw [hq']
    exact hν'
  have hunit' := hunit univ (scaledCoefficient B s v r) id hsetting rfl MeasurableSet.univ
    S' K' hreal' hmono' hmargin' hcov' (r.1 ^ 3 • ξ) hrunit
    0 0 hv' hL0 ν' hνunit
  have hquery : KineticAffineScaling.queryMap hm q' = q := by
    apply Subtype.ext
    rw [hq]
    change (s + r.1 ^ 2 * 0, s + r.1 ^ 2 * L,
      v + r.1 • (0 : PDE.Vec d), (0 : PDE.Vec d) +
        (r.1 ^ 2 * 0) • identityDrift d v + r.1 ^ 3 • (0 : PDE.Vec d)) = _
    simp only [mul_zero, add_zero, smul_zero, zero_smul]
    rw [hr2, mul_comm L]
  have hνmap : IsFourierProjection K (KineticAffineScaling.queryMap hm q') ξ ν := by
    rw [hquery]; exact hν
  have htv := (realizes_ofRadius_fourier_tv s v 0 r hreal hreal' q' ξ ν ν'
    hνmap hν').2
  unfold TV at hunit' ⊢
  change (totalVariationNorm ν).toReal ≤ 1 - δ
  rw [htv]
  exact hunit'

end HypoellipticAleksandrov.KineticAleksandrov.Decay
