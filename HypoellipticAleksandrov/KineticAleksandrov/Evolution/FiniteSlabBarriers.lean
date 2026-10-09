module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTransport
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal

/-!
# (A.1) on a finite slab

The `two_barriers` requires the boundary curve `γ` to be globally Lipschitz and the
operator bound `|L_ε F| ≤ M` for all `σ ≤ τ`.  Neither global premise follows from the standing
hypotheses (a continuous piecewise `C¹` curve is only Lipschitz on compact intervals).
`two_barriers_on_finite_slab` is the same barrier statement on the finite moving slab `[a, τ]`,
requiring the Lipschitz bound of `γ` and the operator bound only on `[a, τ]`.  The solution `u`
is still the solution on the whole past cylinder; the maximum principle is only applied on the
slab.  `M` can be discharged globally by `exists_uniform_terminalDatum_operator_bound`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- Lateral barrier for a viscous classical solution, in the collar, on a finite slab. -/
theorem classical_le_collarSupersolution_of_lipschitzOn {n : ℕ} {c : PDE.Vec n}
    {r₀ dstar : ℝ} (hd : 0 < dstar) (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n}
    (hγpw : IsContinuousPiecewiseC1 γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ) {a τ : ℝ} (haτ : a < τ)
    (hγL : CurveLipschitzOn γ Lγ (Icc a τ)) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r₀) γ B b ε τ F u)
    {FB : ℝ} (hFB : 0 ≤ FB)
    (hle : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, u p ≤ FB)
    (hterm0 : ∀ p ∈ evolutionTerminalClosure (PDE.euclideanBall c r₀) γ τ,
      (r₀ - dstar) ^ 2 ≤ centreSq c γ p → u p ≤ 0) :
    ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
      (r₀ - dstar) ^ 2 ≤ centreSq c γ p → u p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  have hΩo : IsOpen (PDE.euclideanBall c r₀) := PDE.isOpen_euclideanBall c r₀
  have hγ : Continuous γ := hγpw.1
  have hκ : 0 < collarKappa Lγ lam := div_pos (by linarith) hlam
  have hc0 : 0 ≤ FB / barrierW (collarKappa Lγ lam) dstar :=
    div_nonneg hFB (barrierW_pos hκ hd).le
  have hr₀ : 0 ≤ r₀ := by linarith
  have hGnn : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
      0 ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
    intro p hp
    exact mul_nonneg hc0 (collarBarrier_nonneg hκ hr₀
      (vecNormSq_le_of_mem_closure_movingDomain hp.2.2))
  have hslab : movingClosedSlab (PDE.euclideanBall c r₀) γ a τ ⊆
      evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ :=
    fun p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : movingActiveSlab (PDE.euclideanBall c r₀) γ a τ ⊆
      evolutionPastOpenCylinder (PDE.euclideanBall c r₀) γ τ :=
    fun p hp => ⟨hp.2.1, hp.2.2⟩
  obtain ⟨C₁, -, hC₁⟩ := hu.1
  have hchain := collar_chain_of_lipschitzOn (v := u) hd hdr hγpw hLγ hγL haτ hlam hB hb hε0
    hε1 hFB
    ⟨C₁, fun p hp => (le_abs_self _).trans (hC₁ p (hslab hp))⟩
    (hu.2.1.mono hslab)
    (fun p hp => hu.isSliceRegularAt hΩo hγ (hact hp))
    (fun p hp => by rw [hu.2.2.2.1 p (hact hp)])
    (fun p hp hfr => by
      rw [hu.2.2.2.2.2 p ⟨hp.2.1, hfr⟩])
    hle
    (fun p hp hpt => by
      have h1 := hterm0 p ⟨hpt, hpt ▸ hp.1.2.2⟩ hp.2
      have h2 := hGnn p hp.1
      linarith)
  exact fun p hp hS => hchain p ⟨hp, hS⟩

/-- (companion paper, A.1)., finite-slab form.  The two barriers for a viscous classical
terminal solution on the moving ball, with the Lipschitz bound of `γ` and the operator bound `M`
required only on the finite slab `[a, τ]`. -/
theorem two_barriers_on_finite_slab
    {n : ℕ} {c : PDE.Vec n} {r : ℝ} (hr : 0 < r)
    {γ : ℝ → PDE.Vec n} (hγ : IsContinuousPiecewiseC1 γ)
    (a τ : ℝ) (haτ : a < τ) (L : ℝ) (hL : 0 ≤ L)
    (hγL : ∀ s ∈ Icc a τ, ∀ t ∈ Icc a τ,
      PDE.vecEuclideanNorm (γ s - γ t) ≤ L * |s - t|)
    {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {L_b : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift L_b b)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r) γ τ F)
    (d : ℝ) (hd : 0 < d) (hdr : d < r / 4)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    (C M : ℝ) (hC : ∀ q, |F q| ≤ C)
    (hM : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ a τ,
      |viscousTransportedOperator B b ε
        (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r) γ B b ε τ F u) :
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ a τ,
      |u p| ≤ C * min 1
        (barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa L lam) d)) ∧
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ a τ,
      τ - d / (1 + L) ≤ p.time →
        |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M) := by
  have hΩo : IsOpen (PDE.euclideanBall c r) := PDE.isOpen_euclideanBall c r
  have hdr' : d < r := by linarith
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hWpos : 0 < barrierW (collarKappa L lam) d := barrierW_pos hκ hd
  have hγL' : CurveLipschitzOn γ L (Icc a τ) := hγL
  have hslab : movingClosedSlab (PDE.euclideanBall c r) γ a τ ⊆
      evolutionPastClosedCylinder (PDE.euclideanBall c r) γ τ :=
    fun p hp => ⟨hp.2.1, hp.2.2⟩
  refine ⟨?_, ?_⟩
  · intro p hp
    have hAbs := classical_abs_le_const hΩo hγ.1 hlam hB hb hε hε1 hu hC
    have hnu := hu.neg hΩo hγ.1
    rcases le_total 1 (barrierW (collarKappa L lam)
        (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa L lam) d) with h1 | h1
    · rw [min_eq_left h1]
      have := hAbs p (hslab hp)
      linarith
    · rw [min_eq_right h1]
      have hle : barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) ≤
            barrierW (collarKappa L lam) d := by
        rwa [div_le_one hWpos] at h1
      have hd' := le_of_barrierW_le hκ hle
      have hnorm : r - d ≤ PDE.vecEuclideanNorm (p.position - (γ p.time + c)) := by
        linarith
      have hS : (r - d) ^ 2 ≤ centreSq c γ p := by
        have h2 : (r - d) ^ 2 ≤ PDE.vecEuclideanNorm (p.position - (γ p.time + c)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hnorm 2
        rw [PDE.vecEuclideanNorm_sq] at h2
        exact h2
      have hup := classical_le_collarSupersolution_of_lipschitzOn (c := c) hd hdr' hγ hL haτ
        hγL' hlam hB hb hε hε1 hu hC0 (fun q hq => (le_abs_self _).trans (hAbs q (hslab hq)))
        (fun q hq hqS => by
          rw [hu.2.2.2.2.1 q hq, terminalDatum_eq_zero_of_collar hd hdr' hsupp hq.1 hqS])
        p hp hS
      have hdown := classical_le_collarSupersolution_of_lipschitzOn (c := c) hd hdr' hγ hL haτ
        hγL' hlam hB hb hε hε1 hnu hC0
        (fun q hq => (neg_le_abs _).trans (hAbs q (hslab hq)))
        (fun q hq hqS => by
          have h := hnu.2.2.2.2.1 q hq
          simp only [BoundedBorel.neg_apply] at h
          show -u q ≤ 0
          rw [h, terminalDatum_eq_zero_of_collar hd hdr' hsupp hq.1 hqS]
          simp)
        p hp hS
      have hG : collarSupersolution c r d L lam C γ p =
          C * (barrierW (collarKappa L lam)
              (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
            barrierW (collarKappa L lam) d) := by
        have : collarBarrier (collarKappa L lam) r (fun t => γ t + c) p =
            barrierW (collarKappa L lam)
              (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) := rfl
        unfold collarSupersolution
        rw [this]
        ring
      rw [← hG]
      have hdown' : -u p ≤ collarSupersolution c r d L lam C γ p := hdown
      exact abs_le.mpr ⟨by linarith, hup⟩
  · intro p₀ hp₀ hδ
    have hL1 : 0 < 1 + L := by linarith
    have hFzero : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (max a (τ - d / (1 + L))) τ,
        p.position ∈ frontier (movingDomain (PDE.euclideanBall c r) γ p.time) →
          F (p.position, p.velocity) = 0 := by
      intro p hp hfr
      have hp1 : τ - d / (1 + L) ≤ p.time := (le_max_right _ _).trans hp.1
      have hp0 : a ≤ p.time := (le_max_left _ _).trans hp.1
      by_contra hne
      have hmem : (p.position, p.velocity) ∈ tsupport (F : EvolutionAmbientState n → ℝ) :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      have h3 := hsupp _ hmem
      simp only at h3
      have hS := vecNormSq_eq_of_mem_frontier_movingDomain hfr
      have hnorm : PDE.vecEuclideanNorm (p.position - (γ p.time + c)) = r := by
        unfold PDE.vecEuclideanNorm
        rw [hS, Real.sqrt_sq hr.le]
      have htri : p.position - (γ p.time + c) =
          (p.position - (γ τ + c)) + (γ τ - γ p.time) := by abel
      have h4 := PDE.vecEuclideanNorm_add_le (p.position - (γ τ + c)) (γ τ - γ p.time)
      rw [← htri, hnorm] at h4
      have h5 := hγL τ ⟨haτ.le, le_rfl⟩ p.time ⟨hp0, hp.2.1⟩
      have h6 : |τ - p.time| = τ - p.time := abs_of_nonneg (by linarith [hp.2.1])
      rw [h6] at h5
      have h7 : L * (τ - p.time) ≤ L * (d / (1 + L)) :=
        mul_le_mul_of_nonneg_left (by linarith) hL
      have h8 : L * (d / (1 + L)) < d := by
        rw [← mul_div_assoc, div_lt_iff₀ hL1]
        nlinarith
      linarith
    exact classical_sub_terminalDatum_le_core_of_slab hΩo hγ.1 hlam hB hb hε hε1 hF.1 hC
      (a := max a (τ - d / (1 + L)))
      (fun p hp => hM p ⟨(le_max_left _ _).trans hp.1, hp.2.1, hp.2.2⟩) hu hFzero p₀
      ⟨max_le hp₀.1 hδ, hp₀.2.1, hp₀.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
