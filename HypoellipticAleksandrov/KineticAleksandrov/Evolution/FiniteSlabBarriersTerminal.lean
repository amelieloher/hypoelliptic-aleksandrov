module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierFinite

/-!
# Terminal barrier on a finite slab, and the uniform operator bound

The two barriers in the proof of the companion paper, Proposition 2.1.

* `classical_sub_terminalDatum_le_core_of_slab` is the
  `classical_sub_terminalDatum_le_core` with the bound `|L_ε F| ≤ M` required only on the closed
  moving slab `[a, τ]` (the maximum principle is applied only there), not on all of `σ ≤ τ`.
* `exists_uniform_terminalDatum_operator_bound` shows that the bound `M` exists, uniformly
  in `σ` and `ε ∈ [0, 1]`, for every smooth compactly supported terminal datum, from the
  everywhere Loewner bound on `B` and the Lipschitz drift alone.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- Terminal barrier core on a finite slab: if the terminal datum vanishes on the lateral
frontier of the slab `[a, τ]` and `|L_ε F| ≤ M` on the slab, then `|u - F| ≤ (τ - σ) M` there. -/
theorem classical_sub_terminalDatum_le_core_of_slab {n : ℕ} {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {FB M : ℝ} (hFB : ∀ q, |F q| ≤ FB) {a : ℝ}
    (hM : ∀ p ∈ movingClosedSlab Ω γ a τ,
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ} (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u)
    (hlatF : ∀ p ∈ movingClosedSlab Ω γ a τ,
      p.position ∈ frontier (movingDomain Ω γ p.time) → F (p.position, p.velocity) = 0) :
    ∀ p ∈ movingClosedSlab Ω γ a τ, |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  obtain ⟨C₁, -, hC₁⟩ := hu.1
  have hFcont : Continuous (fun q : KineticPoint n => F (q.position, q.velocity)) :=
    hF.continuous.comp (continuous_position.prodMk continuous_velocity)
  have hslab : ∀ a, movingClosedSlab Ω γ a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω γ a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  intro p₀ hp₀
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM p₀ hp₀)
  have side : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * (u p₀ - F (p₀.position, p₀.velocity)) + M * (p₀.time - τ) ≤ 0 := by
    intro s hs
    have hres := growth_comparison (a := a) (T := τ)
      (u := fun q => s * (u q - F (q.position, q.velocity)) + M * (q.time - τ))
      hΩ hγ hlam hB hb hε0 hε1 ?_ ?_ ?_ ?_ ?_ ?_ p₀ hp₀
    · exact hres
    · refine ⟨C₁ + FB, fun p hp => ?_⟩
      have h1 := hC₁ p (hslab _ hp)
      have h2 := hFB (p.position, p.velocity)
      have h3 : M * (p.time - τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0 (by linarith [hp.2.1])
      have h4 := abs_le.mp h1
      have h5 := abs_le.mp h2
      show s * (u p - F (p.position, p.velocity)) + M * (p.time - τ) ≤ C₁ + FB
      rcases hs with rfl | rfl <;> nlinarith [h4.1, h4.2, h5.1, h5.2]
    · exact (((hu.2.1.mono (hslab _)).sub hFcont.continuousOn).const_smul s).add
        ((continuous_const.mul (continuous_time.sub continuous_const)).continuousOn)
    · intro p hp
      have hr := hu.isSliceRegularAt hΩ hγ (hact _ hp)
      exact (((hr.sub (isSliceRegularAt_terminalDatum hF p)).const_mul s).add
        ((isSliceRegularAt_time_sub τ p).const_mul M))
    · intro p hp
      have hr := hu.isSliceRegularAt hΩ hγ (hact _ hp)
      have hF' := isSliceRegularAt_terminalDatum hF p
      have hT := isSliceRegularAt_time_sub (n := n) τ p
      have e1 : viscousTransportedOperator B b ε
          (fun q => s * (u q - F (q.position, q.velocity)) + M * (q.time - τ)) p =
          viscousTransportedOperator B b ε (fun q => s * (u q - F (q.position, q.velocity))) p +
          viscousTransportedOperator B b ε (fun q => M * (q.time - τ)) p :=
        viscousTransportedOperator_add (u := fun q => s * (u q - F (q.position, q.velocity)))
          (v := fun q => M * (q.time - τ)) ((hr.sub hF').const_mul s) (hT.const_mul M)
      have e2 : viscousTransportedOperator B b ε
          (fun q => s * (u q - F (q.position, q.velocity))) p =
          s * viscousTransportedOperator B b ε (fun q => u q - F (q.position, q.velocity)) p :=
        viscousTransportedOperator_const_mul s (hr.sub hF')
      have e3 := viscousTransportedOperator_sub (B := B) (b := b) (ε := ε) hr hF'
      have e4 : viscousTransportedOperator B b ε (fun q => M * (q.time - τ)) p = M := by
        rw [viscousTransportedOperator_const_mul M hT, viscousTransportedOperator_time_sub]
        ring
      have hop := hu.2.2.2.1 p (hact _ hp)
      have hMp := abs_le.mp (hM p ⟨hp.1, hp.2.1.le, subset_closure hp.2.2⟩)
      rw [e1, e2, e3, e4, hop]
      rcases hs with rfl | rfl <;> nlinarith [hMp.1, hMp.2]
    · intro p hp hpT
      have hterm : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hpT ▸ hp.2.2⟩
      have e1 := hu.2.2.2.2.1 p hterm
      show s * (u p - F (p.position, p.velocity)) + M * (p.time - τ) ≤ 0
      rw [e1, hpT]
      simp
    · intro p hp hfr
      have hlat : p ∈ evolutionLateralFrontier Ω γ τ := ⟨hp.2.1, hfr⟩
      show s * (u p - F (p.position, p.velocity)) + M * (p.time - τ) ≤ 0
      rw [hu.2.2.2.2.2 p hlat, hlatF p hp hfr]
      have : M * (p.time - τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0 (by linarith [hp.2.1])
      simpa using this
  have h1 := side 1 (Or.inl rfl)
  have h2 := side (-1) (Or.inr rfl)
  rw [abs_le]
  constructor <;> nlinarith [h1, h2]

/-- (companion paper, A.1).  For a smooth compactly supported terminal datum, the operator
`L_ε F` is bounded uniformly in `p`, in the time, and in `ε ∈ [0, 1]`.  This uses only the
everywhere Loewner bound on `B` and the Lipschitz drift, no derivative bound on `B`. -/
theorem exists_uniform_terminalDatum_operator_bound {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ p : KineticPoint n,
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M := by
  obtain ⟨M, hM⟩ := exists_terminalGenerator_bound hF.1 hF.2.1 hlam hB hb
  refine ⟨max M 0, le_max_right _ _, fun ε hε0 hε1 p => ?_⟩
  exact (hM ε hε0 hε1 p).trans (le_max_left _ _)

end HypoellipticAleksandrov.KineticAleksandrov
