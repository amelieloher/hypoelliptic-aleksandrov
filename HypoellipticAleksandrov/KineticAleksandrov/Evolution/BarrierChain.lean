module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierPiece

/-!
# Collar comparison across the pieces of a piecewise `C¹` curve

The curve `γ` is continuous and piecewise `C¹`.  Choose a partition `a = t₀ < ⋯ < t_{N+1} = τ`
whose pieces carry `C¹` regularity, and apply `collar_piece` successively from the top piece
downwards; the top-face data of each piece is supplied by the piece above it.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- Monotonicity of the closed moving slab in its time interval. -/
theorem movingClosedSlab_mono {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {a a' b b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    movingClosedSlab Ω γ a' b' ⊆ movingClosedSlab Ω γ a b :=
  fun _ hp => ⟨ha.trans hp.1, hp.2.1.trans hb, hp.2.2⟩

/-- Monotonicity of the active moving slab in its time interval. -/
theorem movingActiveSlab_mono {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {a a' b b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    movingActiveSlab Ω γ a' b' ⊆ movingActiveSlab Ω γ a b :=
  fun _ hp => ⟨ha.trans hp.1, hp.2.1.trans_le hb, hp.2.2⟩

/-- Collar comparison on `[a, τ]` for a piecewise `C¹` Lipschitz curve. -/
theorem collar_chain {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγpw : IsContinuousPiecewiseC1 γ) {Lγ : ℝ}
    (hLγ : 0 ≤ Lγ) (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {a τ : ℝ} (haτ : a < τ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {FB : ℝ} (hFB : 0 ≤ FB) {v : KineticPoint n → ℝ}
    (hbdd : ∃ M, ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, v p ≤ M)
    (hcont : ContinuousOn v (movingClosedSlab (PDE.euclideanBall c r₀) γ a τ))
    (hreg : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ a τ, IsSliceRegularAt v p)
    (hop : ∀ p ∈ movingActiveSlab (PDE.euclideanBall c r₀) γ a τ,
      0 ≤ viscousTransportedOperator B b ε v p)
    (hlat : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ,
      p.position ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ p.time) → v p ≤ 0)
    (hFBle : ∀ p ∈ movingClosedSlab (PDE.euclideanBall c r₀) γ a τ, v p ≤ FB)
    (htop : ∀ p ∈ collarClosed c r₀ dstar γ a τ, p.time = τ →
      v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p) :
    ∀ p ∈ collarClosed c r₀ dstar γ a τ, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  obtain ⟨N, t, ht, h0, hl, hdiff⟩ := exists_partition_differentiableAt hγpw haτ
  let motive : Fin (N + 2) → Prop := fun i =>
    ∀ p ∈ collarClosed c r₀ dstar γ (t i) τ, v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p
  have hmain : ∀ i, motive i := by
    intro i
    refine Fin.reverseInduction (motive := motive) ?_ ?_ i
    · intro p hp
      have hpτ : p.time = τ := by
        have h1 := hp.1.1
        have h2 := hp.1.2.1
        rw [hl] at h1
        exact le_antisymm h2 h1
      exact htop p ⟨⟨by rw [hpτ]; exact haτ.le, hp.1.2.1, hp.1.2.2⟩, hp.2⟩ hpτ
    · intro i hprev p hp
      have hlt : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
      have ha : a ≤ t i.castSucc := by
        rw [← h0]
        exact ht.monotone (Fin.zero_le _)
      have hτ : t i.succ ≤ τ := by
        rw [← hl]
        exact ht.monotone (Fin.le_last _)
      by_cases hge : t i.succ ≤ p.time
      · exact hprev p ⟨⟨hge, hp.1.2.1, hp.1.2.2⟩, hp.2⟩
      · have hlt' : p.time < t i.succ := not_le.mp hge
        have hres := collar_piece hd hdr hγpw.1 hLγ hγL hlt (hdiff i) hlam hB hb hε0 hε1 hFB
          (v := v)
          (by
            obtain ⟨M, hM⟩ := hbdd
            exact ⟨M, fun q hq => hM q (movingClosedSlab_mono ha hτ hq)⟩)
          (hcont.mono (movingClosedSlab_mono ha hτ))
          (fun q hq => hreg q (movingActiveSlab_mono ha hτ hq))
          (fun q hq => hop q (movingActiveSlab_mono ha hτ hq))
          (fun q hq => hlat q (movingClosedSlab_mono ha hτ hq))
          (fun q hq => hFBle q (movingClosedSlab_mono ha hτ hq))
          (fun q hq hqt => hprev q ⟨⟨hqt.ge, by rw [hqt]; exact hτ, hq.1.2.2⟩, hq.2⟩)
        exact hres p ⟨⟨hp.1.1, hlt'.le, hp.1.2.2⟩, hp.2⟩
  have h := hmain 0
  have h' : ∀ p ∈ collarClosed c r₀ dstar γ (t 0) τ,
      v p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := h
  rw [h0] at h'
  exact h'

end HypoellipticAleksandrov.KineticAleksandrov
