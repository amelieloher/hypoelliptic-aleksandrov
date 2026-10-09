module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleAttainment
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleLocal

/-!
# Strict maximum exclusion on an inset moving tube

The inset avoids any regularity requirement at the original initial time.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped Topology

/-- A strictly positive operator excludes positive maxima on any inset tube.
All maximum-attainment and moving-boundary steps are discharged internally. -/
theorem nonpos_on_inset_maximumClosedTube_of_strict {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a α b : ℝ}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ}
    (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω)) (haα : a < α)
    (hγ : ContinuousOn γ (Icc a b))
    (hu : ContinuousOn u (maximumClosedTube Ω γ a b))
    (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b))
    (hreg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : ∀ p ∈ maximumOpenTube Ω γ a b,
      (B p.time p.position p.velocity).PosSemidef)
    (hstrict : ∀ p ∈ maximumOpenTube Ω γ a b, 0 < transportedForwardOperator B drift u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ a b, p.time = b → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ a b,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) :
    ∀ q ∈ maximumClosedTube Ω γ α b, u q ≤ 0 := by
  have hsub : maximumClosedTube Ω γ α b ⊆ maximumClosedTube Ω γ a b := by
    intro p hp
    exact ⟨⟨haα.le.trans hp.1.1, hp.1.2⟩, hp.2⟩
  have htSub : Icc α b ⊆ Icc a b := Icc_subset_Icc_left haα.le
  have hcontrol' : IsTransportIndependentOn u (maximumClosedTube Ω γ α b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ α b) := by
    rcases hcontrol with hi | hn
    · exact Or.inl (fun p hp => hi p (hsub hp))
    · right
      intro M
      obtain ⟨R, hR, hb⟩ := hn M
      exact ⟨R, hR, fun p hp => hb p (hsub hp)⟩
  intro q hq
  by_contra hnot
  obtain ⟨p, hp, hpos, hmax⟩ := exists_positive_isMaxOn_maximumClosedTube hcΩ
    (hγ.mono htSub) (hu.mono hsub) hcontrol' hq (lt_of_not_ge hnot)
  have hpFull := hsub hp
  have hpt : p.time < b := lt_of_le_of_ne hp.1.2 (by
    intro heq
    exact (not_le_of_gt hpos) (hterminal p hpFull heq))
  have hpv : p.position ∈ movingDomain Ω γ p.time := by
    by_contra hv
    have hfront : p.position ∈ frontier (movingDomain Ω γ p.time) := by
      rw [(isOpen_movingDomain hΩ p.time).frontier_eq]
      exact ⟨hp.2, hv⟩
    exact (not_le_of_gt hpos) (hlateral p hpFull hfront)
  have hpOpen : p ∈ maximumOpenTube Ω γ a b :=
    ⟨⟨haα.trans_le hp.1.1, hpt⟩, hpv⟩
  obtain ⟨hut, huv, huz⟩ := hreg p hpOpen
  have hγp : ContinuousAt γ p.time :=
    (hγ p.time hpFull.1).continuousAt (Icc_mem_nhds hpOpen.1.1 hpOpen.1.2)
  exact (not_le_of_gt (hstrict p hpOpen))
    (transportedForwardOperator_nonpos_at_tube_max hΩ hγp ⟨hp.1.1, hpt⟩ hpv
      hmax hut huv huz (hB p hpOpen))

end HypoellipticAleksandrov.KineticAleksandrov.Decay
