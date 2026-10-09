module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue

/-! # Compact terminal supports under a continuous moving boundary -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology

/-- The time-state set of interior terminal states is open for a continuous motion. -/
theorem isOpen_terminal_state_graph {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsOpen {q : ℝ × EvolutionAmbientState n | q.2 ∈ evolutionStateSet Ω γ q.1} := by
  have hc : Continuous (fun q : ℝ × EvolutionAmbientState n => q.2.1 - γ q.1) :=
    (continuous_fst.comp continuous_snd).sub (hγ.comp continuous_fst)
  convert hΩ.preimage hc using 1
  ext q
  exact and_iff_left (mem_univ _ ) |>.trans mem_movingDomain_iff

/-- A compact interior terminal support remains interior for all nearby terminal times. -/
theorem IsCompact.eventually_subset_terminal_state
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {K : Set (EvolutionAmbientState n)} (hK : IsCompact K) {τ : ℝ}
    (hKT : K ⊆ evolutionStateSet Ω γ τ) :
    ∀ᶠ t in 𝓝 τ, K ⊆ evolutionStateSet Ω γ t := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  exact (isOpen_terminal_state_graph hΩ hγ).mem_nhds (hKT hx)

/-- The times at which a fixed compact set is an interior terminal support form an open set. -/
theorem IsCompact.isOpen_terminal_support_times
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {K : Set (EvolutionAmbientState n)} (hK : IsCompact K) :
    IsOpen {τ : ℝ | K ⊆ evolutionStateSet Ω γ τ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro τ hτ
  exact IsCompact.eventually_subset_terminal_state hΩ hγ hK hτ


/-- A compact interior datum remains a valid terminal datum on a whole time window. -/
theorem IsSmoothCompactTerminalDatum.exists_terminal_window
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, dist t τ < δ →
      IsSmoothCompactTerminalDatum Ω γ t F := by
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    (IsCompact.eventually_subset_terminal_state hΩ hγ hF.2.1 hF.2.2)
  exact ⟨δ, hδ, fun t ht => ⟨hF.1, hF.2.1, hb ht⟩⟩

/-- If a fixed datum is supported inside every fiber of a slab, it vanishes on each
lateral frontier of that slab. -/
theorem terminalDatum_zero_lateral_of_support
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    {a T : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hs : ∀ t ∈ Icc a T, tsupport F ⊆ evolutionStateSet Ω γ t) :
    ∀ p ∈ movingClosedSlab Ω γ a T,
      p.position ∈ frontier (movingDomain Ω γ p.time) → F (p.position, p.velocity) = 0 := by
  intro p hp hfr
  apply Function.notMem_support.mp
  intro hnon
  have hinside := hs p.time ⟨hp.1, hp.2.1⟩ (subset_closure hnon)
  rw [(isOpen_movingDomain hΩ p.time).frontier_eq] at hfr
  exact hfr.2 hinside.1

/-- The actual kinetic starting point of a valid evolution query. -/
def evolutionQueryPoint {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (q : EvolutionQuery Ω γ) : KineticPoint n := ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩

/-- Extracting the actual starting point is continuous on the valid query subtype. -/
theorem continuous_evolutionQueryPoint {n : ℕ} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} : Continuous (@evolutionQueryPoint n Ω γ) := by
  exact KineticPoint.continuous_mk (continuous_fst.comp continuous_subtype_val)
    (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))

end HypoellipticAleksandrov.KineticAleksandrov
