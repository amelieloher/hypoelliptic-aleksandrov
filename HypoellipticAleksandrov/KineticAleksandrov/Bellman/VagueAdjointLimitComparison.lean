module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitOrder
import Mathlib.Tactic

/-! # Elliptic comparison survives vague convergence -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Constant scalar multiplication preserves vague convergence. -/
theorem IsBellmanVagueLimit.smul {mu : ℕ → Measure BellmanPuncturedPlane}
    {nu : Measure BellmanPuncturedPlane} (h : IsBellmanVagueLimit mu nu) (c : ENNReal) :
    IsBellmanVagueLimit (fun n => c • mu n) (c • nu) := by
  intro f hf hfc
  simp only [integral_smul_measure]
  exact (h f hf hfc).const_smul c.toReal

/-- Positive compact tests transfer an ordered sequence to ordered Radon limits. -/
theorem bellman_vague_limit_le (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (he : ∀ n, IsFiniteMeasureOnCompacts (eta n))
    (hmInf : IsBellmanRadon muInf) (heInf : IsBellmanRadon etaInf)
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf)
    (hle : ∀ n, mu n ≤ eta n) : muInf ≤ etaInf := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  let := hmInf.1
  let := hmInf.2
  let := heInf.1
  let (n : ℕ) : IsFiniteMeasureOnCompacts (eta n) := he n
  apply bellman_measure_le_of_positive_tests
  intro f hf
  exact le_of_tendsto_of_tendsto' (hmv f f.continuous f.hasCompactSupport)
    (hev f f.continuous f.hasCompactSupport) (fun n => integral_mono_measure (hle n)
      (Eventually.of_forall hf) f.integrable)

end HypoellipticAleksandrov.KineticAleksandrov
