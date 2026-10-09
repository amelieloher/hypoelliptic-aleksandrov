module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
# Compact moving tubes for maximum attainment

The velocity carrier is the existing translated evolution domain. Position
truncation uses the explicit Euclidean ball, not the inherited product metric.
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov Set

/-- The finite closed moving tube with unrestricted transported coordinate. -/
def maximumClosedTube {d : ℕ} (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (a b : ℝ) : Set (KineticPoint d) :=
  {p | p.time ∈ Icc a b ∧ p.position ∈ closure (movingDomain Ω γ p.time)}

/-- The finite open moving tube with unrestricted transported coordinate. -/
def maximumOpenTube {d : ℕ} (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (a b : ℝ) : Set (KineticPoint d) :=
  {p | p.time ∈ Ioo a b ∧ p.position ∈ movingDomain Ω γ p.time}

/-- Closure membership is expressed in the fixed translated-back domain. -/
theorem mem_closure_movingDomain_iff {d : ℕ} (Ω : Set (PDE.Vec d))
    (γ : ℝ → PDE.Vec d) (t : ℝ) (v : PDE.Vec d) :
    v ∈ closure (movingDomain Ω γ t) ↔ v - γ t ∈ closure Ω := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  exact (Set.ext_iff.mp ((Homeomorph.subRight (γ t)).preimage_closure Ω).symm) v

/-- A closed moving tube truncated in the transported coordinate is compact. -/
theorem isCompact_maximumClosedTube_truncated {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a b R : ℝ}
    (hΩ : IsCompact (closure Ω)) (hγ : ContinuousOn γ (Icc a b)) (hR : 0 ≤ R) :
    IsCompact {p ∈ maximumClosedTube Ω γ a b |
      p.velocity ∈ PDE.euclideanClosedBall 0 R} := by
  let f : ℝ × (PDE.Vec d × PDE.Vec d) → KineticPoint d :=
    fun q => ⟨q.1, q.2.1 + γ q.1, q.2.2⟩
  have hf : ContinuousOn f (Icc a b ×ˢ (closure Ω ×ˢ PDE.euclideanClosedBall 0 R)) := by
    change ContinuousOn ((KineticPoint.homeomorphProd d).symm ∘
      (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (q.1, (q.2.1 + γ q.1, q.2.2)))) _
    apply (KineticPoint.homeomorphProd d).symm.continuous.comp_continuousOn
    apply ContinuousOn.prodMk continuousOn_fst
    apply ContinuousOn.prodMk
    · exact continuousOn_snd.fst.add (hγ.comp continuousOn_fst (fun q hq => hq.1))
    · exact continuousOn_snd.snd
  have heq : f '' (Icc a b ×ˢ (closure Ω ×ˢ PDE.euclideanClosedBall 0 R)) =
      {p ∈ maximumClosedTube Ω γ a b |
        p.velocity ∈ PDE.euclideanClosedBall 0 R} := by
    ext p
    constructor
    · rintro ⟨q, ⟨ht, hv, hz⟩, rfl⟩
      refine ⟨⟨ht, ?_⟩, hz⟩
      rw [mem_closure_movingDomain_iff]
      simpa only [f, add_sub_cancel_right] using hv
    · rintro ⟨⟨ht, hv⟩, hz⟩
      refine ⟨(p.time, (p.position - γ p.time, p.velocity)), ⟨ht, ?_, hz⟩, ?_⟩
      · exact (mem_closure_movingDomain_iff Ω γ p.time p.position).mp hv
      · simp only [f, sub_add_cancel]
  rw [← heq]
  exact (isCompact_Icc.prod
    (hΩ.prod (PDE.isCompact_euclideanClosedBall 0 hR))).image_of_continuousOn hf

end HypoellipticAleksandrov.KineticAleksandrov.Decay
