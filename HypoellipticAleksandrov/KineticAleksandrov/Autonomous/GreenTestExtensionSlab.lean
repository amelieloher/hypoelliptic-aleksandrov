module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign

/-! # Closed physical slabs and continuous trace bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- Scalar physical coordinates retain the source's time-position-velocity order. -/
def reconstructionScalarHomeomorph : (ℝ × ℝ × ℝ) ≃ₜ Point :=
  ((Homeomorph.refl ℝ).prodCongr
    (PDE.scalarToVecOneContinuousLinearEquiv.toHomeomorph.prodCongr
      PDE.scalarToVecOneContinuousLinearEquiv.toHomeomorph)).trans
    (KineticPoint.homeomorphProd 1).symm

/-- The full physical closed slab at finite times. -/
def reconstructionClosedSlab (H : Interval) (a T : ℝ) : Set Point :=
  {p | a ≤ p.time ∧ p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi}

/-- The closure of a nonempty physical open strip is its literal closed slab. -/
theorem closure_reconstructionStrip (H : Interval) (a T : ℝ) (ha : a < T) :
    closure (reconstructionStrip H a T) = reconstructionClosedSlab H a T := by
  let S : Set (ℝ × ℝ × ℝ) := Ioo a T ×ˢ (univ ×ˢ Ioo H.lo H.hi)
  have heq : reconstructionStrip H a T = reconstructionScalarHomeomorph '' S := by
    ext p
    constructor
    · intro hp
      refine ⟨(p.time, p.position 0, p.velocity 0), ⟨⟨hp.1, hp.2.1⟩, mem_univ _, hp.2.2⟩, ?_⟩
      refine KineticPoint.ext rfl ?_ ?_
      · funext i
        fin_cases i
        rfl
      · funext i
        fin_cases i
        rfl
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1.1, hq.1.2, hq.2.2⟩
  rw [heq, ← Homeomorph.image_closure]
  dsimp only [S]
  rw [closure_prod_eq, closure_prod_eq, closure_Ioo ha.ne, closure_univ,
    closure_Ioo H.ordered.ne]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1.1, hq.1.2, hq.2.2⟩
  · intro hp
    refine ⟨(p.time, p.position 0, p.velocity 0), ⟨⟨hp.1, hp.2.1⟩, mem_univ _, hp.2.2⟩, ?_⟩
    refine KineticPoint.ext rfl ?_ ?_
    · funext i
      fin_cases i
      rfl
    · funext i
      fin_cases i
      rfl

/-- Every closed future slab lies in the regular strip together with its prescribed exit. -/
theorem reconstructionClosedSlab_subset_strip_union_exit (H : Interval)
    {lower a T : ℝ} (ha : lower < a) :
    reconstructionClosedSlab H a T ⊆ reconstructionStrip H lower T ∪ reconstructionExit H
      lower T := by
  intro p hp
  by_cases ht : p.time = T
  · exact Or.inr (Or.inl ⟨ht, hp.2.2⟩)
  · have hpt : p.time < T := lt_of_le_of_ne hp.2.1 ht
    by_cases hv : p.velocity 0 ∈ H.carrier
    · exact Or.inl ⟨ha.trans_le hp.1, hpt, hv⟩
    · have hf : p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi := by
        change ¬(H.lo < p.velocity 0 ∧ p.velocity 0 < H.hi) at hv
        rcases not_and_or.mp hv with hv | hv
        · exact Or.inl (le_antisymm (not_lt.mp hv) hp.2.2.1)
        · exact Or.inr (le_antisymm hp.2.2.2 (not_lt.mp hv))
      exact Or.inr (Or.inr ⟨ha.trans_le hp.1, hpt, hf⟩)

/-- The original interior bound extends to every closed future slab by the prescribed continuity. -/
theorem reconstruction_closed_slab_test_bound
    (H : Interval) {lower a T : ℝ} (ha : lower < a) (hT : a < T)
    (phi : Point → ℝ)
    (hc : ContinuousOn phi (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (M : ℝ) (hM : ∀ p ∈ reconstructionStrip H lower T, |phi p| ≤ M) :
    ∀ p ∈ reconstructionClosedSlab H a T, |phi p| ≤ M := by
  have hcl := closure_reconstructionStrip H a T hT
  intro p hp
  rw [← hcl] at hp
  apply le_on_closure
    (s := reconstructionStrip H a T) (f := fun p => |phi p|) (g := fun _ => M)
    (fun p hp => hM p ⟨ha.trans hp.1, hp.2⟩)
  · rw [hcl]
    exact (hc.mono (reconstructionClosedSlab_subset_strip_union_exit H ha)).abs
  · exact continuousOn_const
  · exact hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
