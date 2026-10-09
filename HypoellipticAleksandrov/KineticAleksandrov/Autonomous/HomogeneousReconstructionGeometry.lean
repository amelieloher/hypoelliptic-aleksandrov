module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport

/-! # Open strip and terminal/lateral exit for homogeneous reconstruction

The initial time is absent from the regularity set. Endpoint identities require a
strictly larger regularity strip, as the endpoint convention requires.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The physical finite strip, open at both time endpoints. -/
def reconstructionStrip (H : Interval) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier}

/-- The prescribed exit omits the initial velocity face. -/
def reconstructionExit (H : Interval) (sMinus T : ℝ) : Set Point :=
  {p | p.time = T ∧ p.velocity 0 ∈ Set.Icc H.lo H.hi} ∪
    {p | sMinus < p.time ∧ p.time < T ∧
      (p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi)}

/-- Interior points lie in the actual Green past domain. -/
theorem reconstructionStrip_subset_stripPast (H : Interval) (sMinus T : ℝ) :
    reconstructionStrip H sMinus T ⊆ stripPast H T :=
  fun _ hp => ⟨hp.2.1, hp.2.2⟩

/-- Lowering the initial time enlarges the open regularity strip. -/
theorem reconstructionStrip_mono_initial (H : Interval) {sMinus' sMinus T : ℝ}
    (hs : sMinus' ≤ sMinus) :
    reconstructionStrip H sMinus T ⊆ reconstructionStrip H sMinus' T :=
  fun _ hp => ⟨lt_of_le_of_lt hs hp.1, hp.2⟩

/-- A pole at the original initial time becomes an interior point after lowering it. -/
theorem endpoint_mem_lowered_reconstructionStrip (H : Interval)
    {sMinus' sMinus T : ℝ} (hs : sMinus' < sMinus)
    (e : StripPole H (T : WithTop ℝ)) (he : e.1.time = sMinus) :
    e.1 ∈ reconstructionStrip H sMinus' T := by
  refine ⟨?_, ?_, e.2.2⟩
  · exact he.symm ▸ hs
  · exact WithTop.coe_lt_coe.mp e.2.1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
