module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenDensityTransport

/-! # Continuous and measurable coordinates for whole-space source potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Set MeasureTheory

/-- The Section 2 coordinate permutation is continuous in the fixed kinetic topology. -/
theorem continuous_sectionTwoPoint (d : ℕ) : Continuous (sectionTwoPoint (d := d)) :=
  KineticPoint.continuous_mk continuous_time continuous_velocity continuous_position

/-- The Section 2 coordinate permutation is a homeomorphism with its own inverse. -/
def sectionTwoHomeomorph (d : ℕ) : KineticPoint d ≃ₜ KineticPoint d where
  toFun := sectionTwoPoint
  invFun := sectionTwoPoint
  left_inv := sectionTwoPoint_involutive
  right_inv := sectionTwoPoint_involutive
  continuous_toFun := continuous_sectionTwoPoint d
  continuous_invFun := continuous_sectionTwoPoint d

/-- Swapping position and velocity preserves compact support. -/
theorem hasCompactSupport_sectionTwoPoint {d : ℕ} {g : KineticPoint d → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ sectionTwoPoint) :=
  hg.comp_homeomorph (sectionTwoHomeomorph d)

/-- A smooth test source remains smooth after the Section 2 permutation. -/
theorem contDiff_sectionTwoPoint_source {d : ℕ} {g : KineticPoint d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => g ((KineticPoint.equivProd d).symm z))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      (g ∘ sectionTwoPoint) ⟨q.1, q.2.1, q.2.2⟩) := by
  exact hg.comp (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
