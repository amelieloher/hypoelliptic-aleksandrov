module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic

/-! # Applying the literal source comparison inequality when both error terms vanish -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- A smooth test with zero localized source and controlled kinetic boundary lies below u. -/
theorem admissible_test_le_of_zero_source {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u psi : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hQO : closure (backwardCylinder P₀ R) ⊆ O)
    (hpsi : IsSmoothNear psi (closure (backwardCylinder P₀ R)))
    (hboundary : ∀ P ∈ kineticBoundary P₀ R, psi P ≤ u P)
    (hsource : localizedSource A psi u =ᵐ[volume.restrict (backwardCylinder P₀ R)] 0) :
    ∀ P ∈ closure (backwardCylinder P₀ R), psi P ≤ u P := by
  have hnorm : eLpNorm (localizedSource A psi u) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R)) = 0 := by
    rw [eLpNorm_congr_ae hsource, eLpNorm_zero]
  have hsup : sSup ((fun P => max (psi P - u P) 0) '' kineticBoundary P₀ R) ≤ 0 := by
    apply csSup_le ((kineticBoundary_nonempty P₀ hR).image _)
    rintro _ ⟨P, hP, rfl⟩
    exact max_le (sub_nonpos.mpr (hboundary P hP)) le_rfl
  have hbounded := (isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image
    (hpsi.continuousOn.sub (hu.1.mono hQO))
  intro P hP
  have hpoint := (le_csSup hbounded (mem_image_of_mem (fun T => psi T - u T) hP)).trans
    (hu.2 P₀ R hR hQO psi hpsi)
  rw [hnorm, ENNReal.toReal_zero, mul_zero, add_zero] at hpoint
  exact sub_nonpos.mp (hpoint.trans hsup)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
