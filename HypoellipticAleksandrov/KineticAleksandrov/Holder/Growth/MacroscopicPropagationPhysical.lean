module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPhysical
import Mathlib.Tactic

/-! # Macroscopic cap comparison stated entirely in physical coordinates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The uniform cap comparison applies to every physical sampling subcylinder above cutoff. -/
theorem exists_physical_macroscopic_cap_constant (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (m : ℕ) (r0 : ℝ)
    (hr0 : 0 < r0) (hr01 : r0 < 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (scale : ℝ), 0 < scale →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
        IsAdmissibleSupersolution A O p C_A u →
      ∀ (Q : KineticPoint d) (r ell : ℝ), 0 < r → r0 * scale ≤ r →
        backwardCylinder Q r ⊆
          backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale →
        0 ≤ ell → (∀ Z ∈ kineticAffine Q r '' cap d, ell ≤ u Z) →
        ∀ P ∈ backwardCylinder P0 scale, c * ell ≤ u P := by
  obtain ⟨c, hc, hc1, hmacro⟩ :=
    exists_macroscopic_cap_constant d hd lam Lam hlam hLam m r0 hr0 hr01
  refine ⟨c, hc, hc1, ?_⟩
  intro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu Q r ell hr hbig hsub
    hell hcap P hP
  let Qref := kineticAffineInverse P0 scale Q
  let Pref := kineticAffineInverse P0 scale P
  have hrref : r0 ≤ r / scale := (le_div_iff₀ hscale).mpr hbig
  have hsubref := physical_sampling_subcylinder P0 Q hscale hr m hsub
  have hPref : Pref ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    apply (kineticAffine_mem_cylinder P0 Pref hscale).mp
    simpa only [Pref, kineticAffine_apply_inverse P0 hscale.ne'] using hP
  have hcapref : ∀ Z ∈ kineticAffine (kineticAffine P0 scale Qref) (scale * (r / scale)) ''
      cap d, ell ≤ u Z := by
    simpa only [Qref, kineticAffine_apply_inverse P0 hscale.ne',
      mul_div_cancel₀ r hscale.ne'] using hcap
  have hbound := hmacro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu
    Qref (r / scale) ell hrref hsubref hell hcapref Pref hPref
  simpa only [Pref, kineticAffine_apply_inverse P0 hscale.ne'] using hbound

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
