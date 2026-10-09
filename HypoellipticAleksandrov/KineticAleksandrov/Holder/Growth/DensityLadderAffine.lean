module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.LevelMeasurabilityAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryAffine
import Mathlib.Tactic

/-! # Ink-spots iteration in physical sampling cylinders with the exact volume factor -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set MeasureTheory

/-- The proved ink-spots constants work uniformly after any kinetic affine change of scale. -/
theorem exists_affine_ink_spots_constants (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ c < 1 ∧ 0 < C ∧
      ∀ m : ℕ, 0 < m →
      ∀ eta r0 : ℝ, 0 < eta → eta < 1 → 0 < r0 → r0 < 1 →
      ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
      ∀ E F : Set (KineticPoint d),
        Bornology.IsBounded E → Bornology.IsBounded F →
        MeasurableSet E → MeasurableSet F → E ⊆ F ∩ backwardCylinder P0 R →
        (∀ (P : KineticPoint d) (r : ℝ), 0 < r →
          backwardCylinder P r ⊆ backwardCylinder P0 R →
          (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
            (volume (E ∩ backwardCylinder P r)).toReal →
          r < r0 * R ∧ forwardStack P r m ⊆ F) →
        (volume E).toReal ≤ (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta) *
          ((volume (F ∩ backwardCylinder P0 R)).toReal +
            R ^ (4 * d + 2) * C * (m : ℝ) * r0 ^ 2) := by
  obtain ⟨c, C, hc, hc1, hC, hink⟩ := kinetic_crawling_ink_spots_aux d hd
  refine ⟨c, C, hc, hc1, hC, ?_⟩
  intro m hm eta r0 heta heta1 hr0 hr01 P0 R hR E F hEb hFb hE hF hEF hstack
  let phi := kineticAffine P0 R
  let Ep := phi ⁻¹' E
  let Fp := phi ⁻¹' F
  let Q := backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1
  have hEp : MeasurableSet Ep := measurableSet_kineticAffine_preimage P0 R hE
  have hFp : MeasurableSet Fp := measurableSet_kineticAffine_preimage P0 R hF
  have hEpF : Ep ⊆ Fp ∩ Q := by
    intro P hP
    have hh := hEF hP
    exact ⟨hh.1, (kineticAffine_mem_cylinder P0 P hR).mp hh.2⟩
  have hfactor : 0 < R ^ (4 * d + 2) := pow_pos hR _
  have hphiInj : Function.Injective phi :=
    (kineticAffineHomeomorph P0 R hR.ne').injective
  have hphiF : phi '' Fp = F :=
    (kineticAffineHomeomorph P0 R hR.ne').toEquiv.image_preimage F
  have hphiQ : phi '' Q = backwardCylinder P0 R :=
    kineticAffine_image_unitCylinder P0 hR
  have hphiE : phi '' Ep = E := (kineticAffineHomeomorph P0 R hR.ne').toEquiv.image_preimage E
  have hphiFQ : phi '' (Fp ∩ Q) = F ∩ backwardCylinder P0 R := by
    rw [image_inter hphiInj, hphiF, hphiQ]
  have hlocal (P : KineticPoint d) (r : ℝ) (hr : 0 < r)
      (hsub : backwardCylinder P r ⊆ Q)
      (hdense : (1 - eta) * (volume (backwardCylinder P r)).toReal ≤
        (volume (Ep ∩ backwardCylinder P r)).toReal) :
      r < r0 ∧ forwardStack P r m ⊆ Fp := by
    have himage := kineticAffine_image_cylinder P0 P R r hR hr
    have hsubp : backwardCylinder (phi P) (R * r) ⊆ backwardCylinder P0 R := by
      rw [← himage, ← kineticAffine_image_unitCylinder P0 hR]
      exact image_mono hsub
    have hinter : phi '' (Ep ∩ backwardCylinder P r) =
        E ∩ backwardCylinder (phi P) (R * r) := by
      rw [image_inter hphiInj, hphiE, himage]
    have hdensep : (1 - eta) *
        (volume (backwardCylinder (phi P) (R * r))).toReal ≤
          (volume (E ∩ backwardCylinder (phi P) (R * r))).toReal := by
      rw [← hinter, ← himage, volume_affine_image_toReal P0 hR,
        volume_affine_image_toReal P0 hR]
      nlinarith only [mul_le_mul_of_nonneg_left hdense hfactor.le]
    obtain ⟨hsmall, hforward⟩ := hstack (phi P) (R * r) (mul_pos hR hr) hsubp hdensep
    refine ⟨?_, ?_⟩
    · nlinarith only [hsmall, hR]
    · intro Z hZ
      apply hforward
      rw [← kineticAffine_image_stack P0 P R r hR hr m]
      exact ⟨Z, hZ, rfl⟩
  have hbound := hink m hm eta r0 heta heta1 hr0 hr01 Ep Fp
    (isBounded_kineticAffine_preimage P0 hR.ne' hEb)
    (isBounded_kineticAffine_preimage P0 hR.ne' hFb)
    hEp.nullMeasurableSet hFp.nullMeasurableSet hEpF hlocal
  have hvolE := volume_affine_image_toReal P0 hR Ep
  have hvolF := volume_affine_image_toReal P0 hR (Fp ∩ Q)
  rw [hphiE] at hvolE
  rw [hphiFQ] at hvolF
  rw [hvolE, hvolF]
  nlinarith only [mul_le_mul_of_nonneg_left hbound hfactor.le]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
