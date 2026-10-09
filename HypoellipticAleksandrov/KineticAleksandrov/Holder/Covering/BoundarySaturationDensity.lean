module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
import Mathlib.Tactic

/-! # Density transfer to the admissible saturation path -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Near-full density on a finite superset transfers after accounting for its volume ratio. -/
theorem density_transfer_subset {d : ℕ} {E A B : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hAB : A ⊆ B) (hB : volume B ≠ ⊤)
    {eta k : ℝ} (hk : 0 < k)
    (hvol : (volume B).toReal = k*(volume A).toReal)
    (hdensity : (1-eta/k)*(volume B).toReal ≤ (volume (E ∩ B)).toReal) :
    (1-eta)*(volume A).toReal ≤ (volume (E ∩ A)).toReal := by
  have hA : volume A ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono hAB)
  have hDA : volume (A \ E) ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono sdiff_subset)
  have hDB : volume (B \ E) ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono sdiff_subset)
  have hIA : volume (A ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono inter_subset_left)
  have hIB : volume (B ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono inter_subset_left)
  have ha := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) A hE)
  have hb := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) B hE)
  rw [ENNReal.toReal_add hIA hDA, inter_comm A E] at ha
  rw [ENNReal.toReal_add hIB hDB, inter_comm B E] at hb
  have hd := ENNReal.toReal_mono hDB (measure_mono (sdiff_subset_sdiff_left hAB))
  have heq : (eta/k)*(volume B).toReal = eta*(volume A).toReal := by
    rw [hvol]
    field_simp
  nlinarith only [ha, hb, hd, hdensity, heq]

/-- Path cylinders have density arbitrarily close to one at almost every point of E in Q. -/
theorem ae_saturationCylinder_density {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) :
    ∀ᵐ X ∂(volume.restrict E), ∀ eta : ℝ, 0 < eta →
      ∃ r1 : ℝ, 0 < r1 ∧ ∀ r : ℝ, 0 < r → r < r1 →
        (1-eta)*(volume (backwardCylinder (saturationCenter X r) r)).toReal ≤
          (volume (E ∩ backwardCylinder (saturationCenter X r) r)).toReal := by
  filter_upwards [ae_centeredCylinder_density_all hE hbounded, ae_restrict_mem₀ hE]
    with X hX hXE
  intro eta heta
  let k : ℝ := 2^(4*d+2)
  have hk : 0 < k := by positivity
  obtain ⟨s, hs, hsmall⟩ := hX (eta/k) (div_pos heta hk)
  refine ⟨s/2, half_pos hs, ?_⟩
  intro r hr hrr
  apply density_transfer_subset hE (saturationCylinder_subset_centered (hEQ hXE) hr)
    (volume_cylinder_pos_ne_top (centeredTop X (2*r)) (by positivity)).2 hk
  · unfold centeredCylinder
    rw [volume_cylinder_eq_unit _ (by positivity : 0 < 2*r),
      volume_cylinder_eq_unit _ hr, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*r)^(4*d+2)),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ r^(4*d+2)), mul_pow]
    ring
  · exact hsmall (2*r) (by positivity) (by linarith)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
