module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationFamily
import Mathlib.Tactic

/-! # Delayed critical unions with a linear leakage error -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- The critical union is controlled by F inside Q and a linear small-height leakage error. -/
theorem criticalUnion_delay_bound {d : ℕ} {E F : Set (KineticPoint d)}
    {eta R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) (m : ℕ) (hm : 0 < m)
    (hheight : (m : ℝ)*R^2 ≤ 1)
    (hstack : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal →
      r < R ∧ forwardStack P r m ⊆ F) :
    (volume (criticalUnion E eta)).toReal ≤
      (((m : ℝ)+1)/(m : ℝ))*((volume (F ∩ unitCylinder d)).toReal+
        2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2)) := by
  obtain ⟨T, hT, hTc, hcover⟩ := exists_countable_critical_subcover E eta
  let : Countable T := hTc.to_subtype
  let P : T → KineticPoint d := fun z => z.1.1
  let r : T → ℝ := fun z => z.1.2
  have hz (z : T) : 0 < r z ∧ backwardCylinder (P z) (r z) ⊆ unitCylinder d ∧
      (volume (E ∩ backwardCylinder (P z) (r z))).toReal =
        (1-eta)*(volume (backwardCylinder (P z) (r z))).toReal := hT z.2
  have hs (z : T) : r z < R ∧ forwardStack (P z) (r z) m ⊆ F :=
    hstack (P z) (r z) (hz z).1 (hz z).2.1 (hz z).2.2.symm.le
  let J := ⋃ z : T, openForwardStack (P z) (r z) m
  have hJopen : IsOpen J := isOpen_iUnion fun z => isOpen_openForwardStack (P z) (r z) m
  have hJF : J ⊆ F := by
    intro X hX
    obtain ⟨z, hz⟩ := mem_iUnion.mp hX
    exact (hs z).2 hz.1
  have hJbox : J ⊆ roundBox d (-1) ((m : ℝ)*R^2) (1+4*(m : ℝ)*R^2) := by
    intro X hX
    obtain ⟨z, hmem⟩ := mem_iUnion.mp hX
    exact forwardStack_subset_roundBox (hz z).1 (hs z).1 hR1 (hz z).2.1 m hm hmem.1
  have hheight0 : 0 < (m : ℝ)*R^2 := mul_pos (by exact_mod_cast hm) (sq_pos_of_pos hR)
  have hboxfinite := volume_roundBox_ne_top d (-1) ((m : ℝ)*R^2)
    (by positivity : 0 < 1+4*(m : ℝ)*R^2)
  have hJfinite : volume J ≠ ⊤ := ne_top_of_le_ne_top hboxfinite (measure_mono hJbox)
  have hFQfinite : volume (F ∩ unitCylinder d) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_cylinder_pos_ne_top _ zero_lt_one).2
      (measure_mono inter_subset_right)
  have hDfinite : volume (roundBox d (-1) ((m : ℝ)*R^2)
      (1+4*(m : ℝ)*R^2) \ unitCylinder d) ≠ ⊤ :=
    ne_top_of_le_ne_top hboxfinite (measure_mono sdiff_subset)
  have hJbound : (volume J).toReal ≤ (volume (F ∩ unitCylinder d)).toReal+
      2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2) := by
    have hsub : J ⊆ (F ∩ unitCylinder d) ∪
        (roundBox d (-1) ((m : ℝ)*R^2) (1+4*(m : ℝ)*R^2) \ unitCylinder d) := by
      intro X hX
      by_cases hQ : X ∈ unitCylinder d
      · exact Or.inl ⟨hJF hX, hQ⟩
      · exact Or.inr ⟨hJbox hX, hQ⟩
    have hb := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hFQfinite, hDfinite⟩) hb
    rw [ENNReal.toReal_add hFQfinite hDfinite] at hreal
    have hshell : (volume (roundBox d (-1) ((m : ℝ)*R^2)
        (1+4*(m : ℝ)*R^2) \ unitCylinder d)).toReal ≤
        2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*((m : ℝ)*R^2) := by
      simpa only [mul_assoc] using leakage_shell_volume d hheight0 hheight
    linarith only [hreal, hshell]
  have hH : (⋃ z : T, backwardCylinder (P z) (r z)) = criticalUnion E eta := by
    rw [iUnion_subtype]
    exact hcover
  have hdelay := delayed_union_countable P r (fun z => (hz z).1) m hm
  rw [hH] at hdelay
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfinite) hdelay
  have hq : 0 ≤ ((m : ℝ)+1)/(m : ℝ) := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_left hJbound hq)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
