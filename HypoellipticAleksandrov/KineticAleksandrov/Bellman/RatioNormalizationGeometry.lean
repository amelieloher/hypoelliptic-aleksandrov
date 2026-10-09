module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Geometry
public import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic

/-! # The position rescaling used to normalize the ellipticity ratio -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Position rescaling as an actual continuous linear equivalence of the product plane. -/
def bellmanPositionEquiv (s : ℝ) (hs : 0 < s) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun q := (s * q.1, q.2)
  invFun q := (s⁻¹ * q.1, q.2)
  map_add' q z := by ext <;> simp [mul_add]
  map_smul' c q := by ext <;> simp [mul_left_comm]
  left_inv q := by ext <;> simp [hs.ne']
  right_inv q := by ext <;> simp [hs.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Position rescaling preserves the punctured plane. -/
theorem bellmanPositionEquiv_ne_zero (s : ℝ) (hs : 0 < s) (q : BellmanPuncturedPlane) :
    bellmanPositionEquiv s hs q.val ≠ (0, 0) := by
  intro h
  apply q.property
  have hx := congrArg Prod.fst h
  have hv := congrArg Prod.snd h
  change s * q.val.1 = 0 at hx
  change q.val.2 = 0 at hv
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left hs.ne') hv

/-- The position rescaling is a homeomorphism of the literal punctured carrier. -/
def bellmanPositionHomeomorph (s : ℝ) (hs : 0 < s) :
    BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane where
  toFun q := ⟨bellmanPositionEquiv s hs q.val, bellmanPositionEquiv_ne_zero s hs q⟩
  invFun q := ⟨bellmanPositionEquiv s⁻¹ (inv_pos.mpr hs) q.val,
    bellmanPositionEquiv_ne_zero s⁻¹ (inv_pos.mpr hs) q⟩
  left_inv q := by
    apply Subtype.ext
    change (s⁻¹ * (s * q.val.1), q.val.2) = q.val
    simp [hs.ne']
  right_inv q := by
    apply Subtype.ext
    change (s * (s⁻¹ * q.val.1), q.val.2) = q.val
    simp [hs.ne']
  continuous_toFun := by
    exact ((bellmanPositionEquiv s hs).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((bellmanPositionEquiv s⁻¹ (inv_pos.mpr hs)).continuous.comp
      continuous_subtype_val).subtype_mk _

/-- Position rescaling commutes with every kinetic dilation. -/
theorem bellmanPositionHomeomorph_dilation (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) (q : BellmanPuncturedPlane) :
    bellmanPositionHomeomorph s hs (bellmanDilation r hr q) =
      bellmanDilation r hr (bellmanPositionHomeomorph s hs q) := by
  apply Subtype.ext
  change (s * (r ^ 3 * q.val.1), r * q.val.2) =
    (r ^ 3 * (s * q.val.1), r * q.val.2)
  ext <;> ring

end HypoellipticAleksandrov.KineticAleksandrov
