module

public import PDEFoundation.Geometry.ConvexDomain

/-!
# Axis-aligned cubes

Open coordinate cubes as instances of the bounded open convex domain API.
-/

@[expose] public section

namespace PDE

/-- The open axis cube `z + (0,L)^d`, parametrized by a corner and side. -/
def axisCube {d : ℕ} (z : Vec d) (L : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ioo (z i) (z i + L)

/-- The coordinate center of an axis cube. -/
noncomputable def axisCubeCenter {d : ℕ} (z : Vec d) (L : ℝ) : Vec d :=
  fun i => z i + L / 2

@[simp]
theorem axisCubeCenter_apply {d : ℕ}
    (z : Vec d) (L : ℝ) (i : Fin d) :
    axisCubeCenter z L i = z i + L / 2 :=
  rfl

theorem axisCube_nonempty {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) :
    (axisCube z L).Nonempty := by
  refine ⟨axisCubeCenter z L, ?_⟩
  intro i _hi
  constructor <;> dsimp <;> linarith

theorem axisCube_eq_translateSet_zero {d : ℕ}
    (z : Vec d) (L : ℝ) :
    axisCube z L = translateSet z (axisCube (0 : Vec d) L) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · intro hx i _hi
    have hxi := hx i (Set.mem_univ i)
    change z i < x i ∧ x i < z i + L at hxi
    have hresult : 0 < x i - z i ∧ x i - z i < L := by
      constructor <;> linarith [hxi.1, hxi.2]
    simpa [axisCube] using hresult
  · intro hx i _hi
    have hxi := hx i (Set.mem_univ i)
    have hxi' : 0 < x i - z i ∧ x i - z i < L := by
      simpa [axisCube] using hxi
    change z i < x i ∧ x i < z i + L
    constructor <;> linarith [hxi'.1, hxi'.2]

theorem isOpen_axisCube {d : ℕ} (z : Vec d) (L : ℝ) :
    IsOpen (axisCube z L) := by
  dsimp [axisCube]
  exact isOpen_set_pi Set.finite_univ fun _i _hi => isOpen_Ioo

theorem isBoundedDomain_axisCube {d : ℕ}
    (z : Vec d) (L : ℝ) :
    IsBoundedDomain (axisCube z L) := by
  dsimp [axisCube]
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun _i => Metric.isBounded_Ioo _ _

theorem convex_axisCube {d : ℕ} (z : Vec d) (L : ℝ) :
    Convex ℝ (axisCube z L) := by
  dsimp [axisCube]
  refine convex_pi ?_
  intro _i _hi
  exact convex_Ioo _ _

theorem isOpenBoundedConvexDomain_axisCube {d : ℕ}
    (z : Vec d) (L : ℝ) :
    IsOpenBoundedConvexDomain (axisCube z L) :=
  ⟨isOpen_axisCube z L, isBoundedDomain_axisCube z L,
    convex_axisCube z L⟩

theorem hasEuclideanDiameterLE_axisCube {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    HasEuclideanDiameterLE (axisCube z L)
      (Real.sqrt d * L) := by
  intro x hx y hy
  have hsup : ‖x - y‖ ≤ L := by
    rw [pi_norm_le_iff_of_nonneg hL]
    intro i
    have hxi := hx i (Set.mem_univ i)
    have hyi := hy i (Set.mem_univ i)
    simpa [Real.norm_eq_abs] using
      (abs_le.2 ⟨by linarith [hxi.1, hyi.2],
        by linarith [hxi.2, hyi.1]⟩)
  exact
    (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y)).trans
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg d))

end PDE
