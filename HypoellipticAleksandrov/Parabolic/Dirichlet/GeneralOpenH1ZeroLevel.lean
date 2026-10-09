module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1PositivePart
public import PDEFoundation.Sobolev.H1.Algebra

/-!
# Vanishing of an H¹ gradient on the zero set of its representative

The two strict one-sided truncations reconstruct the original representative.
Uniqueness of weak partial derivatives on an open set then identifies their
difference gradient with the selected gradient of the original function.
-/

@[expose] public section

namespace PDE.H1Function

open Filter MeasureTheory Set

/-- On an arbitrary open set, the selected weak gradient of an `H¹`
representative vanishes almost everywhere on its zero set. -/
theorem grad_ae_zero_on_zero_set_of_isOpen
    {d : ℕ} {U : Set (PDE.Vec d)} (hU : IsOpen U)
    (u : PDE.H1Function U) :
    ∀ᵐ x ∂(PDE.volumeOn U), u.toFun x = 0 → u.grad x = 0 := by
  obtain ⟨v₁, hv₁Fun, hv₁Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hU u 0 (by norm_num)
  obtain ⟨v₂, hv₂Fun, hv₂Grad⟩ :=
    exists_h1PositivePartSubConst_of_isOpen hU (-u) 0 (by norm_num)
  let v : PDE.H1Function U := v₁ - v₂
  have hvFun : v.toFun = u.toFun := by
    simp only [v, sub_toFun]
    funext x
    rw [hv₁Fun, hv₂Fun]
    simp only [neg_toFun, sub_zero]
    rcases le_total (u.toFun x) 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
  have hgradAE : ∀ᵐ x ∂(PDE.volumeOn U), v.grad x = u.grad x := by
    have hcoord : ∀ i : Fin d,
        (fun x => v.grad x i) =ᵐ[PDE.volumeOn U] (fun x => u.grad x i) := by
      intro i
      refine PDE.HasWeakPartialDerivOn.ae_eq hU
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((v.gradMemL2 i).locallyIntegrable (by norm_num)))
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((u.gradMemL2 i).locallyIntegrable (by norm_num)))
        (v.hasWeakGradient i) ?_
      rw [hvFun]
      exact u.hasWeakGradient i
    have hall : ∀ᵐ x ∂(PDE.volumeOn U), ∀ i, v.grad x i = u.grad x i :=
      ae_all_iff.mpr hcoord
    filter_upwards [hall] with x hx
    funext i
    exact hx i
  filter_upwards [hgradAE] with x hx hux
  have hv₁Zero : v₁.grad x = 0 := by
    rw [hv₁Grad]
    change {y | 0 < u.toFun y}.indicator u.grad x = 0
    rw [indicator_of_notMem]
    simp only [mem_setOf_eq, hux, lt_self_iff_false, not_false_eq_true]
  have hv₂Zero : v₂.grad x = 0 := by
    rw [hv₂Grad]
    change {y | 0 < (-u).toFun y}.indicator (-u).grad x = 0
    rw [indicator_of_notMem]
    simp only [mem_setOf_eq, neg_toFun, hux, neg_zero, lt_self_iff_false,
      not_false_eq_true]
  rw [← hx]
  simp only [v, sub_grad]
  rw [hv₁Zero, hv₂Zero, sub_zero]

end PDE.H1Function
