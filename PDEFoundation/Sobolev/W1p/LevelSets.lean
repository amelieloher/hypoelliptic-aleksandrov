module

public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Truncation

/-!
# Vanishing of weak gradients on individual level sets

For a representative-level finite-exponent `W^{1,p}` function on a bounded
open convex domain, this module proves that its selected weak gradient
vanishes almost everywhere on each individual level set.  The proof compares
the two one-sided positive-part truncations of `u` and `-u`; it does not use a
general Lipschitz Sobolev chain rule.

The result concerns one fixed level only.  The stronger null-preimage theorem
needed for an arbitrary Lipschitz scalar composition remains a separate
later result.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The selected weak gradient of a finite-exponent `W^{1,p}` representative
vanishes almost everywhere on each individual level set. -/
theorem grad_ae_zero_on_level_set
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (c : ℝ) :
    ∀ᵐ x ∂(volumeOn U), u.toFun x = c → u.grad x = 0 := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let v₁ : W1pFunction U p :=
    u.positivePartSubConst hU hp hpTop c
  let v₂ : W1pFunction U p :=
    (-u).positivePartSubConst hU hp hpTop (-c)
  let v : W1pFunction U p := v₁ - v₂
  let w : W1pFunction U p := u.addConst (-c)
  have htoFun_eq : v.toFun = w.toFun := by
    funext x
    have hneg : (-u).toFun x - -c = c - u.toFun x := by
      simp only [neg_toFun]
      ring
    change max (u.toFun x - c) 0 - max ((-u).toFun x - -c) 0 =
      u.toFun x + -c
    rw [hneg]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hgrad_ae : ∀ᵐ x ∂(volumeOn U), v.grad x = w.grad x := by
    have hcoord : ∀ i : Fin d,
        (fun x => v.grad x i) =ᵐ[volumeOn U] (fun x => w.grad x i) := by
      intro i
      refine HasWeakPartialDerivOn.ae_eq hU.isOpen
        (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          (v.locallyIntegrable_grad i))
        (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
          (w.locallyIntegrable_grad i))
        (v.hasWeakGradient i) ?_
      rw [htoFun_eq]
      exact w.hasWeakGradient i
    have hall : ∀ᵐ x ∂(volumeOn U), ∀ i, v.grad x i = w.grad x i :=
      ae_all_iff.mpr hcoord
    filter_upwards [hall] with x hx
    funext i
    exact hx i
  filter_upwards [hgrad_ae] with x hx hxc
  have hvgrad : v.grad x = v₁.grad x - v₂.grad x := by
    rfl
  have hwgrad : w.grad x = u.grad x := by
    simp only [w, addConst_grad]
  have hv₁zero : v₁.grad x = 0 := by
    change {y | c < u.toFun y}.indicator u.grad x = 0
    rw [Set.indicator_of_notMem (by
      simp only [Set.mem_ofPred_eq, not_lt, hxc, le_refl])]
  have hv₂zero : v₂.grad x = 0 := by
    change {y | -c < (-u).toFun y}.indicator (-u).grad x = 0
    rw [Set.indicator_of_notMem (by
      simp only [Set.mem_ofPred_eq, neg_toFun, not_lt, hxc]
      exact le_rfl)]
  rw [← hwgrad, ← hx, hvgrad, hv₁zero, hv₂zero, sub_zero]

end W1pFunction

end PDE
