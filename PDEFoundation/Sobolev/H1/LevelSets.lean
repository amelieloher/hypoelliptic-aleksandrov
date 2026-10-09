module

public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.LevelSets

/-!
# Level-set gradient vanishing in `H¹`

The theorem in this file is a direct `p = 2` facade for the finite-exponent
result.  It concerns the selected concrete weak-gradient representative.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The selected `H¹` weak gradient vanishes almost everywhere on each fixed
level set. -/
theorem grad_ae_zero_on_level_set
    (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (c : ℝ) :
    ∀ᵐ x ∂(volumeOn U), u.toFun x = c → u.grad x = 0 := by
  simpa only [H1Function.toW1pFunction_toFun,
    H1Function.toW1pFunction_grad] using
    W1pFunction.grad_ae_zero_on_level_set
      hU (by norm_num) (by norm_num) u.toW1pFunction c

end H1Function

end PDE
