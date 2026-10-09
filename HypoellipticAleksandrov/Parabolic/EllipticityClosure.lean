module

public import HypoellipticAleksandrov.Parabolic.LocalClassical

/-!
# Closure of local lower ellipticity

This module records that lower Loewner ellipticity is closed under limits of
continuous coefficient fields.  It is deliberately pointwise: no openness,
compactness, or positive ellipticity constant is needed for this extension.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Matrix Set
open scoped MatrixOrder

private theorem isClosed_isHermitian (d : ℕ) :
    IsClosed {H : PDE.Mat d | H.IsHermitian} := by
  have hset :
      {H : PDE.Mat d | H.IsHermitian} =
        ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
    ext H
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i j
      simpa using h.apply i j
    · intro h
      apply Matrix.IsHermitian.ext
      intro i j
      simpa using h i j
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)

private theorem isClosed_posSemidef (d : ℕ) :
    IsClosed {H : PDE.Mat d | H.PosSemidef} := by
  have hset :
      {H : PDE.Mat d | H.PosSemidef} =
        {H : PDE.Mat d | H.IsHermitian} ∩
          ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H *ᵥ q)} := by
    ext H
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
  rw [hset]
  refine (isClosed_isHermitian d).inter (isClosed_iInter fun q => ?_)
  have hquad : Continuous (fun H : PDE.Mat d => dotProduct q (H *ᵥ q)) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact isClosed_le continuous_const hquad

/-- The affine lower Loewner cone is closed in the native matrix topology. -/
theorem isClosed_setOf_lowerEllipticity (d : ℕ) (lam : ℝ) :
    IsClosed {M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M} := by
  have hset : {M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M} =
      (fun M : PDE.Mat d => M - lam • (1 : PDE.Mat d)) ⁻¹'
        {H : PDE.Mat d | H.PosSemidef} := by
    ext M
    exact Matrix.le_iff
  rw [hset]
  exact (isClosed_posSemidef d).preimage (continuous_id.sub continuous_const)

namespace HasLowerEllipticityOn

/-- A continuous lower ellipticity bound extends to the closure whenever the
closure stays within the coefficient's continuity set. -/
theorem closure
    {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {S U : Set (TimeVelocity d)}
    (h : HasLowerEllipticityOn lam A S)
    (hcont : IsContinuousCoefficientOn A U)
    (hclosureU : _root_.closure S ⊆ U) :
    HasLowerEllipticityOn lam A (_root_.closure S) := by
  have hmaps : MapsTo (coefficientAt A) S
      {M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M} := h
  have hcontClosure : ContinuousOn (coefficientAt A) (_root_.closure S) :=
    hcont.mono hclosureU
  have hmapsClosure : MapsTo (coefficientAt A) (_root_.closure S)
      (_root_.closure {M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M}) :=
    hmaps.closure_of_continuousOn hcontClosure
  intro z hz
  have hzLower := hmapsClosure hz
  rwa [(isClosed_setOf_lowerEllipticity d lam).closure_eq] at hzLower

end HasLowerEllipticityOn

end HypoellipticAleksandrov.Parabolic
