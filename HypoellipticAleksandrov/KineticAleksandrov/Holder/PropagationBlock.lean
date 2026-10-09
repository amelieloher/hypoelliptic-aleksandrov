module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockSource
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockComparison
import Mathlib.Tactic

/-! # The source one-block comparison with all boundary and source terms discharged -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Initial-strip comparison propagates throughout the source block in the halved tube. -/
theorem propagation_one_block {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus sblock TP : ℝ)
    (hsblock : 0 ≤ sblock) (hblock : sblock + h ≤ TP)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A : ℝ} (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinit : ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      P.time - tminus - sblock ≤ 0 →
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus sblock x v P ≤ u P) :
    ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus sblock x v P ≤ u P := by
  let R := barrierW d lam Lam H T1 * Real.sqrt h
  let P₀ : KineticPoint d :=
    ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
  have hR : 0 < R := mul_pos
    (lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)) (Real.sqrt_pos.mpr hh)
  have hQO := (propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
    tminus sblock TP hsblock hblock hv.continuous hkin hLip).trans htube
  apply admissible_test_le_of_zero_source hu P₀ hR hQO
    (gaussianBarrier_isSmoothNear hlam hh Lam H (barrierL d lam Lam H T1)
      ell tminus sblock hx hv _)
  · intro P hP
    exact (gaussianBarrier_nonpos_boundary hd hlam hLam hH hT0 hT1 hh hhstar
      hell tminus sblock hv.continuous hkin hLip P hP).trans
      (hnonneg P (hQO (mem_kineticBoundary_iff.mp hP).1))
  · exact gaussianBarrier_localizedSource_zero hlam hh hR Lam H
      (barrierL d lam Lam H T1) ell tminus sblock hLam hH hell A hA
      hx hv hkin hLip u hinit

end HypoellipticAleksandrov.KineticAleksandrov.Holder
