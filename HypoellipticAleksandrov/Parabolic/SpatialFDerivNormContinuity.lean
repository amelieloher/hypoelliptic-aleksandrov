module

public import HypoellipticAleksandrov.Parabolic.SpatialFDerivNorm
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators Matrix.Norms.Elementwise

/-- Smoothness on a neighborhood makes the spatial derivative norm of a
scalar field continuous on the carrier. -/
theorem IsSmoothOnNeighborhood.continuousOn_spatialScalarFDerivEuclideanNorm
    {d : ℕ} {K : Set (TimeVelocity d)}
    {f : TimeVelocity d → ℝ}
    (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn (spatialScalarFDerivEuclideanNorm f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  unfold spatialScalarFDerivEuclideanNorm
  apply (Real.continuous_sqrt.comp_continuousOn ?_).mono hKV
  apply continuousOn_finset_sum
  intro k _hk
  exact ((hV.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
    continuousOn_const).pow 2

/-- Smoothness on a neighborhood makes the spatial derivative Frobenius norm
of a vector field continuous on the carrier. -/
theorem IsSmoothOnNeighborhood.continuousOn_spatialVectorFDerivFrobeniusNorm
    {d : ℕ} {K : Set (TimeVelocity d)}
    {f : TimeVelocity d → PDE.Vec d}
    (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn (spatialVectorFDerivFrobeniusNorm f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  unfold spatialVectorFDerivFrobeniusNorm
  apply (Real.continuous_sqrt.comp_continuousOn ?_).mono hKV
  apply continuousOn_finset_sum
  intro j _hj
  apply continuousOn_finset_sum
  intro k _hk
  have hfj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => f z j) V :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hV fun _ _ => Set.mem_univ _
  exact ((hfj.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
    continuousOn_const).pow 2

/-- Smoothness on a neighborhood makes the spatial derivative Frobenius norm
of a matrix field continuous on the carrier. -/
theorem IsSmoothOnNeighborhood.continuousOn_spatialMatrixFDerivFrobeniusNorm
    {d : ℕ} {K : Set (TimeVelocity d)}
    {f : TimeVelocity d → PDE.Mat d}
    (hf : IsSmoothOnNeighborhood f K) :
    ContinuousOn (spatialMatrixFDerivFrobeniusNorm f) K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  unfold spatialMatrixFDerivFrobeniusNorm
  apply (Real.continuous_sqrt.comp_continuousOn ?_).mono hKV
  apply continuousOn_finset_sum
  intro i _hi
  apply continuousOn_finset_sum
  intro j _hj
  apply continuousOn_finset_sum
  intro k _hk
  have hfi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => f z i) V :=
    (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV fun _ _ => Set.mem_univ _
  have hfij : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => f z i j) V :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hfi fun _ _ => Set.mem_univ _
  exact ((hfij.continuousOn_fderiv_of_isOpen hVopen (by simp)).clm_apply
    continuousOn_const).pow 2

end HypoellipticAleksandrov.Parabolic
