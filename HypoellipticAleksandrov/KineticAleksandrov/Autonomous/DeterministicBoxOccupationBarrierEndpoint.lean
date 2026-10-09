module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationEndpointUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulus

/-! # Actual Bellman endpoint estimate with the modulus discharged -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory

/-- The homogeneous Bellman barrier has a uniform endpoint bound under the velocity restriction.
The constant precedes the coefficient field, pole, terminal time and position shift. -/
theorem deterministic_barrier_endpoint_uniform
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {alpha : ℝ} {phi : Z → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (Y : ℝ),
      |z.2| ≤ M * Real.sqrt (T : ℝ) →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      Integrable (fun w : Z => bellmanOriginExtension phi (w.1 - Y, w.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2)) (kernelXV E T z) ∧
      (∫ w, |bellmanOriginExtension phi (w.1 - Y, w.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2)| ∂kernelXV E T z) ≤
        C * (T : ℝ) ^ (alpha / 2) := by
  obtain ⟨B, hB, hb⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
  exact deterministic_barrier_endpoint_uniform_of_modulus hH hLE hlam hLam
    alpha B M ha.le ha1.le hB _ (h.origin_extension_continuous ha) hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
