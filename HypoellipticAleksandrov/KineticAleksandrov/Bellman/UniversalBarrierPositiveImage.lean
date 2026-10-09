module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationary
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierSeparation
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalization
import Mathlib.Tactic

/-! # The annihilating probability would produce an adjoint degree above the supremum -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Above the adjoint threshold a homogeneous function has strictly positive sphere image. -/
theorem exists_positive_bellman_image (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) :
    ∃ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi ∧
      ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
        0 < bellmanOperator b.val phi z.val := by
  obtain ⟨hapos, _, hgap⟩ := bellman_barrier_parameter_range lam Lam hlam hLam alpha ha ha1
  by_contra hno
  obtain ⟨pi, hpi, hann⟩ :=
    exists_annihilating_bellman_probability lam Lam alpha hlam hLam hapos ha1 hno
  let := hpi
  have hp := radial_bellman_pair_stationary lam Lam alpha hlam hLam hapos ha1 pi hann
  have hd : 2 + alpha ∈ bellmanDegrees lam Lam := ⟨radialMu alpha pi, radialEta alpha pi, hp⟩
  rw [bellman_degrees_normalize lam Lam hlam hLam] at hd
  have hupper := (bellmanAdjointExponent_characterization (Lam / lam)
    (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam)).1.1 hd
  exact (not_le_of_gt hgap) hupper

end HypoellipticAleksandrov.KineticAleksandrov
