module

public import HypoellipticAleksandrov.Parabolic.WeakEquationMollification
public import HypoellipticAleksandrov.Parabolic.ParabolicConvolutionCommutator

/-!
# Compact decay of weak-equation mollification residuals

This module identifies the explicit residual of a supplied global weak jet
with the parabolic convolution commutator and obtains its compact finite-norm
decay from Borel elliptic coefficient data.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The residual of weak-equation mollification is definitionally the
coefficient--Hessian parabolic convolution commutator. -/
@[simp] theorem weakEquationMollificationResidual_eq_parabolicConvolutionCommutator
    {d : Nat} {p : ENNReal} (Aext : CoefficientField d)
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    weakEquationMollificationResidual Aext g n =
      parabolicConvolutionCommutator Aext g.velocityHessian n :=
  rfl

/-- The explicit weak-equation mollification residual of a supplied global
weak jet converges to zero in finite parabolic norm on every compact carrier. -/
theorem tendsto_eLpNorm_weakEquationMollificationResidual_on_compact
    (d : Nat) (lam Lam : Real) (Aext : CoefficientField d)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    (K : Set (TimeVelocity d)) (hK : IsCompact K)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext) :
    Tendsto (fun n => eLpNorm
      (weakEquationMollificationResidual Aext g n)
      (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) := by
  simpa only [weakEquationMollificationResidual_eq_parabolicConvolutionCommutator] using
    tendsto_eLpNorm_parabolicConvolutionCommutator_on_compact
      Aext g.velocityHessian K hK (3 * (|lam| + |Lam|))
      (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (fun i j =>
        (measurable_pi_iff.mp (measurable_pi_iff.mp hExtBorel i) j).aestronglyMeasurable)
      (fun i j =>
        locallyIntegrable_coefficientAt_entry_of_ellipticity
          hExtBorel hExtLower hExtUpper i j)
      (fun i j z =>
        coefficient_entry_abs_le_of_ellipticity
          (hExtLower z.1 z.2) (hExtUpper z.1 z.2) i j)
      (fun i j => by
        have h := g.velocityHessian_memLp i j
        change MemLp (fun z => g.velocityHessian z i j) (parabolicExponent d)
          ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
        simpa only [Measure.restrict_univ] using h)

end HypoellipticAleksandrov.Parabolic
