module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibility
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import Mathlib.Tactic

/-!
# Proposed corollary: Hölder continuity for one-dimensional autonomous coefficients

Source: companion paper, Corollary 9.10. The coefficient is
literally Borel a(x,v) with values in [lam,Lam]; the equation is homogeneous a.e.
The estimate and compact-inner-cylinder convention are (9.7).
Conditional theorem; the improved density assertion remains an explicit hypothesis.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder
open scoped MatrixOrder

/-- Source c:holder-a under the classical inputs used by t:a and its p=6 comparison. -/
theorem kinetic_holder_autonomous_relative_of_below_four_density
    (hdensity : Autonomous.BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  obtain ⟨C_A, hadm⟩ := autonomous_admissibility_of_below_four_density
    hdensity hH hLE lam Lam hlam hLam
  obtain ⟨alpha, C, ha, ha1, hholder⟩ := kinetic_holder_of_aleksandrov_aux
    1 (by norm_num) lam Lam 6 C_A hlam hLam (by norm_num)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro a hmeas hb Omega hOmega u hbounded hu heq
  have hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint 1)),
      lam • (1 : PDE.Mat 1) ≤
        fullKineticCoefficientAt (Autonomous.autonomousCoefficient a) P :=
    Filter.Eventually.of_forall (fun P => (Autonomous.autonomous_lift_elliptic hb P).1)
  have hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint 1)),
      fullKineticCoefficientAt (Autonomous.autonomousCoefficient a) P ≤
        Lam • (1 : PDE.Mat 1) :=
    Filter.Eventually.of_forall (fun P => (Autonomous.autonomous_lift_elliptic hb P).2)
  exact hholder (Autonomous.autonomousCoefficient a)
    (Autonomous.autonomous_lift_measurable hmeas) (Autonomous.autonomous_lift_symm a)
    hlo hhi Omega hOmega u hbounded (hadm a hmeas hb Omega hOmega u hbounded hu heq)

end HypoellipticAleksandrov.KineticAleksandrov
