module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution

/-!
# Scalar versus `z`-independent kinetic classical solutions (outside context)

A scalar classical terminal solution `W` of the parabolic problem with coefficient `B σ y 0` and
terminal datum `F` is the same thing as a classical terminal solution `W(σ, y)` of the transported
kinetic problem with the `z`-independent datum `F(y)`, provided `B` does not depend on `z`
(`hBz`; needed only for scalar to kinetic).  This is the reduction that makes the scalar marginal
uniqueness a consequence of the kinetic comparison.

* `IsClassicalScalarTerminalSolution.toKinetic`: scalar solution lifted along `(σ, y, z) ↦ (σ, y)`.
* `IsClassicalTerminalSolution.toScalar`: a `z`-independent kinetic solution restricted to `z = 0`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory

section Scalar

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {B : FullKineticCoefficient n}
  {b : PDE.Vec n → PDE.Vec n} {τ : ℝ} {F : BoundedBorel (PDE.Vec n)}

theorem classicalGradient_const_eq_zero (c : ℝ) (x : PDE.Vec n) :
    PDE.classicalGradient (fun _ : PDE.Vec n => c) x = 0 := by
  ext i
  simp [PDE.classicalGradient]

/-- A classical scalar terminal solution, lifted along `(σ, y, z) ↦ (σ, y)`, is a classical
kinetic terminal solution for the `z`-independent datum, when `B` does not depend on `z`. -/
theorem ParabolicProbe.IsClassicalScalarTerminalSolution.toKinetic
    {W : TimeVelocity n → ℝ}
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (hW : ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F W) :
    IsClassicalTerminalSolution Ω γ B b τ (lowerDatum F)
      (fun p => W (p.time, p.position)) := by
  obtain ⟨⟨C, hC0, hC⟩, hcont, hsmooth, hop, hterm, hlat⟩ := hW
  have hpr : Continuous (fun p : KineticPoint n => (p.time, p.position)) :=
    continuous_time.prodMk continuous_position
  refine ⟨⟨C, hC0, fun p hp => hC _ hp⟩, hcont.comp hpr.continuousOn (fun p hp => hp), ?_, ?_,
    ?_, ?_⟩
  · have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => (q.1, q.2.1)) :=
      contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
    exact hsmooth.comp h2.contDiffOn (fun q hq => hq)
  · intro p hp
    have h0 := hop (p.time, p.position) hp
    have hz : kineticVelocityGradient (fun p : KineticPoint n => W (p.time, p.position)) p = 0 :=
      classicalGradient_const_eq_zero (n := n) (W (p.time, p.position)) p.velocity
    have hv1 : PDE.vecDot (b p.position) (0 : PDE.Vec n) = 0 := by simp [PDE.vecDot]
    have hv2 : ∀ g : PDE.Vec n,
        PDE.vecDot ((0 : ℝ → PDE.Vec n → PDE.Vec n) p.time p.position) g = 0 := by
      intro g
      simp [PDE.vecDot]
    rw [transportedForwardOperator_apply, hz, hv1, fullKineticCoefficientAt_apply,
      hBz p.time p.position p.velocity 0, add_zero]
    rw [scalarParabolicOperator_apply, hv2, add_zero] at h0
    exact h0
  · intro p hp
    exact hterm (p.time, p.position) hp
  · intro p hp
    exact hlat (p.time, p.position) hp

/-- A classical kinetic terminal solution of the `z`-independent datum which does not depend on
`z` on the past closed cylinder restricts, at `z = 0`, to a classical scalar terminal solution. -/
theorem IsClassicalTerminalSolution.toScalar
    {V : KineticPoint n → ℝ}
    (hV : IsClassicalTerminalSolution Ω γ B b τ (lowerDatum F) V)
    (hz : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, V p = V ⟨p.time, p.position, 0⟩) :
    ParabolicProbe.IsClassicalScalarTerminalSolution Ω γ B τ F
      (fun q => V ⟨q.1, q.2, 0⟩) := by
  obtain ⟨⟨C, hC0, hC⟩, hcont, hsmooth, hop, hterm, hlat⟩ := hV
  have hin : ∀ q : TimeVelocity n,
      q ∈ ParabolicProbe.scalarPastClosedCylinder Ω γ τ →
        (⟨q.1, q.2, 0⟩ : KineticPoint n) ∈ evolutionPastClosedCylinder Ω γ τ :=
    fun q hq => hq
  have hemb : Continuous (fun q : TimeVelocity n => (⟨q.1, q.2, 0⟩ : KineticPoint n)) :=
    (KineticPoint.homeomorphProd n).symm.continuous.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  refine ⟨⟨C, hC0, fun q hq => hC _ (hin q hq)⟩, hcont.comp hemb.continuousOn hin, ?_, ?_, ?_, ?_⟩
  · have h2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : TimeVelocity n => ((q.1, (q.2, (0 : PDE.Vec n))) :
          ℝ × (PDE.Vec n × PDE.Vec n))) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
    exact hsmooth.comp h2.contDiffOn (fun q hq => hq)
  · intro q hq
    have h0 := hop ⟨q.1, q.2, 0⟩ hq
    have hconst : (fun v : PDE.Vec n => V ⟨q.1, q.2, v⟩) = fun _ => V ⟨q.1, q.2, 0⟩ := by
      funext v
      exact hz ⟨q.1, q.2, v⟩ ⟨hq.1.le, subset_closure hq.2⟩
    have hg : kineticVelocityGradient V ⟨q.1, q.2, 0⟩ = 0 := by
      show PDE.classicalGradient (fun v : PDE.Vec n => V ⟨q.1, q.2, v⟩) 0 = 0
      rw [hconst]
      exact classicalGradient_const_eq_zero _ _
    have hv1 : PDE.vecDot (b q.2) (0 : PDE.Vec n) = 0 := by simp [PDE.vecDot]
    have hv2 : ∀ g : PDE.Vec n,
        PDE.vecDot ((0 : ℝ → PDE.Vec n → PDE.Vec n) q.1 q.2) g = 0 := by
      intro g
      simp [PDE.vecDot]
    rw [transportedForwardOperator_apply, hg] at h0
    change kineticTimeDerivative V ⟨q.1, q.2, 0⟩ +
      matrixContraction (B q.1 q.2 0) (diffusedHessian V ⟨q.1, q.2, 0⟩) +
        PDE.vecDot (b q.2) (0 : PDE.Vec n) = 0 at h0
    rw [hv1, add_zero] at h0
    rw [scalarParabolicOperator_apply, hv2, add_zero]
    exact h0
  · intro q hq
    have := hterm ⟨q.1, q.2, 0⟩ hq
    simpa using this
  · intro q hq
    exact hlat ⟨q.1, q.2, 0⟩ hq

end Scalar

end HypoellipticAleksandrov.KineticAleksandrov
