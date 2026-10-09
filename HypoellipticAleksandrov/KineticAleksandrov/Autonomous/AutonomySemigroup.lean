module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
import Mathlib.Basic.NNReal.Basic

/-! # The full-space autonomous semigroup on every bounded Borel function -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Insert an ambient state into the unrestricted full-space fiber. -/
def fullspaceState (t : ℝ) (x : EvolutionAmbientState 1) :
    EvolutionState autonomousWholeDomain (fun _ => 0) t :=
  ⟨x, by rw [autonomous_stateSet]; trivial⟩

/-- State insertion is measurable. -/
theorem measurable_fullspaceState (t : ℝ) : Measurable (fullspaceState t) :=
  measurable_id.subtype_mk

/-- Time translation preserves the operator on all bounded Borel terminal data. -/
theorem fullspace_operator_timeShift {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (h σ τ : ℝ) (hστ : σ ≤ τ) :
    E.1 (σ + h) (τ + h) (by linarith) = E.1 σ τ hστ := by
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  let F := f.pullback (fullspaceState τ) (measurable_fullspaceState τ)
  have hm (s t : ℝ) (hst : s ≤ t)
      (x : EvolutionState autonomousWholeDomain (fun _ => 0) s) :
      E.1 s t hst f x = ∫ y, F y ∂E.2.master (evolutionQueryOfState _ _ s t hst x) := by
    have he := integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
      s t hst x F F.measurable
    exact (hE.2.1 s t hst x f).trans he.symm
  have hk := fullspace_kernel_timeShift A E hE h
    (evolutionQueryOfState _ _ σ τ hστ p)
  exact (hm (σ + h) (τ + h) (by linarith) p).trans
    ((congrArg (fun μ => ∫ y, F y ∂μ) hk).trans (hm σ τ hστ p).symm)

/-- The autonomous full-space operator at a nonnegative elapsed time. -/
def fullSpaceSemigroup (E : FullSpaceEvolution) (t : NNReal) :
    BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) →ₗ[ℝ]
      BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) :=
  E.1 0 t t.coe_nonneg

/-- The source composition law holds for every bounded Borel datum. -/
theorem fullSpaceSemigroup_add {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (t s : NNReal) :
    fullSpaceSemigroup E (t + s) =
      (fullSpaceSemigroup E t).comp (fullSpaceSemigroup E s) := by
  have hcomp := fullspace_operator_composition A E hE 0 t (t + s)
    t.coe_nonneg (by linarith [s.coe_nonneg])
  have ht := fullspace_operator_timeShift A E hE t 0 s s.coe_nonneg
  have ht' : E.1 (t : ℝ) ((t : ℝ) + s)
      (by linarith [s.coe_nonneg]) = E.1 0 s s.coe_nonneg := by
    let P (q : {q : ℝ × ℝ // q.1 ≤ q.2}) :
        BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) →ₗ[ℝ]
          BoundedBorel (EvolutionState autonomousWholeDomain (fun _ => 0) 0) :=
      E.1 q.1.1 q.1.2 q.2
    have hq : (⟨(0 + (t : ℝ), (s : ℝ) + t), by linarith [s.coe_nonneg]⟩ :
        {q : ℝ × ℝ // q.1 ≤ q.2}) =
        ⟨((t : ℝ), (t : ℝ) + s), by linarith [s.coe_nonneg]⟩ := by
      apply Subtype.ext
      apply Prod.ext <;> ring
    exact (congrArg P hq).symm.trans ht
  change E.1 0 ((t : ℝ) + s) _ = (E.1 0 t _).comp (E.1 0 s _)
  rw [hcomp, ht']
  rfl

/-- At zero elapsed time the semigroup is the identity. -/
theorem fullSpaceSemigroup_zero {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) :
    fullSpaceSemigroup E 0 = LinearMap.id :=
  realizes_endpoint autonomousWholeDomain_measurable
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE 0

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
