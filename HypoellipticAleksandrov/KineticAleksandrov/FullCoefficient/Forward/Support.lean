module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Smoothness and support of the joint forward expression

For smooth `G` the expression `forwardRepr B b G` is smooth, and its topological support lies in
that of `G`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem tsupport_jointTimePartial_subset (G : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (jointTimePartial G) ⊆ tsupport G :=
  tsupport_fderiv_apply_subset ℝ (f := G) ((1 : ℝ), (0 : EvolutionAmbientState d))

theorem tsupport_jointVelocityPartial_subset (G : ℝ × EvolutionAmbientState d → ℝ) (i : Fin d) :
    tsupport (jointVelocityPartial i G) ⊆ tsupport G :=
  tsupport_fderiv_apply_subset ℝ (f := G) ((0 : ℝ), ((Pi.single i 1 : PDE.Vec d), (0 : PDE.Vec d)))

theorem tsupport_jointPositionPartial_subset (G : ℝ × EvolutionAmbientState d → ℝ) (i : Fin d) :
    tsupport (jointPositionPartial i G) ⊆ tsupport G :=
  tsupport_fderiv_apply_subset ℝ (f := G) ((0 : ℝ), ((0 : PDE.Vec d), (Pi.single i 1 : PDE.Vec d)))

/-- The forward expression vanishes off the topological support of the function. -/
theorem forwardRepr_eq_zero_of_notMem_tsupport (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (G : ℝ × EvolutionAmbientState d → ℝ)
    {q : ℝ × EvolutionAmbientState d} (hq : q ∉ tsupport G) : forwardRepr B b G q = 0 := by
  have h1 : jointTimePartial G q = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hq (tsupport_jointTimePartial_subset G h))
  have h2 : ∀ i j, jointVelocityPartial i (jointVelocityPartial j G) q = 0 := fun i j =>
    image_eq_zero_of_notMem_tsupport (fun h => hq (tsupport_jointVelocityPartial_subset G j
      (tsupport_jointVelocityPartial_subset _ i h)))
  have h3 : ∀ i, jointPositionPartial i G q = 0 := fun i =>
    image_eq_zero_of_notMem_tsupport (fun h => hq (tsupport_jointPositionPartial_subset G i h))
  simp [forwardRepr, h1, h2, h3]

/-- The topological support of the forward expression lies in that of the function. -/
theorem tsupport_forwardRepr_subset (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (G : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (forwardRepr B b G) ⊆ tsupport G := by
  refine closure_minimal ?_ (isClosed_tsupport G)
  intro q hq
  by_contra h
  exact hq (forwardRepr_eq_zero_of_notMem_tsupport B b G h)

/-- The forward expression of a smooth function is smooth. -/
theorem contDiff_forwardRepr {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {G : ℝ × EvolutionAmbientState d → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (forwardRepr B b G) := by
  unfold forwardRepr
  refine ((contDiff_jointTimePartial hG).add
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_)).add (ContDiff.sum fun i _ => ?_)
  · exact (hB i j).mul (contDiff_jointVelocityPartial (contDiff_jointVelocityPartial hG j) i)
  · have hbi : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d => b q.2.1 i) :=
      (contDiff_apply ℝ ℝ i).comp (hb.comp (contDiff_snd.fst))
    exact hbi.mul (contDiff_jointPositionPartial hG i)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
