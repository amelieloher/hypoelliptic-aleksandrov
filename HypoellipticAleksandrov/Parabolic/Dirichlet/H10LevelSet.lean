module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import PDEFoundation.Sobolev.H1.LevelSets
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Level-set locality for the Hilbert realization of spatial `H¹₀`

This module proves the geometry-free Stampacchia property for the selected
value and gradient representatives of `H10HilbertGraph`.  The argument is
local: on every ball compactly contained in the open domain, the graph point
defines an `H¹` representative, to which the existing bounded-convex theorem
applies.  A countable subcover then recovers the original open domain.

No boundedness, convexity, or boundary regularity is assumed of the original
domain, and the proof does not use the zero-boundary closure property.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The concrete representatives selected by a Hilbert `H¹₀` graph point,
viewed as a representative-level `H¹` function. -/
private def h1FunctionOfH10HilbertGraph
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) : PDE.H1Function Ω where
  toFun := valueCLM hΩ u
  grad := fun x => (gradientCLM hΩ u x).ofLp
  memL2 := Lp.memLp (valueCLM hΩ u)
  gradMemL2 := fun i =>
    (Lp.memLp (gradientCLM hΩ u)).eval_piLp i
  hasWeakGradient := by
    intro i
    rw [PDE.hasWeakPartialDerivOn_iff_forall_testFunction]
    intro φ
    apply eq_neg_iff_add_eq_zero.mpr
    have hconstraint := PDE.W1pGraph.constraint_eq_zero
      (PDE.H1HilbertGraph.toH1Graph
        (u : PDE.H1HilbertGraph Ω)) i φ
    simpa only [PDE.weakGradientConstraint_apply_eq_integral, valueCLM_apply,
      gradientCLM_apply, PDE.H1HilbertGraph.value, PDE.H1HilbertGraph.gradient,
      PDE.volumeOn, PDE.H1HilbertGraph.toH1Graph, PDE.h1HilbertAmbientEquiv,
        WithLp.prodContinuousLinearEquiv] using! hconstraint

@[simp]
private theorem h1FunctionOfH10HilbertGraph_toFun
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    (h1FunctionOfH10HilbertGraph hΩ u).toFun = valueCLM hΩ u :=
  rfl

@[simp]
private theorem h1FunctionOfH10HilbertGraph_grad
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    (h1FunctionOfH10HilbertGraph hΩ u).grad =
      fun x => (gradientCLM hΩ u x).ofLp :=
  rfl

/-- On an arbitrary open domain, the selected weak gradient of a spatial
`H¹₀` graph point vanishes almost everywhere on each fixed level set of
its selected value representative. -/
theorem gradientCLM_ae_zero_on_level_set
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) (c : ℝ) :
    ∀ᵐ x ∂(PDE.volumeOn Ω),
      valueCLM hΩ u x = c → gradientCLM hΩ u x = 0 := by
  let w : PDE.H1Function Ω := h1FunctionOfH10HilbertGraph hΩ u
  have hballs : ∀ x : Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : PDE.Vec d) r ⊆ Ω := by
    intro x
    exact Metric.isOpen_iff.mp hΩ x x.property
  choose r hrPos hrSub using hballs
  let B : Ω → Set (PDE.Vec d) := fun x => Metric.ball (x : PDE.Vec d) (r x)
  have hBOpen : ∀ x, IsOpen (B x) := fun x => Metric.isOpen_ball
  have hcover : Ω ⊆ ⋃ x, B x := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hrPos ⟨y, hy⟩)⟩
  obtain ⟨s, hsCountable, hsCover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      B hBOpen hcover
  have hUnionSub : (⋃ x ∈ s, B x) ⊆ Ω := by
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨x, _hx, hxy⟩ := hy
    exact hrSub x hxy
  have hUnion : (⋃ x ∈ s, B x) = Ω :=
    Subset.antisymm hUnionSub hsCover
  have hOnUnion :
      ∀ᵐ y ∂volume.restrict (⋃ x ∈ s, B x),
        valueCLM hΩ u y = c → gradientCLM hΩ u y = 0 := by
    rw [ae_restrict_biUnion_iff B hsCountable]
    intro x hx
    have hBDomain : PDE.IsOpenBoundedConvexDomain (B x) := by
      refine ⟨Metric.isOpen_ball, ?_, convex_ball (x : PDE.Vec d) (r x)⟩
      exact PDE.Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball
    have hlocal := PDE.H1Function.grad_ae_zero_on_level_set
      hBDomain (w.restrict Metric.isOpen_ball (hrSub x)) c
    filter_upwards [hlocal] with y hy
    intro hyLevel
    apply (WithLp.ofLp_eq_zero 2).mp
    exact hy hyLevel
  have hmeasure :
      PDE.volumeOn Ω = volume.restrict (⋃ x ∈ s, B x) := by
    rw [hUnion]
  have hae : ae (PDE.volumeOn Ω) =
      ae (volume.restrict (⋃ x ∈ s, B x)) := congrArg ae hmeasure
  exact hOnUnion.filter_mono hae.le

end HypoellipticAleksandrov.Parabolic.Dirichlet
