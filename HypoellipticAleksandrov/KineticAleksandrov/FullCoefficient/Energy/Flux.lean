module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Divergence
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.FlowOperator

/-!
# The flux form of the smoothed equation

The smoothed equation (the smoothed equation) and the energy inequality. With
`J = ρ β` the smoothed equation reads `∂_τ ρ + v·∇_z ρ = div_{z,v} (F)` for the vector field
`F = (fluxV, gradFluxZ)`, where `fluxV_i = -(λh/2) ∂_{z_i} ρ + ∑_j ∂_{v_j} J_ij`. Integrating this
form by parts only needs the first and second derivatives of `ρ` and `J`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The `v`-component `-(λh/2) ∂_{z_i} ρ + ∑_j ∂_{v_j} J_ij` of the flux field. -/
def fluxV (lam h : ℝ) (ρ : EvolutionAmbientState d → ℝ) (J : EvolutionAmbientState d → PDE.Mat d)
    (i : Fin d) (y : EvolutionAmbientState d) : ℝ :=
  -(lam * h / 2) * positionPartial i ρ y + ∑ j, velocityPartial j (fun y => J y i j) y

/-- The flux field indexed by the coordinates of phase space, velocity first. -/
def fluxField (lam h : ℝ) (ρ : EvolutionAmbientState d → ℝ)
    (J : EvolutionAmbientState d → PDE.Mat d) :
    Fin d ⊕ Fin d → EvolutionAmbientState d → ℝ
  | Sum.inl i => fluxV lam h ρ J i
  | Sum.inr i => gradFluxZ lam h ρ i

/-- The divergence of the flux field, in the form of the right-hand side of the smoothed equation.
-/
theorem div_fluxField_eq (lam h : ℝ) {ρ : EvolutionAmbientState d → ℝ}
    {J : EvolutionAmbientState d → PDE.Mat d} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hJ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => J y i j) (y : EvolutionAmbientState d) :
    ∑ c, coordPartial c (fluxField lam h ρ J c) y =
      lam * h ^ 2 / 2 * positionLaplacian ρ y - lam * h * mixedDivergence ρ y +
        ∑ i, ∑ j, velocityPartial i (velocityPartial j (fun y => J y i j)) y := by
  have hdρ : ∀ c, Differentiable ℝ (coordPartial c ρ) := fun c => differentiable_coordPartial hρ c
  have hZ : ∀ i, positionPartial i (gradFluxZ lam h ρ i) y =
      lam * h ^ 2 / 2 * positionPartial i (positionPartial i ρ) y -
        lam * h / 2 * positionPartial i (velocityPartial i ρ) y := fun i => by
    have e : gradFluxZ lam h ρ i = fun y => lam * h ^ 2 / 2 * positionPartial i ρ y +
        (-(lam * h / 2)) * velocityPartial i ρ y := funext fun y => by unfold gradFluxZ; ring
    have := coordPartial_lin₂ (lam * h ^ 2 / 2) (-(lam * h / 2)) (hdρ (Sum.inr i) y)
      (hdρ (Sum.inl i) y) (Sum.inr i)
    rw [e]
    simp only [positionPartial_eq, velocityPartial_eq] at this ⊢
    rw [this]
    ring
  have hV : ∀ i, velocityPartial i (fluxV lam h ρ J i) y =
      -(lam * h / 2) * velocityPartial i (positionPartial i ρ) y +
        ∑ j, velocityPartial i (velocityPartial j (fun y => J y i j)) y := fun i => by
    have e : fluxV lam h ρ J i = fun y => -(lam * h / 2) * positionPartial i ρ y +
        1 * ∑ j, velocityPartial j (fun y => J y i j) y := funext fun y => by
      unfold fluxV; ring
    have hd2 : Differentiable ℝ fun y => ∑ j, velocityPartial j (fun y => J y i j) y :=
      Differentiable.fun_sum fun j _ => differentiable_coordPartial (hJ i j) (Sum.inl j)
    have h1 := coordPartial_lin₂ (-(lam * h / 2)) 1 (hdρ (Sum.inr i) y) (hd2 y) (Sum.inl i)
    have h2 := coordPartial_finsetSum_at (y := y) Finset.univ
      (f := fun j y => coordPartial (Sum.inl j) (fun y => J y i j) y)
      (fun j _ => differentiable_coordPartial (hJ i j) (Sum.inl j) y) (Sum.inl i)
    rw [e]
    simp only [positionPartial_eq, velocityPartial_eq] at h1 ⊢
    rw [h1, one_mul, h2]
  have hM : ∀ i, positionPartial i (velocityPartial i ρ) y =
      velocityPartial i (positionPartial i ρ) y := fun i => by
    simp only [positionPartial_eq, velocityPartial_eq]
    exact coordPartial_comm hρ _ _ y
  rw [Fintype.sum_sum_type]
  simp only [fluxField]
  unfold positionLaplacian mixedDivergence
  have e1 : ∀ i, coordPartial (Sum.inl i) (fluxV lam h ρ J i) y =
      velocityPartial i (fluxV lam h ρ J i) y := fun i => rfl
  have e2 : ∀ i, coordPartial (Sum.inr i) (gradFluxZ lam h ρ i) y =
      positionPartial i (gradFluxZ lam h ρ i) y := fun i => rfl
  simp_rw [e1, e2, hZ, hV, hM]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
