module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Equation
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.RpowCalculus
import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FisherBeta

/-!
# The divergence form of the smoothed equation

The smoothed equation, equation its divergence form: on a non-zero slice
`∂_τ ρ + v·∇_z ρ = div_{z,v}(G Dρ) + div_v(ρ div_v β_h)` with
`G = [[λh²/2 I, -λh/2 I], [-λh/2 I, β_h]]`, written out with the coordinate partials of
`Calculus.lean`: the `z`-component of `G Dρ` is `gradFluxZ`, the `v`-component is `gradFluxV`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory

variable {d : ℕ}

/-- The `z`-component `(λh²/2) ∂_{z_i} ρ - (λh/2) ∂_{v_i} ρ` of `G Dρ`. -/
def gradFluxZ (lam h : ℝ) (ρ : EvolutionAmbientState d → ℝ) (i : Fin d)
    (y : EvolutionAmbientState d) : ℝ :=
  lam * h ^ 2 / 2 * positionPartial i ρ y - lam * h / 2 * velocityPartial i ρ y

/-- The `v`-component `-(λh/2) ∂_{z_i} ρ + ∑_j β_{ij} ∂_{v_j} ρ` of `G Dρ`. -/
def gradFluxV (lam h : ℝ) (β : EvolutionAmbientState d → PDE.Mat d)
    (ρ : EvolutionAmbientState d → ℝ) (i : Fin d) (y : EvolutionAmbientState d) : ℝ :=
  -(lam * h / 2) * positionPartial i ρ y + ∑ j, β y i j * velocityPartial j ρ y

/-- The divergence `div_{z,v}(G Dρ)` of the vector field `G Dρ`. -/
def divGradFlux (lam h : ℝ) (β : EvolutionAmbientState d → PDE.Mat d)
    (ρ : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i (gradFluxZ lam h ρ i) y +
    ∑ i, velocityPartial i (gradFluxV lam h β ρ i) y

/-- The lower-order term `div_v(ρ div_v β) = ∑_i ∂_{v_i}(ρ ∑_j ∂_{v_j} β_{ij})`. -/
def divDensityDivBeta (β : EvolutionAmbientState d → PDE.Mat d)
    (ρ : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, velocityPartial i (fun y => ρ y * ∑ j, velocityPartial j (fun y => β y i j) y) y

/-- Symmetry of mixed second partial derivatives of a smooth function. -/
theorem coordPartial_comm {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    coordPartial c (coordPartial c' F) y = coordPartial c' (coordPartial c F) y := by
  have key : ∀ c c' : Fin d ⊕ Fin d, coordPartial c (coordPartial c' F) y =
      fderiv ℝ (fderiv ℝ F) y (coordDir c) (coordDir c') := fun c c' => by
    have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
      ((hF.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero) y
    have hfun : coordPartial c' F = fun x => fderiv ℝ F x (coordDir c') := rfl
    rw [coordPartial, hfun, fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) _ _

theorem coordPartial_finsetSum_at {y : EvolutionAmbientState d} {ι : Type} (s : Finset ι)
    {f : ι → EvolutionAmbientState d → ℝ} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) y)
    (c : Fin d ⊕ Fin d) :
    coordPartial c (fun y => ∑ i ∈ s, f i y) y = ∑ i ∈ s, coordPartial c (f i) y := by
  unfold coordPartial
  rw [(HasFDerivAt.fun_sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp

theorem coordPartial_lin₂ {y : EvolutionAmbientState d} {f g : EvolutionAmbientState d → ℝ}
    (a b : ℝ) (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) (c : Fin d ⊕ Fin d) :
    coordPartial c (fun y => a * f y + b * g y) y =
      a * coordPartial c f y + b * coordPartial c g y := by
  rw [coordPartial_add c (hf.const_mul a) (hg.const_mul b), coordPartial_const_mul' c a hf,
    coordPartial_const_mul' c b hg]

variable {ρ : EvolutionAmbientState d → ℝ} {β : EvolutionAmbientState d → PDE.Mat d}

theorem differentiable_gradFluxV_sum (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j) (i : Fin d) :
    Differentiable ℝ fun y => ∑ j, β y i j * velocityPartial j ρ y :=
  Differentiable.fun_sum fun j _ => ((hβ i j).differentiable (by simp)).mul
    (differentiable_coordPartial hρ (Sum.inl j))

/-- The `div_{z,v}(G Dρ)` expanded: the mixed terms combine by symmetry of second derivatives. -/
theorem divGradFlux_eq (lam h : ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j) (y : EvolutionAmbientState d) :
    divGradFlux lam h β ρ y =
      lam * h ^ 2 / 2 * positionLaplacian ρ y - lam * h * mixedDivergence ρ y +
        ∑ i, velocityPartial i (fun y => ∑ j, β y i j * velocityPartial j ρ y) y := by
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
  have hV : ∀ i, velocityPartial i (gradFluxV lam h β ρ i) y =
      -(lam * h / 2) * velocityPartial i (positionPartial i ρ) y +
        velocityPartial i (fun y => ∑ j, β y i j * velocityPartial j ρ y) y := fun i => by
    have e : gradFluxV lam h β ρ i = fun y => -(lam * h / 2) * positionPartial i ρ y +
        1 * ∑ j, β y i j * velocityPartial j ρ y := funext fun y => by unfold gradFluxV; ring
    have := coordPartial_lin₂ (-(lam * h / 2)) 1 (hdρ (Sum.inr i) y)
      (differentiable_gradFluxV_sum hρ hβ i y) (Sum.inl i)
    rw [e]
    simp only [positionPartial_eq, velocityPartial_eq] at this ⊢
    rw [this]
    ring
  have hM : ∀ i, positionPartial i (velocityPartial i ρ) y =
      velocityPartial i (positionPartial i ρ) y := fun i => by
    simp only [positionPartial_eq, velocityPartial_eq]
    exact coordPartial_comm hρ _ _ y
  unfold divGradFlux positionLaplacian mixedDivergence
  simp_rw [hZ, hV, hM]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Leibniz rule for the flux `J = ρ β`:
`∑_{ij} ∂_{v_i} ∂_{v_j} (ρ β_{ij}) = ∑_i ∂_{v_i}(∑_j β_{ij} ∂_{v_j} ρ) + div_v(ρ div_v β)`. -/
theorem hessian_flux_eq (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j) (y : EvolutionAmbientState d) :
    ∑ i, ∑ j, velocityPartial i (velocityPartial j (fun y => ρ y * β y i j)) y =
      ∑ i, velocityPartial i (fun y => ∑ j, β y i j * velocityPartial j ρ y) y +
        divDensityDivBeta β ρ y := by
  have hdρ : ∀ c, Differentiable ℝ (coordPartial c ρ) := fun c => differentiable_coordPartial hρ c
  have hdβ : ∀ i j, Differentiable ℝ fun y => β y i j := fun i j =>
    (hβ i j).differentiable (by simp)
  have hdβ' : ∀ i j c, Differentiable ℝ (coordPartial c fun y => β y i j) := fun i j c =>
    differentiable_coordPartial (hβ i j) c
  have hleib : ∀ i j z, velocityPartial j (fun y => ρ y * β y i j) z =
      β z i j * velocityPartial j ρ z + ρ z * velocityPartial j (fun y => β y i j) z :=
    fun i j z => by
    rw [velocityPartial_eq, coordPartial_mul _ (hρ.differentiable (by simp) z) (hdβ i j z)]
    simp only [velocityPartial_eq]
    ring
  unfold divDensityDivBeta
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ∀ j, velocityPartial i (velocityPartial j (fun y => ρ y * β y i j)) y =
      velocityPartial i (fun y => β y i j * velocityPartial j ρ y +
        ρ y * velocityPartial j (fun y => β y i j) y) y := fun j => by
    congr 1
    funext z
    exact hleib i j z
  simp_rw [e1]
  have hd1 : ∀ j, DifferentiableAt ℝ (fun y => β y i j * velocityPartial j ρ y) y := fun j =>
    (hdβ i j y).mul (hdρ (Sum.inl j) y)
  have hd2 : ∀ j, DifferentiableAt ℝ
      (fun y => ρ y * velocityPartial j (fun y => β y i j) y) y := fun j =>
    (hρ.differentiable (by simp) y).mul (hdβ' i j (Sum.inl j) y)
  have hs1 : velocityPartial i (fun y => ∑ j, β y i j * velocityPartial j ρ y) y =
      ∑ j, velocityPartial i (fun y => β y i j * velocityPartial j ρ y) y :=
    coordPartial_finsetSum_at Finset.univ (fun j _ => hd1 j) (Sum.inl i)
  have hs2 : velocityPartial i (fun y => ρ y * ∑ j, velocityPartial j (fun y => β y i j) y) y =
      ∑ j, velocityPartial i (fun y => ρ y * velocityPartial j (fun y => β y i j) y) y := by
    have e : (fun y => ρ y * ∑ j, velocityPartial j (fun y => β y i j) y) =
        fun y => ∑ j, ρ y * velocityPartial j (fun y => β y i j) y :=
      funext fun _ => Finset.mul_sum _ _ _
    rw [e]
    exact coordPartial_finsetSum_at Finset.univ (fun j _ => hd2 j) (Sum.inl i)
  rw [hs1, hs2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => coordPartial_add (Sum.inl i) (hd1 j) (hd2 j)

variable {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h τ T : ℝ}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)} {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- **The smoothed equation in divergence form**: on a non-zero slice,
`∂_τ ρ + v·∇_z ρ = div_{z,v}(G Dρ) + div_v(ρ div_v β_h)`. -/
theorem smoothed_equation_div (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hδ : 0 < δ) (hτ : δ < τ) (hτT : τ + δ < T)
    (hfwd : IsForwardMeasure T Bt Γ')
    (hcomm : ∀ w, transportDerivative (Φ.kernel h) w =
      lam * h ^ 2 / 2 * positionLaplacian (Φ.kernel h) w -
        lam * h * mixedDivergence (Φ.kernel h) w)
    (hm : averagedSlice η τ Γ' ≠ 0) (y : EvolutionAmbientState d) :
    deriv (fun τ' => smoothedDensity Φ η h Γ' τ' y) τ +
        transportDerivative (smoothedDensity Φ η h Γ' τ) y =
      divGradFlux lam h (smoothedBeta Φ η Bt Lam h Γ' τ) (smoothedDensity Φ η h Γ' τ) y +
        divDensityDivBeta (smoothedBeta Φ η Bt Lam h Γ' τ) (smoothedDensity Φ η h Γ' τ) y := by
  have hfin := hD.finite
  have hνfin := isFiniteMeasure_averagedSlice (τ := τ) hη hD.marginal
  have hcoef := isAdmissibleCoefficient_averagedCoefficient (η := η) (τ := τ) (Γ' := Γ')
    hD.symm hD.loewner
  have hρ : ContDiff ℝ (⊤ : ℕ∞) (smoothedDensity Φ η h Γ' τ) :=
    contDiff_smoothDensity Φ (averagedSlice η τ Γ') hh
  have hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => smoothedBeta Φ η Bt Lam h Γ' τ y i j :=
    fun i j => contDiff_smoothCoefficient_entry Φ (averagedSlice η τ Γ') hD.lam_pos hcoef hh hm i j
  have hJ : ∀ i j, (fun y => smoothedFlux Φ η Bt Lam h Γ' τ y i j) =
      fun y => smoothedDensity Φ η h Γ' τ y * smoothedBeta Φ η Bt Lam h Γ' τ y i j :=
    fun i j => funext fun y => smoothFluxEntry_eq_mul Φ (averagedSlice η τ Γ') hh hm i j y
  rw [smoothed_equation Φ hη hD hh hδ hτ hτT hfwd hcomm y]
  simp_rw [hJ]
  rw [hessian_flux_eq hρ hβ y, divGradFlux_eq lam h hρ hβ y]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
