module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinODE
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Reverse-time finite Galerkin energy bounds

This module derives the finite-dimensional primal energy estimates from the
reverse-time Galerkin ODE.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

private def galerkinEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (t : ℝ) : ℝ :=
  ‖valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2

private def galerkinEnergyDeriv
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (t : ℝ) : ℝ :=
  2 * inner ℝ
    (valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))
    (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))

private def galerkinGradientEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (t : ℝ) : ℝ :=
  ‖gradientCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2

private theorem sum_smul_clm_apply
    {I E : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (e : I → E) (x : I → ℝ) :
    ∑ i, x i * L (e i) = L (∑ i, x i • e i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [smul_eq_mul] using (L.map_smul (x i) (e i)).symm

private theorem sum_smul_inner_right
    {I E : Type} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (e : I → E) (x : I → ℝ) :
    ∑ i, x i * inner ℝ v (e i) = inner ℝ v (∑ i, x i • e i) := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right]

private theorem coe_galerkinReconstruct_eq_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) := by
  exact congrArg (fun u : galerkinSpace hΩ N => (u : H10HilbertGraph hΩ))
    (galerkinReconstruct_apply hΩ N x)

private theorem map_galerkinReconstruct_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : H10HilbertGraph hΩ →L[ℝ] Z)
    (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
    Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
  calc
    Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
        Q (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) := by
      exact congrArg Q (coe_galerkinReconstruct_eq_sum hΩ N x)
    _ = Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
      have hcoe : (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) =
          ∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
        simpa only [Submodule.coe_smul] using
        (Submodule.coe_sum (p := galerkinSpace hΩ N)
          (fun i => x i • galerkinSpaceBasis hΩ N i) Finset.univ)
      exact congrArg Q hcoe
    _ = ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
      calc
        Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) =
            ∑ i, Q (x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) :=
          map_sum Q (fun i => x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))
            Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          exact Q.map_smul (x i) (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)

private theorem reverseTimeGalerkin_rows_sum
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hrows : ∀ i,
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) :
    inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      reverseTimeSourceFunctional hΩ
        (reverseTimeSourceSlice r₁ τ.1 F
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
            τ.1 τ.2))
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) := by
  let vdot : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)
  let u : H10HilbertGraph hΩ := galerkinReconstruct hΩ N x
  let e : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → H10HilbertGraph hΩ :=
    fun i => galerkinSpaceBasis hΩ N i
  let B : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ u
  let q : H10HilbertGraph hΩ →L[ℝ] ℝ :=
    reverseTimeSourceFunctional hΩ
      (reverseTimeSourceSlice r₁ τ.1 F
        (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
          τ.1 τ.2))
  have hsum : ∑ i, x i *
      (inner ℝ vdot (valueCLM hΩ (e i)) + B (e i)) =
      ∑ i, x i * q (e i) := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [vdot, e, B, q, reverseTimeSpatialFormOperator_apply,
      reverseTimeGalerkinSource_eq] using congrArg (fun z => x i * z) (hrows i)
  have hsum_left : ∑ i, x i *
      (inner ℝ vdot (valueCLM hΩ (e i)) + B (e i)) =
      inner ℝ vdot (valueCLM hΩ u) + B u := by
    have hvalue := map_galerkinReconstruct_sum hΩ N (valueCLM hΩ) x
    have hform := map_galerkinReconstruct_sum hΩ N B x
    have hinner : ∑ i, x i * inner ℝ vdot (valueCLM hΩ (e i)) =
        inner ℝ vdot (valueCLM hΩ u) := by
      change ∑ i, x i * inner ℝ vdot
        (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) = _
      rw [sum_smul_inner_right]
      exact congrArg (inner ℝ vdot) hvalue.symm
    have hB : ∑ i, x i * B (e i) = B u := by
      change ∑ i, x i * B (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) = B u
      simpa only [smul_eq_mul] using hform.symm
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hinner, hB]
  have hsum_right : (∑ i, x i * q (e i)) = q u := by
    have hq := map_galerkinReconstruct_sum hΩ N q x
    change ∑ i, x i * q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) = q u
    simpa only [smul_eq_mul] using hq.symm
  simpa only [vdot, u, B, q, reverseTimeSpatialFormOperator_apply] using
    hsum_left.symm.trans (hsum.trans hsum_right)

private theorem hasDerivWithinAt_value_reconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    {s : Set ℝ} {τ : ℝ}
    (hx : HasDerivWithinAt x xdot s τ) :
    HasDerivWithinAt
      (fun t => valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)) s τ := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp R
  have hV := (V.hasFDerivAt).comp_hasDerivWithinAt τ hx
  simpa only [V, R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
    LinearMap.coe_toContinuousLinearMap'] using! hV

private theorem hasDerivWithinAt_energy_reconstruct
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    {s : Set ℝ} {τ : ℝ}
    (hx : HasDerivWithinAt x xdot s τ) :
    HasDerivWithinAt
      (fun t => ‖valueCLM hΩ (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)‖ ^ 2)
      (2 * inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
  exact (hasDerivWithinAt_value_reconstruct hΩ N x xdot hx).norm_sq

private theorem energy_differential_algebra
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (lam K M : ℝ) (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ)
    (w f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (B : ℝ)
    (hidentity : inner ℝ w (valueCLM hΩ u) + B = -inner ℝ (valueCLM hΩ u) f)
    (hgarding : (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤ B)
    (hsource : ‖f‖ ≤ M) :
    2 * inner ℝ (valueCLM hΩ u) w ≤
      (2 * K + 1) * ‖valueCLM hΩ u‖ ^ 2 + M ^ 2 -
        lam * ‖gradientCLM hΩ u‖ ^ 2 := by
  have hforcing : -inner ℝ (valueCLM hΩ u) f ≤ ‖valueCLM hΩ u‖ * M := by
    calc
      -inner ℝ (valueCLM hΩ u) f ≤ |inner ℝ (valueCLM hΩ u) f| := neg_le_abs _
      _ ≤ ‖valueCLM hΩ u‖ * ‖f‖ := abs_real_inner_le_norm (valueCLM hΩ u) f
      _ ≤ ‖valueCLM hΩ u‖ * M :=
        mul_le_mul_of_nonneg_left hsource (norm_nonneg _)
  have hyoung : 2 * ‖valueCLM hΩ u‖ * M ≤ ‖valueCLM hΩ u‖ ^ 2 + M ^ 2 := by
    nlinarith [sq_nonneg (‖valueCLM hΩ u‖ - M)]
  rw [real_inner_comm]
  nlinarith

private theorem continuousOn_galerkinEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ)
    (hx : ContinuousOn x s) :
    ContinuousOn (galerkinEnergy hΩ N x) s := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp R
  have hV : ContinuousOn (fun t => V (x t)) s :=
    V.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  simpa only [galerkinEnergy, V, R, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
    LinearMap.coe_toContinuousLinearMap'] using! hV.norm.pow 2

private theorem galerkinEnergy_zero_le_initial
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hx0 : x 0 = (galerkinSpaceBasis hΩ N).equivFun
      (galerkinInitialProjection hΩ N initial)) :
    galerkinEnergy hΩ N x 0 ≤ ‖initial‖ ^ 2 := by
  have hrec : (galerkinReconstruct hΩ N (x 0) : H10HilbertGraph hΩ) =
      (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := by
    calc
      (galerkinReconstruct hΩ N (x 0) : H10HilbertGraph hΩ) =
          (galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun
            (galerkinInitialProjection hΩ N initial)) : H10HilbertGraph hΩ) :=
        congrArg (fun z => (galerkinReconstruct hΩ N z : H10HilbertGraph hΩ)) hx0
      _ = (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) :=
        congrArg (fun v : galerkinSpace hΩ N => (v : H10HilbertGraph hΩ))
          (galerkinReconstruct_equivFun hΩ N (galerkinInitialProjection hΩ N initial))
  rw [galerkinEnergy, hrec]
  have hnorm := norm_value_galerkinInitialProjection_le hΩ N initial
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm

private theorem continuousOn_galerkinGradientEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ)
    (hx : ContinuousOn x s) :
    ContinuousOn (galerkinGradientEnergy hΩ N x) s := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let W := (gradientCLM hΩ).comp R
  have hW : ContinuousOn (fun t => W (x t)) s :=
    W.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  simpa only [galerkinGradientEnergy, W, R, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
    LinearMap.coe_toContinuousLinearMap'] using! hW.norm.pow 2

private theorem ContinuousOn.clm_apply_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} (A : ℝ → E →L[ℝ] E) (f x : ℝ → E)
    (hA : ContinuousOn A s) (hf : ContinuousOn f s) (hx : ContinuousOn x s) :
    ContinuousOn (fun t => A t (x t) + f t) s := by
  exact (hA.clm_apply hx).add hf

private theorem continuousOn_two_mul_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set ℝ} (v w : ℝ → E)
    (hv : ContinuousOn v s) (hw : ContinuousOn w s) :
    ContinuousOn (fun t => 2 * inner ℝ (v t) (w t)) s := by
  exact continuousOn_const.mul (hv.inner hw)

private theorem galerkin_energy_deriv_ineq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam K M : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hGarding : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph hΩ,
      (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u)
    (hsource : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => F (r₁ - τ) y)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M)
    (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (τ : Set.Icc 0 (r₁ - r₀))
    (hdx : HasDerivWithinAt x
      (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth N τ (x τ) +
      reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
      (Set.Icc 0 (r₁ - r₀)) τ)
    (hrows : ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
              H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) :
    HasDerivWithinAt (galerkinEnergy hΩ N x)
      (galerkinEnergyDeriv hΩ N x
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) τ)
      (Set.Icc 0 (r₁ - r₀)) τ ∧
    galerkinEnergyDeriv hΩ N x
        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth N τ (x τ) +
        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) τ +
      lam * galerkinGradientEnergy hΩ N x τ ≤
      (2 * K + 1) * galerkinEnergy hΩ N x τ + M ^ 2 := by
  let xdot := reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth N τ (x τ) +
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ
  let u : H10HilbertGraph hΩ := galerkinReconstruct hΩ N (x τ)
  let f : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    reverseTimeSourceSlice r₁ τ.1 F
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
        τ.1 τ.2)
  have hderiv : HasDerivWithinAt (galerkinEnergy hΩ N x)
      (galerkinEnergyDeriv hΩ N x xdot τ) (Set.Icc 0 (r₁ - r₀)) τ := by
    simpa only [galerkinEnergy, galerkinEnergyDeriv] using!
      hasDerivWithinAt_energy_reconstruct hΩ N x xdot hdx
  refine ⟨hderiv, ?_⟩
  have hid := reverseTimeGalerkin_rows_sum r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N τ (x τ) xdot (by
      intro i
      simpa only [xdot] using hrows i)
  have hid' : inner ℝ
      (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
      (valueCLM hΩ u) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c u u =
      -inner ℝ (valueCLM hΩ u) f := by
    simpa only [u, f, reverseTimeSourceFunctional_apply] using hid
  have hbound := energy_differential_algebra lam K M hΩ u
    (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)) f
    (reverseTimeSpatialForm hΩ r₁ τ.1 a b c u u) hid'
    (hGarding τ.1 τ.2 u)
    (hsource τ.1 τ.2
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
        τ.1 τ.2))
  simpa only [galerkinEnergyDeriv, galerkinGradientEnergy, galerkinEnergy, xdot, u] using
    (le_sub_iff_add_le.mp hbound)

private theorem continuousOn_galerkinEnergyDeriv
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ)
    (x xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ)
    (hx : ContinuousOn x s) (hxdot : ContinuousOn xdot s) :
    ContinuousOn (fun t => galerkinEnergyDeriv hΩ N x (xdot t) t) s := by
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).comp R
  have hVx : ContinuousOn (fun t => V (x t)) s :=
    V.continuous.continuousOn.comp hx (fun _ _ => Set.mem_univ _)
  have hVxdot : ContinuousOn (fun t => V (xdot t)) s :=
    V.continuous.continuousOn.comp hxdot (fun _ _ => Set.mem_univ _)
  simpa only [galerkinEnergyDeriv, V, R, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, Function.comp_def, Pi.pow_def,
    LinearMap.coe_toContinuousLinearMap'] using!
    continuousOn_two_mul_inner _ _ hVx hVxdot

private theorem exists_galerkin_energy_constants
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph hΩ,
        (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤
          reverseTimeSpatialForm hΩ r₁ τ a b c u u) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
        ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => F (r₁ - τ) y)
          (2 : ℝ≥0∞) (PDE.volumeOn Ω),
          ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M := by
  obtain ⟨K, hK, hGarding⟩ :=
    reverseTimeSpatialForm_garding_of_smoothOnNeighborhood r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  obtain ⟨M, hM, hsource⟩ :=
    exists_reverseTimeSourceSlice_L2_bound_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
  exact ⟨K, hK, hGarding, M, hM, hsource⟩


private theorem reverseTimeGalerkin_uniform_energy_solution_fixed
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (K M : ℝ) (hK : 0 ≤ K)
    (hGarding : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ u : H10HilbertGraph hΩ,
      (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 - K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u)
    (hsource : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ hτLp : MeasureTheory.MemLp (fun y : PDE.Vec d => F (r₁ - τ) y)
        (2 : ℝ≥0∞) (PDE.volumeOn Ω),
        ‖hτLp.toLp (fun y : PDE.Vec d => F (r₁ - τ) y)‖ ≤ M) :
    ∀ N : ℕ, ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
      ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧ ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ (valueCLM hΩ (galerkinReconstruct hΩ N
              (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth N τ (x τ) +
              reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                H10HilbertGraph hΩ))
              (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
            reverseTimeSpatialForm hΩ r₁ τ.1 a b c (u τ : H10HilbertGraph hΩ)
              (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
            reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ∧
        (∀ t ∈ Set.Icc 0 (r₁ - r₀),
          ‖valueCLM hΩ (u t : H10HilbertGraph hΩ)‖ ^ 2 ≤
            gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
        ∀ t ∈ Set.Icc 0 (r₁ - r₀),
          lam * ∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ : H10HilbertGraph hΩ)‖ ^ 2 ≤
            ‖initial‖ ^ 2 + (2 * K + 1) * t *
              gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (r₁ - r₀) + M ^ 2 * t := by
  intro N initial
  have hsol := exists_reverseTimeGalerkin_solution r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth N initial
  let x := hsol.choose
  let u := hsol.choose_spec.choose
  have hspec := hsol.choose_spec.choose_spec
  have hx0 := hspec.1
  have hu := hspec.2.1
  have hxcont := hspec.2.2.1
  have hucont := hspec.2.2.2.1
  have hode := hspec.2.2.2.2
  let T : ℝ := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) := fun t =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth N
      (Set.projIcc 0 T hT t)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun t =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N (Set.projIcc 0 T hT t)
  let xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun t => A t (x t) + f t
  have hxdot : ContinuousOn xdot (Set.Icc 0 T) := by
    have hA : Continuous A := (continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth N).comp continuous_projIcc
    have hf : Continuous f := (continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F
      hFSmooth N).comp continuous_projIcc
    exact (hA.continuousOn.clm_apply hxcont).add hf.continuousOn
  let D : ℝ → ℝ := fun t => galerkinEnergyDeriv hΩ N x (xdot t) t
  have hDcont : ContinuousOn D (Set.Icc 0 T) :=
    continuousOn_galerkinEnergyDeriv hΩ N x xdot _ hxcont hxdot
  have hEcont := continuousOn_galerkinEnergy hΩ N x (Set.Icc 0 T) hxcont
  have hGcont := continuousOn_galerkinGradientEnergy hΩ N x (Set.Icc 0 T) hxcont
  have hEicc : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (galerkinEnergy hΩ N x) (D t) (Set.Icc 0 T) t := by
    intro t ht
    let τ : Set.Icc 0 (r₁ - r₀) := ⟨t, by simpa only [T] using ht⟩
    have hp : Set.projIcc 0 T hT t = τ := Set.projIcc_of_mem hT ht
    simpa only [D, xdot, A, f, T, hp] using
      (galerkin_energy_deriv_ineq r₀ r₁ lam K M h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hGarding hsource N x τ (hode τ).1
        (by simpa only [hu] using (hode τ).2)).1
  have hEineq : ∀ t ∈ Set.Icc 0 T,
      D t + lam * galerkinGradientEnergy hΩ N x t ≤
        (2 * K + 1) * galerkinEnergy hΩ N x t + M ^ 2 := by
    intro t ht
    let τ : Set.Icc 0 (r₁ - r₀) := ⟨t, by simpa only [T] using ht⟩
    have hp : Set.projIcc 0 T hT t = τ := Set.projIcc_of_mem hT ht
    simpa only [D, xdot, A, f, T, hp] using
      (galerkin_energy_deriv_ineq r₀ r₁ lam K M h₀₁ hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hGarding hsource N x τ (hode τ).1
        (by simpa only [hu] using (hode τ).2)).2
  have hE0 := galerkinEnergy_zero_le_initial hΩ N initial x hx0
  have hEbound : ∀ t ∈ Set.Icc 0 T,
      galerkinEnergy hΩ N x t ≤ gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t := by
    have hbound : ∀ t ∈ Set.Icc 0 T,
        galerkinEnergy hΩ N x t ≤
          gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (t - 0) := by
      apply le_gronwallBound_of_liminf_deriv_right_le hEcont
      · intro t ht r hr
        have hgrad : 0 ≤ lam * galerkinGradientEnergy hΩ N x t :=
          mul_nonneg hlam.le (sq_nonneg _)
        have hDle : D t ≤ (2 * K + 1) * galerkinEnergy hΩ N x t + M ^ 2 :=
          (le_add_of_nonneg_right hgrad).trans (hEineq t (Set.Ico_subset_Icc_self ht))
        exact ((hEicc t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht)).liminf_right_slope_le (hDle.trans_lt hr)
      · simpa only [T] using hE0
      · intro t ht
        have hg : 0 ≤ galerkinGradientEnergy hΩ N x t := sq_nonneg _
        linarith [hEineq t (Set.Ico_subset_Icc_self ht)]
    simpa only [sub_zero] using hbound
  refine ⟨x, u, hx0, hu, hxcont, hucont, hode, ?_, ?_⟩
  · intro t ht
    simpa only [u, hu, galerkinEnergy, T] using hEbound t ht
  intro t ht
  have htT : t ∈ Set.Icc 0 T := by simpa only [T] using ht
  let R := gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) T
  have hA0 : 0 ≤ 2 * K + 1 := by linarith
  have hconst : ∀ s ∈ Set.Icc 0 t,
      D s + lam * galerkinGradientEnergy hΩ N x s ≤ (2 * K + 1) * R + M ^ 2 := by
    intro s hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans htT.2⟩
    have hER : galerkinEnergy hΩ N x s ≤ R := (hEbound s hsT).trans
      (gronwallBound_mono (sq_nonneg _) (sq_nonneg _) hA0 (hs.2.trans htT.2))
    have hmult := mul_le_mul_of_nonneg_left hER hA0
    linarith [hEineq s hsT]
  have hleft : IntervalIntegrable (fun s => D s + lam * galerkinGradientEnergy hΩ N x s)
      MeasureTheory.volume 0 t := ((hDcont.add (continuousOn_const.mul hGcont)).mono
        (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 t :=
    (hDcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hGint : IntervalIntegrable (galerkinGradientEnergy hΩ N x)
      MeasureTheory.volume 0 t :=
    (hGcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  have hLGint : IntervalIntegrable (fun s => lam * galerkinGradientEnergy hΩ N x s)
      MeasureTheory.volume 0 t := hGint.const_mul lam
  have hint := intervalIntegral.integral_mono_on ht.1 hleft
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (2 * K + 1) * R + M ^ 2) MeasureTheory.volume 0 t)
    (by
      intro s hs
      exact hconst s hs)
  have hFTC : (∫ s in 0..t, D s) = galerkinEnergy hΩ N x t - galerkinEnergy hΩ N x 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      (hEcont.mono (Set.Icc_subset_Icc le_rfl htT.2))
    · intro s hs
      have hsIcc : s ∈ Set.Icc 0 T := ⟨hs.1.le, hs.2.le.trans htT.2⟩
      have hsIco : s ∈ Set.Ico 0 T := ⟨hs.1.le, hs.2.trans_le htT.2⟩
      exact (hEicc s hsIcc).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hsIco)
    · exact (hDcont.mono (Set.Icc_subset_Icc le_rfl htT.2)).intervalIntegrable_of_Icc ht.1
  rw [intervalIntegral.integral_add hDint hLGint, intervalIntegral.integral_const_mul, hFTC,
    intervalIntegral.integral_const] at hint
  have hEt : 0 ≤ galerkinEnergy hΩ N x t := sq_nonneg _
  have hrhs : t * ((2 * K + 1) * R + M ^ 2) =
      (2 * K + 1) * t * R + M ^ 2 * t := by
    ring
  rw [sub_zero, smul_eq_mul, hrhs] at hint
  have hgrad : lam * (∫ s in 0..t, galerkinGradientEnergy hΩ N x s) ≤
      ‖initial‖ ^ 2 + (2 * K + 1) * t * R + M ^ 2 * t := by
    linarith [hint, hE0]
  simpa only [u, hu, galerkinGradientEnergy, R, T, intervalIntegral.integral_of_le ht.1] using
    hgrad

private theorem reverseTimeGalerkin_uniform_energy_solution_aux
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ N : ℕ, ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
      ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
      ∃ u : ℝ → galerkinSpace hΩ N,
        x 0 = (galerkinSpaceBasis hΩ N).equivFun (galerkinInitialProjection hΩ N initial) ∧
        u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
        ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧ ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
        (∀ τ : Set.Icc 0 (r₁ - r₀),
          HasDerivWithinAt x
            (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth N τ (x τ) +
            reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
            (Set.Icc 0 (r₁ - r₀)) τ ∧
          ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
            inner ℝ (valueCLM hΩ (galerkinReconstruct hΩ N
              (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth N τ (x τ) +
              reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                H10HilbertGraph hΩ))
              (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
            reverseTimeSpatialForm hΩ r₁ τ.1 a b c (u τ : H10HilbertGraph hΩ)
              (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
            reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ∧
        (∀ t ∈ Set.Icc 0 (r₁ - r₀),
          ‖valueCLM hΩ (u t : H10HilbertGraph hΩ)‖ ^ 2 ≤
            gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
        ∀ t ∈ Set.Icc 0 (r₁ - r₀),
          lam * ∫ τ in Set.Ioc 0 t, ‖gradientCLM hΩ (u τ : H10HilbertGraph hΩ)‖ ^ 2 ≤
            ‖initial‖ ^ 2 + (2 * K + 1) * t *
              gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) (r₁ - r₀) + M ^ 2 * t := by
  let constants := exists_galerkin_energy_constants r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
  let K : ℝ := constants.choose
  have hK : 0 ≤ K := constants.choose_spec.1
  have hGarding := constants.choose_spec.2.1
  let M : ℝ := constants.choose_spec.2.2.choose
  have hM : 0 ≤ M := constants.choose_spec.2.2.choose_spec.1
  have hsource := constants.choose_spec.2.2.choose_spec.2
  refine ⟨K, hK, M, hM, ?_⟩
  exact reverseTimeGalerkin_uniform_energy_solution_fixed r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth K M hK hGarding hsource

/-- Smooth finite Galerkin systems have uniform primal energy bounds. -/
theorem exists_reverseTimeGalerkin_uniform_energy_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ N : ℕ, ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
          ∃ x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ,
            ∃ u : ℝ → galerkinSpace hΩ N,
              x 0 = (galerkinSpaceBasis hΩ N).equivFun
                (galerkinInitialProjection hΩ N initial) ∧
              u = (fun τ => galerkinReconstruct hΩ N (x τ)) ∧
              ContinuousOn x (Set.Icc 0 (r₁ - r₀)) ∧
              ContinuousOn u (Set.Icc 0 (r₁ - r₀)) ∧
              (∀ τ : Set.Icc 0 (r₁ - r₀),
                HasDerivWithinAt x
                  (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                    haSmooth hbSmooth hcSmooth N τ (x τ) +
                  reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ)
                  (Set.Icc 0 (r₁ - r₀)) τ ∧
                ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
                  inner ℝ
                      (valueCLM hΩ (galerkinReconstruct hΩ N
                        (reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
                          haSmooth hbSmooth hcSmooth N τ (x τ) +
                        reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ) :
                          H10HilbertGraph hΩ))
                      (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
                    reverseTimeSpatialForm hΩ r₁ τ.1 a b c
                      (u τ : H10HilbertGraph hΩ)
                      (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
                    reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i) ∧
              (∀ t ∈ Set.Icc 0 (r₁ - r₀),
                ‖valueCLM hΩ (u t : H10HilbertGraph hΩ)‖ ^ 2 ≤
                  gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2) t) ∧
              ∀ t ∈ Set.Icc 0 (r₁ - r₀),
                lam * ∫ τ in Set.Ioc 0 t,
                    ‖gradientCLM hΩ (u τ : H10HilbertGraph hΩ)‖ ^ 2 ≤
                  ‖initial‖ ^ 2 +
                    (2 * K + 1) * t *
                      gronwallBound (‖initial‖ ^ 2) (2 * K + 1) (M ^ 2)
                        (r₁ - r₀) +
                    M ^ 2 * t := by
  exact reverseTimeGalerkin_uniform_energy_solution_aux r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos

end HypoellipticAleksandrov.Parabolic.Dirichlet
