module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs

/-! # Position cutoff calculus in the fixed packed kinetic coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- Exact derivative of a scalar cutoff depending only on transported position. -/
theorem reconstruction_position_cutoff_fderiv (chi : ℝ → ℝ)
    (hchi : Differentiable ℝ chi) (x w : EvolutionVec 1) :
    fderiv ℝ (fun y => chi (transportedCoord 1 y 0)) x w =
      deriv chi (transportedCoord 1 x 0) * transportedCoord 1 w 0 := by
  let c : EvolutionVec 1 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp (transportedCoord 1)
  have hc := (hchi (c x)).hasDerivAt.comp_hasFDerivAt x c.hasFDerivAt
  have hh := congrArg (fun L : EvolutionVec 1 →L[ℝ] ℝ => L w) hc.fderiv
  simpa only [c, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_apply, smul_eq_mul] using! hh

/-- Only the transport derivative contributes to a pure position cutoff product. -/
theorem reconstruction_position_cutoff_operator
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (f : EvolutionVec 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : EvolutionVec 1) :
    transportedOperator B b (fun y => chi (transportedCoord 1 y 0) * f y) x =
      chi (transportedCoord 1 x 0) * transportedOperator B b f x +
        b (diffusedCoord 1 x) 0 * deriv chi (transportedCoord 1 x 0) * f x := by
  let c : EvolutionVec 1 → ℝ := fun y => chi (transportedCoord 1 y 0)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    hchi.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (transportedCoord 1).contDiff)
  have hcd := hc.differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  have hcv (y : EvolutionVec 1) : fderiv ℝ c y (basisV (0 : Fin 1)) = 0 := by
    rw [reconstruction_position_cutoff_fderiv _ (hchi.differentiable (by simp))]
    simp only [basisV, transportedCoord_packPoint, Pi.zero_apply, mul_zero]
  have hct : fderiv ℝ c x basisT = 0 := by
    rw [reconstruction_position_cutoff_fderiv _ (hchi.differentiable (by simp))]
    simp only [basisT, transportedCoord_packPoint, Pi.zero_apply, mul_zero]
  have hcz : fderiv ℝ c x (basisZ (0 : Fin 1)) = deriv chi (transportedCoord 1 x 0) := by
    rw [reconstruction_position_cutoff_fderiv _ (hchi.differentiable (by simp))]
    simp only [basisZ, transportedCoord_packPoint, Pi.single_eq_same, mul_one]
  have hv : (fun y => fderiv ℝ (fun z => c z * f z) y (basisV (0 : Fin 1))) =
      fun y => c y * fderiv ℝ f y (basisV (0 : Fin 1)) := by
    funext y
    rw [fderiv_fun_mul (hcd y) (hfd y)]
    simp only [add_apply, smul_apply,
      smul_eq_mul, hcv, mul_zero, add_zero]
  have hfv : Differentiable ℝ (fun y => fderiv ℝ f y (basisV (0 : Fin 1))) :=
    ((hf.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  change transportedOperator B b (fun y => c y * f y) x = _
  simp only [transportedOperator, Fin.sum_univ_one]
  rw [hv, fderiv_fun_mul (hcd x) (hfd x), fderiv_fun_mul (hcd x) (hfv x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, hcv, hct, hcz, mul_zero, add_zero]
  dsimp only [c]
  ring

/-- The physical operator of every smooth packed test agrees with the native packed operator. -/
theorem reconstruction_physical_operator_packed {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph)) (p : Point) :
    forwardScalarOperator A.a phi p =
      transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
        (phi ∘ reconstructionPhysicalHomeomorph) (reconstructionPhysicalHomeomorph.symm p) := by
  let x := reconstructionPhysicalHomeomorph.symm p
  have heq : (phi ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1 =
      phi ∘ reconstructionPhysicalHomeomorph := rfl
  have hs : ContDiffAt ℝ 2 ((phi ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x := by
    rw [heq]
    exact (hphi.of_le (by simp)).contDiffAt
  have hop := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hs
  rw [heq, reconstruction_scalar_operator_swap] at hop
  have hx : sectionTwoPoint (evolutionHomeomorph 1 x) = p :=
    reconstructionPhysicalHomeomorph.apply_symm_apply p
  rw [hx] at hop
  exact hop.symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
