module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelJets

/-!
# Time cutoffs and the transported adjoint

For a smooth function `χ` of the time coordinate alone,
`Lop^*(χ(σ) ψ) = χ(σ) Lop^* ψ - χ'(σ) ψ`, and `Lop^* ψ` vanishes off the topological support of
`ψ`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/-- Product rule for a time cutoff. -/
theorem fderiv_cutoff_mul {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {f : EvolutionVec d → ℝ}
    {x : EvolutionVec d} (hf : DifferentiableAt ℝ f x) (v : EvolutionVec d) :
    fderiv ℝ (fun y => χ (Evolution.timeCoord d y) * f y) x v =
      χ (Evolution.timeCoord d x) * fderiv ℝ f x v +
        deriv χ (Evolution.timeCoord d x) * Evolution.timeCoord d v * f x := by
  have hc : HasFDerivAt (fun y => χ (Evolution.timeCoord d y))
      (deriv χ (Evolution.timeCoord d x) • Evolution.timeCoord d) x :=
    (hχ _).hasDerivAt.comp_hasFDerivAt x (Evolution.timeCoord d).hasFDerivAt
  rw [(hc.fun_mul hf.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The cutoff commutation formula for the transported adjoint. -/
theorem transportedAdjoint_cutoff_mul {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (hB : IsSmoothFullKineticCoefficient B) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : EvolutionVec d) :
    transportedAdjoint B b (fun y => χ (Evolution.timeCoord d y) * ψ y) x =
      χ (Evolution.timeCoord d x) * transportedAdjoint B b ψ x -
        deriv χ (Evolution.timeCoord d x) * ψ x := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE d).contDiff
  have hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) :=
    fun i j => (hA i j).mul hψ
  have hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EvolutionVec d => fderiv ℝ (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) := fun i j => contDiff_fderiv_apply (hF i j) _
  have hψd : ∀ y, DifferentiableAt ℝ ψ y := fun y => differentiableAt_of_contDiff hψ y
  unfold transportedAdjoint
  have t1 := fderiv_cutoff_mul (d := d) hχd (hψd x) basisT
  have t3 : ∀ l, fderiv ℝ (fun y => χ (Evolution.timeCoord d y) * ψ y) x (basisZ l) =
      χ (Evolution.timeCoord d x) * fderiv ℝ ψ x (basisZ l) := by
    intro l
    rw [fderiv_cutoff_mul hχd (hψd x), timeCoord_basisZ]
    ring
  have t2 : ∀ i j, fderiv ℝ (fun y => fderiv ℝ (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j *
        (χ (Evolution.timeCoord d w) * ψ w)) y (basisV j)) x (basisV i) =
      χ (Evolution.timeCoord d x) * fderiv ℝ (fun y => fderiv ℝ (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) x (basisV i) := by
    intro i j
    have hin : (fun y => fderiv ℝ (fun w : EvolutionVec d =>
        B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j *
          (χ (Evolution.timeCoord d w) * ψ w)) y (basisV j)) =
        fun y => χ (Evolution.timeCoord d y) * fderiv ℝ (fun w : EvolutionVec d =>
          B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
            (basisV j) := by
      funext y
      have hfun : (fun w : EvolutionVec d =>
          B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j *
            (χ (Evolution.timeCoord d w) * ψ w)) =
          fun w => χ (Evolution.timeCoord d w) * (B (Evolution.timeCoord d w)
            (diffusedCoord d w) (transportedCoord d w) i j * ψ w) := by
        funext w; ring
      rw [hfun, fderiv_cutoff_mul hχd ((hF i j).differentiable (by simp) y), timeCoord_basisV]
      ring
    rw [hin, fderiv_cutoff_mul hχd (((hG i j).differentiable (by simp)) x), timeCoord_basisV]
    ring
  simp only [t2, t3, t1, timeCoord_basisT]
  simp only [mul_left_comm _ (χ (Evolution.timeCoord d x)), ← Finset.mul_sum]
  ring

/-- The transported adjoint vanishes off the topological support of the test. -/
theorem transportedAdjoint_eq_zero_of_notMem_tsupport {B : FullKineticCoefficient d}
    {b : PDE.Vec d → PDE.Vec d} (ψ : EvolutionVec d → ℝ) {x : EvolutionVec d}
    (hx : x ∉ tsupport ψ) : transportedAdjoint B b ψ x = 0 := by
  have hz : ∀ (φ : EvolutionVec d → ℝ) (v : EvolutionVec d), tsupport φ ⊆ tsupport ψ →
      fderiv ℝ φ x v = 0 := fun φ v hφ =>
    image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v)
      (fun h => hx (hφ (tsupport_evolution_fderiv_apply φ v h)))
  have h1 : fderiv ℝ ψ x basisT = 0 := hz ψ _ subset_rfl
  have h3 : ∀ l, fderiv ℝ ψ x (basisZ l) = 0 := fun l => hz ψ _ subset_rfl
  have h2 : ∀ i j, fderiv ℝ (fun y => fderiv ℝ (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) x (basisV i) = 0 := by
    intro i j
    refine hz _ _ ?_
    intro y hy
    have hy1 := tsupport_evolution_fderiv_apply _ (basisV j) hy
    exact tsupport_mul_subset_right hy1
  unfold transportedAdjoint
  simp only [h1, h2, h3, mul_zero, Finset.sum_const_zero, neg_zero, add_zero, sub_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
