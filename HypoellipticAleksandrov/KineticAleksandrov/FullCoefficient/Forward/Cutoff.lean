module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Joint
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Product cut-offs for the forward equation

The admissible test functions: the product cut-off `ζ_R(v, z) = ζ(v/R) ζ(z/R²)` of a smooth bump
`ζ`.
Its velocity partials are `O(1/R)` and `O(1/R²)`, and the transport error `v · ∇_z ζ_R` is
`O(1/R)` because `|v| ≤ 2R` on the support of the velocity factor.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set

variable {d : ℕ}

/-- Derivative of a dilated function. -/
theorem fderiv_comp_const_smul' (f : PDE.Vec d → ℝ) (c : ℝ) (v w : PDE.Vec d)
    (hf : DifferentiableAt ℝ f (c • v)) :
    fderiv ℝ (fun v => f (c • v)) v w = c * fderiv ℝ f (c • v) w := by
  have h : HasFDerivAt (fun v : PDE.Vec d => f (c • v)) ((fderiv ℝ f (c • v)).comp
      (c • ContinuousLinearMap.id ℝ (PDE.Vec d))) v :=
    hf.hasFDerivAt.comp v ((hasFDerivAt_id v).const_smul c)
  rw [h.fderiv]
  simp

/-- Velocity partial of a product of a velocity factor and a position factor. -/
theorem velocityPartial_mul_split (a b : PDE.Vec d → ℝ) (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) (i : Fin d) (y : EvolutionAmbientState d) :
    velocityPartial i (fun y : EvolutionAmbientState d => a y.1 * b y.2) y =
      fderiv ℝ a y.1 (Pi.single i 1) * b y.2 := by
  have h1 : HasFDerivAt (fun y : EvolutionAmbientState d => a y.1)
      ((fderiv ℝ a y.1).comp (ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    (ha y.1).hasFDerivAt.comp y (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun y : EvolutionAmbientState d => b y.2)
      ((fderiv ℝ b y.2).comp (ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    (hb y.2).hasFDerivAt.comp y (hasFDerivAt_snd)
  unfold velocityPartial
  rw [(h1.fun_mul h2).fderiv]
  simp [mul_comm]

/-- Position partial of a product of a velocity factor and a position factor. -/
theorem positionPartial_mul_split (a b : PDE.Vec d → ℝ) (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) (i : Fin d) (y : EvolutionAmbientState d) :
    positionPartial i (fun y : EvolutionAmbientState d => a y.1 * b y.2) y =
      a y.1 * fderiv ℝ b y.2 (Pi.single i 1) := by
  have h1 : HasFDerivAt (fun y : EvolutionAmbientState d => a y.1)
      ((fderiv ℝ a y.1).comp (ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    (ha y.1).hasFDerivAt.comp y (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun y : EvolutionAmbientState d => b y.2)
      ((fderiv ℝ b y.2).comp (ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    (hb y.2).hasFDerivAt.comp y (hasFDerivAt_snd)
  unfold positionPartial
  rw [(h1.fun_mul h2).fderiv]
  simp

/-- Second velocity partials of a product of a velocity factor and a position factor. -/
theorem velocityPartial_velocityPartial_mul_split (a b : PDE.Vec d → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : Differentiable ℝ b) (i j : Fin d)
    (y : EvolutionAmbientState d) :
    velocityPartial i (velocityPartial j (fun y : EvolutionAmbientState d => a y.1 * b y.2)) y =
      fderiv ℝ (fun v => fderiv ℝ a v (Pi.single j 1)) y.1 (Pi.single i 1) * b y.2 := by
  have hfun : velocityPartial j (fun y : EvolutionAmbientState d => a y.1 * b y.2) =
      fun y : EvolutionAmbientState d => fderiv ℝ a y.1 (Pi.single j 1) * b y.2 := by
    funext y
    exact velocityPartial_mul_split a b (ha.differentiable (by simp)) hb j y
  rw [hfun]
  exact velocityPartial_mul_split _ b ((contDiff_fderiv_apply ha _).differentiable (by simp)) hb i y
/-- Uniform bounds for the first two derivative layers of a compactly supported smooth bump. -/
theorem exists_bump_bounds {ζ : PDE.Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x i, |fderiv ℝ ζ x (Pi.single i 1)| ≤ M) ∧
      ∀ x i j, |fderiv ℝ (fun v => fderiv ℝ ζ v (Pi.single j 1)) x (Pi.single i 1)| ≤ M := by
  have h1 : ∀ i : Fin d, ∃ C : ℝ, ∀ x, ‖fderiv ℝ ζ x (Pi.single i 1)‖ ≤ C := fun i =>
    ((contDiff_fderiv_apply hζ _).continuous).bounded_above_of_compact_support
      (hc.fderiv_apply ℝ _)
  choose C1 hC1 using h1
  have h2 : ∀ i j : Fin d, ∃ C : ℝ, ∀ x,
      ‖fderiv ℝ (fun v => fderiv ℝ ζ v (Pi.single j 1)) x (Pi.single i 1)‖ ≤ C := fun i j =>
    (contDiff_fderiv_apply (contDiff_fderiv_apply hζ _) _).continuous
      |>.bounded_above_of_compact_support
      ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _)
  choose C2 hC2 using h2
  have hn1 : ∀ i, 0 ≤ C1 i := fun i => (norm_nonneg _).trans (hC1 i 0)
  have hn2 : ∀ i j, 0 ≤ C2 i j := fun i j => (norm_nonneg _).trans (hC2 i j 0)
  refine ⟨∑ i, C1 i + ∑ i, ∑ j, C2 i j, add_nonneg (Finset.sum_nonneg fun i _ => hn1 i)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn2 i j), fun x i => ?_,
    fun x i j => ?_⟩
  · have := (Real.norm_eq_abs _ ▸ hC1 i x : |fderiv ℝ ζ x (Pi.single i 1)| ≤ C1 i)
    have h3 : C1 i ≤ ∑ i, C1 i := Finset.single_le_sum (fun i _ => hn1 i) (Finset.mem_univ i)
    have h4 : 0 ≤ ∑ i, ∑ j, C2 i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn2 i j
    linarith
  · have := (Real.norm_eq_abs _ ▸ hC2 i j x :
      |fderiv ℝ (fun v => fderiv ℝ ζ v (Pi.single j 1)) x (Pi.single i 1)| ≤ C2 i j)
    have h3 : C2 i j ≤ ∑ j, C2 i j :=
      Finset.single_le_sum (fun j _ => hn2 i j) (Finset.mem_univ j)
    have h5 : ∑ j, C2 i j ≤ ∑ i, ∑ j, C2 i j :=
      Finset.single_le_sum (f := fun i => ∑ j, C2 i j)
        (fun i _ => Finset.sum_nonneg fun j _ => hn2 i j) (Finset.mem_univ i)
    have h4 : 0 ≤ ∑ i, C1 i := Finset.sum_nonneg fun i _ => hn1 i
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
