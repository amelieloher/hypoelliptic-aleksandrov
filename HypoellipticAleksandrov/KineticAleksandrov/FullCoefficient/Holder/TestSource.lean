module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelMatrixError
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import Mathlib.Analysis.Matrix.MeasurableSpace
import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Smooth-near test functions have bounded sources for Borel full coefficients

For a Borel symmetric coefficient `A(t,x,v)` with
`λ I ≤ A ≤ Λ I` almost everywhere, and a test function `ψ` smooth near the closure of a backward
cylinder, `P_A ψ` is measurable on the cylinder and essentially bounded there; hence it lies in
every `L^q` of the cylinder. Only the almost-everywhere bounds of `A` are used.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory Evolution
open scoped MatrixOrder ENNReal

/-- Source-near smooth tests have the existing anisotropic classical regularity. -/
theorem smoothNear_regular_of_full {d : ℕ} {psi : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hpsi : IsSmoothNear psi E) :
    ∃ U : Set (KineticPoint d), IsOpen U ∧ E ⊆ U ∧ IsKineticC112On psi U := by
  obtain ⟨U, hU, hEU, hs⟩ := hpsi
  refine ⟨U, hU, hEU, TheoremA.isKineticC112On_of_contDiffOn hU ?_⟩
  have h := hs.comp (evolutionProdCLE d).contDiff.contDiffOn (by
    intro x hx
    exact ⟨evolutionHomeomorph d x, hx, rfl⟩)
  exact h

/-- Smooth-near tests have measurable and bounded operator sources on a cylinder, for Borel
coefficients with almost-everywhere bounds. -/
theorem full_test_source {d : ℕ} {A : FullKineticCoefficient d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hBorel : Measurable (fullKineticCoefficientAt A))
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) {psi : KineticPoint d → ℝ}
    (hpsi : IsSmoothNear psi (closure (backwardCylinder P₀ R))) :
    Measurable (fun P : backwardCylinder P₀ R => backwardOperator A psi P) ∧
      ∀ q : ℝ≥0∞, MemLp (fun P => max (backwardOperator A psi P) 0) q
        (volume.restrict (backwardCylinder P₀ R)) := by
  let Q := backwardCylinder P₀ R
  obtain ⟨U, _hU, hQU, hs⟩ := smoothNear_regular_of_full hpsi
  have ht := hs.continuousOn_kineticTimeDerivative.mono hQU
  have hx := hs.continuousOn_kineticPositionGradient.mono hQU
  have hh := hs.continuousOn_kineticVelocityHessian.mono hQU
  have hq : Q ⊆ closure Q := subset_closure
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let : BorelSpace (PDE.Mat d) := inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have hdot : ContinuousOn (fun P : KineticPoint d =>
      PDE.vecDot P.velocity (kineticPositionGradient psi P)) (closure Q) := by
    unfold PDE.vecDot
    exact continuousOn_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_velocity).continuousOn).mul
        ((continuous_apply i).comp_continuousOn hx)
  have hcontr : Measurable (fun P : Q => matrixContraction (fullKineticCoefficientAt A P)
      (kineticVelocityHessian psi P)) := by
    have hHm : Measurable (fun P : Q => kineticVelocityHessian psi P) :=
      (hh.mono hq).domRestrict.measurable
    have hAm : Measurable (fun P : Q => fullKineticCoefficientAt A P) :=
      hBorel.comp measurable_subtype_coe
    unfold matrixContraction
    exact Finset.measurable_fun_sum _ fun i _ =>
      Finset.measurable_fun_sum _ fun k _ => (hAm.eval.eval).mul (hHm.eval.eval)
  have hm : Measurable (fun P : Q => backwardOperator A psi P) := by
    simp only [backwardOperator_apply]
    exact ((ht.mono hq).domRestrict.measurable.add (hdot.mono hq).domRestrict.measurable).sub
      hcontr
  refine ⟨hm, fun q => ?_⟩
  let F : KineticPoint d → ℝ := fun P => |kineticTimeDerivative psi P| +
    |PDE.vecDot P.velocity (kineticPositionGradient psi P)| +
      Real.sqrt d * Lam * borelFrobeniusNorm (kineticVelocityHessian psi P)
  have hFN : ContinuousOn (fun P => borelFrobeniusNorm (kineticVelocityHessian psi P))
      (closure Q) := by
    have h2 := Real.continuous_sqrt.comp_continuousOn (continuousOn_matrixContraction hh hh)
    convert h2 using 1
    funext P
    simp only [borelFrobeniusNorm_eq, matrixContraction, pow_two, Function.comp_def]
  have hF : ContinuousOn F (closure Q) :=
    (ht.abs.add hdot.abs).add (continuousOn_const.mul hFN)
  have hk := isCompact_closure_backwardCylinder P₀ R hR
  obtain ⟨B, hB⟩ := (hk.bddAbove_image hF).exists_ge (0 : ℝ)
  have hLam0 : 0 ≤ Lam := hlam.le.trans hLam
  have hbound : ∀ᵐ P ∂(volume.restrict Q), ‖max (backwardOperator A psi P) 0‖ ≤ B := by
    filter_upwards [ae_restrict_of_ae hlo, ae_restrict_of_ae hhi,
      ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P hl hu hP
    have hA := borel_frobenius_norm_le hlam hLam hl hu
    have hc := (borel_matrix_contraction_le (fullKineticCoefficientAt A P)
      (kineticVelocityHessian psi P)).trans
        (mul_le_mul_of_nonneg_right hA (by
          rw [borelFrobeniusNorm_eq]
          exact Real.sqrt_nonneg _))
    have he : |backwardOperator A psi P| ≤ F P := by
      rw [backwardOperator_apply]
      refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) ?_)
      calc |matrixContraction (fullKineticCoefficientAt A P) (kineticVelocityHessian psi P)|
          ≤ Real.sqrt d * Lam * borelFrobeniusNorm (kineticVelocityHessian psi P) := hc
        _ ≤ _ := le_rfl
    have hFB : F P ≤ B := hB.2 _ (mem_image_of_mem F (hq hP))
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (he.trans hFB)) hB.1
  have hmmax : AEStronglyMeasurable (fun P => max (backwardOperator A psi P) 0)
      (volume.restrict Q) := by
    have hQm : MeasurableSet Q := (isOpen_backwardCylinder P₀ R hR).measurableSet
    have h1 : Measurable ((fun P => max (backwardOperator A psi P) 0) ∘
        ((↑) : Q → KineticPoint d)) := hm.max measurable_const
    exact ((aemeasurable_restrict_iff_comap_subtype hQm).mpr h1.aemeasurable).aestronglyMeasurable
  let : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using volume_backwardCylinder_lt_top P₀ hR⟩
  exact MemLp.of_bound hmmax B hbound

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
