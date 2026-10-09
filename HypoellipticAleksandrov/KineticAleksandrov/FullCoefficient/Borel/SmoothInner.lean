module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Borel.InnerError
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerError
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Passing the coefficient limit on a fixed compact inner cylinder (full coefficients)

The passage from smooth to Borel coefficients. On a fixed compact inner
cylinder the smooth estimate for the mollified coefficients `A_j` is applied to `u` with source
`f + e_j`, where `e_j = |(A_j - A) : D_v² u|`. Since `e_j → 0` in `L^p`, the localized source norms
converge, and the estimate passes to the limit with the same constant.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology ENNReal

/-- The localized estimate for smooth full coefficients with everywhere bounds, with the constant
`C₀` and exponent `alpha` fixed before all coefficient and solution data. -/
def FullSmoothEstimate {d : ℕ} (lam Lam p alpha C₀ : ℝ) : Prop :=
  ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
  ∀ (A : FullKineticCoefficient d),
    IsSmoothFullKineticCoefficient A →
    (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
    (∀ P : KineticPoint d, lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P ∧
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
  ∀ (f u : KineticPoint d → ℝ),
    Measurable (fun P : backwardCylinder P₀ R => f P) →
    ContinuousOn u (closure (backwardCylinder P₀ R)) →
    IsKineticC112On u (backwardCylinder P₀ R) →
    (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)), backwardOperator A u P ≤ f P) →
    MemLp (fun P => max (f P) 0) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) →
    ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
        (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R))).toReal

/-- The operator change is precisely minus the coefficient Hessian contraction. -/
theorem full_backwardOperator_sub {d : ℕ} (C A : FullKineticCoefficient d)
    (u : KineticPoint d → ℝ) (P : KineticPoint d) :
    backwardOperator C u P - backwardOperator A u P =
      -matrixContraction (fullKineticCoefficientAt C P - fullKineticCoefficientAt A P)
        (kineticVelocityHessian u P) := by
  rw [backwardOperator_apply, backwardOperator_apply]
  unfold matrixContraction
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The coefficient limit preserves the complete localized estimate on a fixed inner cylinder. -/
theorem full_smooth_inner_limit {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (hsmooth : FullSmoothEstimate (d := d) lam Lam p alpha C₀)
    (A : FullKineticCoefficient d) (hBorel : Measurable (fullKineticCoefficientAt A))
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))
    (C : ℕ → FullKineticCoefficient d)
    (hC : ∀ j, IsSmoothFullKineticCoefficient (C j) ∧ IsSymmetricFullKineticCoefficient (C j) ∧
      HasEverywhereLoewnerBounds lam Lam (C j))
    (hc : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      Tendsto (fun j => fullKineticCoefficientAt (C j) P) atTop
        (𝓝 (fullKineticCoefficientAt A P)))
    {D : Set (KineticPoint d)} (u f : KineticPoint d → ℝ) (hreg : IsKineticC112On u D)
    (P₁ : KineticPoint d) (r : ℝ) (hr : 0 < r)
    (hK : IsCompact (closure (backwardCylinder P₁ r)))
    (hKD : closure (backwardCylinder P₁ r) ⊆ D)
    (hf : Measurable (fun P : backwardCylinder P₁ r => f P))
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)), backwardOperator A u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
  classical
  let Q := backwardCylinder P₁ r
  let K := closure Q
  let H := kineticVelocityHessian u
  have hH : ContinuousOn H K := hreg.continuousOn_kineticVelocityHessian.mono hKD
  let Hext := K.indicator H
  let e := fun j => fullCoefficientError (C j) A Hext
  have he0 j P : 0 ≤ e j P := abs_nonneg _
  have hQ : IsOpen Q := isOpen_backwardCylinder P₁ r hr
  have hQK : Q ⊆ K := subset_closure
  have hregQ := comparison_regular_mono hreg (hQK.trans hKD)
  have hcontK := hreg.continuousOn.mono hKD
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let : BorelSpace (PDE.Mat d) := inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have hHext : Measurable Hext :=
    hH.measurable_piecewise continuousOn_const hK.measurableSet
  have hem j : Measurable (e j) := by
    have hCs : Continuous (fullKineticCoefficientAt (C j)) :=
      continuous_fullKineticCoefficientAt_of_smooth (hC j).1
    have hs : Measurable (fun P : KineticPoint d =>
        matrixContraction (fullKineticCoefficientAt (C j) P - fullKineticCoefficientAt A P)
          (Hext P)) := by
      unfold matrixContraction
      exact Finset.measurable_fun_sum _ fun i _ =>
        Finset.measurable_fun_sum _ fun k _ =>
          ((hCs.measurable.eval.eval).sub hBorel.eval.eval).mul hHext.eval.eval
    exact continuous_abs.measurable.comp hs
  have heq j : e j =ᵐ[volume.restrict K] fullCoefficientError (C j) A H := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
    simp only [e, fullCoefficientError, Hext, indicator_of_mem hP]
  obtain ⟨hmraw, htraw⟩ := full_inner_error hlam hLam A hBorel hlo hhi C hC hc K hK H hH
    (lt_of_lt_of_le zero_lt_one hp)
  have hmK j : MemLp (e j) (ENNReal.ofReal p) (volume.restrict K) :=
    (hmraw j).ae_eq (heq j).symm
  have hμ : volume.restrict Q ≤ volume.restrict K := Measure.restrict_mono_set volume hQK
  have hme j : MemLp (e j) (ENNReal.ofReal p) (volume.restrict Q) := (hmK j).mono_measure hμ
  have hte : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p)
      (volume.restrict Q)).toReal) atTop (𝓝 0) := by
    have htK : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p)
        (volume.restrict K)).toReal) atTop (𝓝 0) := by
      simpa only [eLpNorm_congr_ae (heq _)] using htraw
    apply squeeze_zero (fun j => ENNReal.toReal_nonneg) _ htK
    intro j
    exact ENNReal.toReal_mono (hmK j).eLpNorm_ne_top (eLpNorm_mono_measure _ hμ)
  let F := borelSource true u f
  let G := fun j => borelSource true u (f + e j)
  have hFp := borelSource_memLp hQ true u f hregQ.continuousOn hLp
  have hpert j : MemLp (fun P => max ((f + e j) P) 0) (ENNReal.ofReal p)
      (volume.restrict Q) := by
    have hmeas : Measurable (fun P : Q => (f + e j) P) :=
      hf.add ((hem j).comp measurable_subtype_coe)
    have hae : AEStronglyMeasurable (fun P => max ((f + e j) P) 0) (volume.restrict Q) := by
      have hQm : MeasurableSet Q := hQ.measurableSet
      have h1 : Measurable ((fun P => max ((f + e j) P) 0) ∘ ((↑) : Q → KineticPoint d)) :=
        hmeas.max measurable_const
      exact ((aemeasurable_restrict_iff_comap_subtype hQm).mpr h1.aemeasurable)
        |>.aestronglyMeasurable
    apply (hLp.add (hme j)).of_le hae
    filter_upwards with P
    change ‖max (f P + e j P) 0‖ ≤ ‖max (f P) 0 + e j P‖
    simp only [Real.norm_of_nonneg (le_max_right _ _),
      Real.norm_of_nonneg (add_nonneg (le_max_right _ _) (he0 j P))]
    exact max_le (by linarith only [le_max_left (f P) 0])
      (add_nonneg (le_max_right (f P) 0) (he0 j P))
  have hGp j := borelSource_memLp hQ true u (f + e j) hregQ.continuousOn (hpert j)
  have htG := borel_source_norm_tendsto hp F G e hFp hme
    (fun j => (hGp j).aestronglyMeasurable)
    (Filter.Eventually.of_forall (borelSource_nonneg true u f))
    (fun j => Filter.Eventually.of_forall (borelSource_nonneg true u (f + e j)))
    (fun j => Filter.Eventually.of_forall (he0 j))
    (fun j => Filter.Eventually.of_forall fun P => borelSource_error_le true u f P (he0 j P))
    hte
  have hineq j : ∀ P ∈ K, u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) +
      C₀ * r ^ alpha * (eLpNorm (G j) (ENNReal.ofReal p) (volume.restrict Q)).toReal := by
    apply hsmooth P₁ r hr (C j) (hC j).1 (fun P => (hC j).2.1 P.time P.position P.velocity)
      (fun P => (hC j).2.2 P.time P.position P.velocity) (f + e j) u
      (hf.add ((hem j).comp measurable_subtype_coe)) hcontK hregQ ?_ (hpert j)
    filter_upwards [hsub, ae_restrict_mem hQ.measurableSet] with P hsubP hP
    have heP : e j P = fullCoefficientError (C j) A H P := by
      simp only [e, fullCoefficientError, Hext, indicator_of_mem (hQK hP)]
    have hdiff := full_backwardOperator_sub (C j) A u P
    have hab := neg_le_abs (matrixContraction
      (fullKineticCoefficientAt (C j) P - fullKineticCoefficientAt A P) (H P))
    dsimp only [fullCoefficientError, H] at heP
    change backwardOperator (C j) u P ≤ f P + e j P
    rw [heP]
    linarith only [hdiff, hsubP, hab]
  intro P hP
  exact ge_of_tendsto
    (tendsto_const_nhds.add (tendsto_const_nhds.mul htG))
    (Filter.Eventually.of_forall fun j => hineq j P hP)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
