module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerError
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-! # Passing the coefficient limit on a fixed compact inner cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped MatrixOrder Matrix.Norms.Elementwise Topology ENNReal

/-- The coefficient limit preserves the complete source estimate on a fixed inner cylinder. -/
theorem borel_smooth_inner_limit {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmooth : BorelSmoothEstimate (d := d) lam Lam p alpha C₀ localised)
    (A : CoefficientField d) (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A)
    (C : ℕ → CoefficientField d)
    (hC : ∀ j, IsSmoothCoefficient (C j) ∧ IsSymmetricCoefficient (C j) ∧
      HasLowerEllipticity lam (C j) ∧ HasUpperEllipticity Lam (C j))
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × PDE.Vec d)),
      Tendsto (fun j => coefficientAt (C j) z) atTop (𝓝 (coefficientAt A z)))
    {D : Set (KineticPoint d)} (u f : KineticPoint d → ℝ) (hreg : IsKineticC112On u D)
    (P₁ : KineticPoint d) (r : ℝ) (hr : 0 < r)
    (hK : IsCompact (closure (backwardCylinder P₁ r)))
    (hKD : closure (backwardCylinder P₁ r) ⊆ D) (hf : Measurable f)
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
  classical
  let Q := backwardCylinder P₁ r
  let K := closure Q
  let H := kineticVelocityHessian u
  have hH : ContinuousOn H K := hreg.continuousOn_kineticVelocityHessian.mono hKD
  let Hext := K.indicator H
  let e := fun j => borelCoefficientError (C j) A Hext
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
  have hproj : Measurable (fun P : KineticPoint d => (P.time,P.velocity)) :=
    (continuous_time.prodMk continuous_velocity).measurable
  have hA : Measurable (fun P : KineticPoint d => A P.time P.velocity) := hBorel.comp hproj
  have hem j : Measurable (e j) := by
    have hCs : Continuous (coefficientAt (C j)) := (hC j).1.continuous
    have hs : Measurable (fun P : KineticPoint d =>
        matrixContraction (C j P.time P.velocity - A P.time P.velocity) (Hext P)) := by
      unfold matrixContraction
      exact Finset.measurable_fun_sum _ fun i _ =>
        Finset.measurable_fun_sum _ fun k _ =>
          (((hCs.measurable.comp hproj).eval.eval).sub hA.eval.eval).mul hHext.eval.eval
    exact continuous_abs.measurable.comp hs
  have heq j : e j =ᵐ[volume.restrict K] borelCoefficientError (C j) A H := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
    simp only [e,borelCoefficientError,Hext,indicator_of_mem hP]
  obtain ⟨_,hmraw,htraw⟩ := borel_inner_error hlam hLam A hBorel hlo hhi C hC hc K hK H hH
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
  let F := borelSource localised u f
  let G := fun j => borelSource localised u (f + e j)
  have hFp := borelSource_memLp hQ localised u f hregQ.continuousOn hLp
  have hpert j : MemLp (fun P => max ((f + e j) P) 0) (ENNReal.ofReal p)
      (volume.restrict Q) := by
    apply (hLp.add (hme j)).of_le ((hf.add (hem j)).sup measurable_const).aestronglyMeasurable
    filter_upwards with P
    change ‖max (f P + e j P) 0‖ ≤ ‖max (f P) 0 + e j P‖
    simp only [Real.norm_of_nonneg (le_max_right _ _),
      Real.norm_of_nonneg (add_nonneg (le_max_right _ _) (he0 j P))]
    exact max_le (by linarith only [le_max_left (f P) 0])
      (add_nonneg (le_max_right (f P) 0) (he0 j P))
  have hGp j := borelSource_memLp hQ localised u (f + e j) hregQ.continuousOn (hpert j)
  have htG := borel_source_norm_tendsto hp F G e hFp hme
    (fun j => (hGp j).aestronglyMeasurable)
    (Filter.Eventually.of_forall (borelSource_nonneg localised u f))
    (fun j => Filter.Eventually.of_forall (borelSource_nonneg localised u (f + e j)))
    (fun j => Filter.Eventually.of_forall (he0 j))
    (fun j => Filter.Eventually.of_forall fun P => borelSource_error_le localised u f P (he0 j P))
    hte
  have hineq j : ∀ P ∈ K, u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) +
      C₀ * r ^ alpha * (eLpNorm (G j) (ENNReal.ofReal p) (volume.restrict Q)).toReal := by
    apply hsmooth (C j) (hC j).1 (hC j).2.1 (hC j).2.2.1 (hC j).2.2.2
      P₁ r hr u (f + e j) hcontK hregQ (hf.add (hem j)) (hpert j)
    filter_upwards [hsub,ae_restrict_mem hQ.measurableSet] with P hsubP hP
    have heP : e j P = borelCoefficientError (C j) A H P := by
      simp only [e,borelCoefficientError,Hext,indicator_of_mem (hQK hP)]
    have hdiff := borel_backwardOperator_sub (C j) A u P
    have hab := neg_le_abs (matrixContraction
      (C j P.time P.velocity - A P.time P.velocity) (H P))
    dsimp only [borelCoefficientError,H] at heP
    change backwardOperatorOfTimeVelocityCoefficient (C j) u P ≤ f P + e j P
    rw [heP]
    linarith only [hdiff,hsubP,hab]
  intro P hP
  exact ge_of_tendsto
    (tendsto_const_nhds.add (tendsto_const_nhds.mul htG))
    (Filter.Eventually.of_forall fun j => hineq j P hP)

end HypoellipticAleksandrov.KineticAleksandrov
