module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarBorelInnerError
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-! # Passing the coefficient limit on a fixed compact inner cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The coefficient limit preserves the complete source estimate on a fixed inner cylinder. -/
theorem scalar_borel_smooth_inner_limit (lam Lam : ℝ) (hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (p : ℝ) (hp : 1 ≤ p) (alpha C₀ : ℝ) (localised : Bool)
    (hsmooth : ∀ a : ℝ → ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry a) →
      (∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (P₀ : Point) (R : ℝ), 0 < R → ∀ u f : Point → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R), autonomousScalarOperator a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) + C₀ * R ^ alpha *
        (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R))).toReal)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (C : ℕ → ℝ → ℝ → ℝ)
    (hC : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
      ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam)
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2)))
    {D : Set (Point)} (u f : Point → ℝ) (hreg : IsKineticC112On u D)
    (P₁ : Point) (r : ℝ) (hr : 0 < r)
    (hK : IsCompact (closure (backwardCylinder P₁ r)))
    (hKD : closure (backwardCylinder P₁ r) ⊆ D) (hf : Measurable f)
    (hLp : MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₁ r)))
    (hsub : ∀ᵐ P ∂(volume.restrict (backwardCylinder P₁ r)),
      autonomousScalarOperator a u P ≤ f P) :
    ∀ P ∈ closure (backwardCylinder P₁ r), u P ≤
      sSup ((fun P => max (u P) 0) '' kineticBoundary P₁ r) + C₀ * r ^ alpha *
      (eLpNorm (borelSource localised u f) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₁ r))).toReal := by
  classical
  let Q := backwardCylinder P₁ r
  let K := closure Q
  let H : Point → ℝ := fun P => kineticVelocityHessian u P 0 0
  have hH : ContinuousOn H K :=
    (continuous_apply 0).comp_continuousOn
      ((continuous_apply 0).comp_continuousOn
        (hreg.continuousOn_kineticVelocityHessian.mono hKD))
  let Hext := K.indicator H
  let e := fun j => scalarBorelError (C j) a Hext
  have he0 j P : 0 ≤ e j P := abs_nonneg _
  have hQ : IsOpen Q := isOpen_backwardCylinder P₁ r hr
  have hQK : Q ⊆ K := subset_closure
  have hregQ := comparison_regular_mono hreg (hQK.trans hKD)
  have hcontK := hreg.continuousOn.mono hKD
  have hHext : Measurable Hext :=
    hH.measurable_piecewise continuousOn_const hK.measurableSet
  have hproj : Measurable (fun P : Point => (P.position 0, P.velocity 0)) :=
    (((continuous_apply 0).comp continuous_position).prodMk
      ((continuous_apply 0).comp continuous_velocity)).measurable
  have hAm : Measurable (fun P : Point => a (P.position 0) (P.velocity 0)) := ha.comp hproj
  have hem j : Measurable (e j) :=
    continuous_abs.measurable.comp
      ((((hC j).1.continuous.measurable.comp hproj).sub hAm).mul hHext)
  have heq j : e j =ᵐ[volume.restrict K] scalarBorelError (C j) a H := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
    simp only [e,scalarBorelError,Hext,indicator_of_mem hP]
  obtain ⟨_,hmraw,htraw⟩ := scalar_borel_inner_error hlam a ha hb C hC hc K hK H hH
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
    apply hsmooth (C j) (hC j).1 (hC j).2
      P₁ r hr u (f + e j) hcontK hregQ (hf.add (hem j)) (hpert j)
    filter_upwards [hsub,ae_restrict_mem hQ.measurableSet] with P hsubP hP
    have heP : e j P = scalarBorelError (C j) a H P := by
      simp only [e,scalarBorelError,Hext,indicator_of_mem (hQK hP)]
    have hdiff := scalar_borel_operator_sub (C j) a u P
    have hab := neg_le_abs ((C j (P.position 0) (P.velocity 0) -
      a (P.position 0) (P.velocity 0)) * H P)
    dsimp only [scalarBorelError, H] at heP
    change autonomousScalarOperator (C j) u P ≤ f P + e j P
    rw [heP]
    linarith only [hdiff, hsubP, hab]
  intro P hP
  exact ge_of_tendsto
    (tendsto_const_nhds.add (tendsto_const_nhds.mul htG))
    (Filter.Eventually.of_forall fun j => hineq j P hP)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
