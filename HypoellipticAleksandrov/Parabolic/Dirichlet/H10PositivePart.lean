module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenPositivePartApproximation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10LevelSet
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Positive parts in spatial `H¹₀`

This module constructs the positive part of an arbitrary spatial `H¹₀`
graph point on an open set, identifies its weak gradient, and records the
sharp contractions of its value and gradient components.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private def h1FunctionOfH10
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) : PDE.H1Function Ω where
  toFun := valueCLM hΩ u
  grad := fun x => (gradientCLM hΩ u x).ofLp
  memL2 := Lp.memLp _
  gradMemL2 := fun i => (Lp.memLp (gradientCLM hΩ u)).eval_piLp i
  hasWeakGradient := by
    intro i
    rw [PDE.hasWeakPartialDerivOn_iff_forall_testFunction]
    intro φ
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [PDE.weakGradientConstraint_apply_eq_integral, PDE.H1HilbertGraph.toH1Graph,
      PDE.H1HilbertGraph.value, PDE.H1HilbertGraph.gradient, PDE.volumeOn,
      WithLp.prodContinuousLinearEquiv_apply, WithLp.fst, WithLp.snd,
      valueCLM_apply, gradientCLM_apply] using
      PDE.W1pGraph.constraint_eq_zero
        (PDE.H1HilbertGraph.toH1Graph
          (u : PDE.H1HilbertGraph Ω)) i φ

private theorem h1FunctionOfH10_hasSupportedSmoothApproximation
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    Nonempty (h1FunctionOfH10 hΩ u).SupportedSmoothApproximation := by
  let ug := h10HilbertGraphContinuousLinearEquiv hΩ u
  rcases PDE.H10Graph.exists_tendsto_smooth hΩ ug with ⟨φ, hφ⟩
  let w := h1FunctionOfH10 hΩ u
  have hvalue : Tendsto
      (fun n => (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.1)
      atTop (𝓝 (valueCLM hΩ u)) := by
    simpa only [ug, h10HilbertGraphContinuousLinearEquiv, valueCLM_apply,
      h1HilbertGraphContinuousLinearEquiv_apply, Function.comp_def,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans, ContinuousLinearEquiv.ofEq,
      ContinuousLinearEquiv.ofSubmodule'_apply, PDE.H1HilbertGraph.value,
      PDE.H1HilbertGraph.gradient, PDE.H1HilbertGraph.toH1Graph] using!
      ((continuous_fst.comp continuous_subtype_val).tendsto _ |>.comp hφ)
  have hgradient : Tendsto
      (fun n => (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2)
      atTop (𝓝 (gradientCLM hΩ u)) := by
    simpa only [ug, h10HilbertGraphContinuousLinearEquiv, gradientCLM_apply,
      h1HilbertGraphContinuousLinearEquiv_apply, Function.comp_def,
      ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans, ContinuousLinearEquiv.ofEq,
      ContinuousLinearEquiv.ofSubmodule'_apply, PDE.H1HilbertGraph.value,
      PDE.H1HilbertGraph.gradient, PDE.H1HilbertGraph.toH1Graph] using!
      ((continuous_snd.comp continuous_subtype_val).tendsto _ |>.comp hφ)
  refine ⟨{
    approx := fun n => (φ n).toFun
    approx_smooth := fun n => (φ n).contDiff
    approx_hasCompactSupport := fun n => (φ n).hasCompactSupport
    approx_tsupport_subset := fun n => (φ n).tsupport_subset
    tendsto_value := ?_
    tendsto_grad := ?_ }⟩
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (φ n).toFun) (fun n => (φ n).memLp_toFun (2 : ℝ≥0∞))
      w.toFun w.memL2).mp (by
        simpa only [w, h1FunctionOfH10,
          PDE.smoothCompactlySupportedH1Graph,
          PDE.smoothCompactlySupportedW1pGraph,
          PDE.W1pFunction.toW1pGraph, PDE.W1pFunction.ofContDiff,
          Lp.toLp_coeFn, PDE.w1pGraphOfRepresentatives,
          PDE.weakGradientLpPairOfRepresentatives] using! hvalue)
  · intro i
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i))
      (fun n => (φ n).memLp_partialDeriv i (2 : ℝ≥0∞))
      (fun x => w.grad x i) (w.gradMemL2 i)).mp
    have heval := (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i).continuous.tendsto _ |>.comp hgradient
    have hseq : ∀ n,
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2 =
          ((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
            (fun x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i)) := by
      intro n
      apply Lp.ext
      filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
          (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2,
        PDE.W1pFunction.coeFn_toW1pGraph_snd
          (PDE.W1pFunction.ofContDiff hΩ
            ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2),
        ((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).coeFn_toLp] with x hc hg ht
      have hg' :
          ⇑(PDE.smoothCompactlySupportedH1Graph hΩ (φ n)).1.2 x =
            PDE.toHilbertVecField
              (PDE.W1pFunction.ofContDiff hΩ
                ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport 2).grad x := by
        simpa only [PDE.smoothCompactlySupportedH1Graph,
          PDE.smoothCompactlySupportedW1pGraph] using hg
      have ht' :
          ⇑(((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
            (fun x => (fderiv ℝ (φ n).toFun x) (PDE.basisVec i))) x =
            (fderiv ℝ (φ n).toFun x) (PDE.basisVec i) := by
        change ⇑(((φ n).memLp_partialDeriv i (2 : ℝ≥0∞)).toLp
          ((φ n).partialDeriv i)) x = _
        exact ht
      rw [hc, hg', ht']
      rfl
    have hlim : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ u) =
        (w.gradMemL2 i).toLp (fun x => w.grad x i) := by
      apply Lp.ext
      filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i (gradientCLM hΩ u),
        (w.gradMemL2 i).coeFn_toLp] with x hc ht
      rw [hc, ht]
      rfl
    rw [← hlim]
    simpa only [Function.comp_def, hseq] using heval

private theorem exists_positivePart_data
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ∃ v : H10HilbertGraph hΩ,
      valueCLM hΩ v = MeasureTheory.Lp.posPart (valueCLM hΩ u) ∧
      ∀ᵐ x ∂(PDE.volumeOn Ω),
        gradientCLM hΩ v x =
          {y | 0 < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  let w := h1FunctionOfH10 hΩ u
  obtain ⟨z, hzValue, hzGrad, hzApprox⟩ :=
    PDE.H1Function.exists_positivePart_supportedSmoothApproximation
      (Classical.choice (h1FunctionOfH10_hasSupportedSmoothApproximation hΩ u))
      (by
        filter_upwards [gradientCLM_ae_zero_on_level_set hΩ u 0] with x hx
        intro hzero
        apply (WithLp.ofLp_eq_zero 2).mpr
        exact hx hzero)
  let zg : PDE.H10Graph hΩ :=
    ⟨z.toW1pFunction.toW1pGraph,
      z.mem_h10Graph_of_supportedSmoothApproximation hΩ (Classical.choice hzApprox)⟩
  let v := (h10HilbertGraphContinuousLinearEquiv hΩ).symm zg
  refine ⟨v, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [PDE.W1pFunction.coeFn_toW1pGraph_fst z.toW1pFunction,
      Lp.coeFn_posPart (valueCLM hΩ u)] with x hx hpos
    change (zg : PDE.H1Graph Ω).1.1 x =
      MeasureTheory.Lp.posPart (valueCLM hΩ u) x
    rw [hx]
    change z.toFun x = _
    rw [hzValue, hpos]
    rfl
  · filter_upwards [PDE.W1pFunction.coeFn_toW1pGraph_snd z.toW1pFunction] with x hx
    change (zg : PDE.H1Graph Ω).1.2 x = _
    rw [hx]
    ext i
    change z.grad x i = _
    rw [hzGrad]
    simp only [h1FunctionOfH10, indicator_apply]
    split <;> rfl

/-- The positive part has a unique spatial `H¹₀` graph representative. -/
theorem exists_unique_h10PositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ∃! v : H10HilbertGraph hΩ,
      valueCLM hΩ v = MeasureTheory.Lp.posPart (valueCLM hΩ u) := by
  obtain ⟨v, hv, _⟩ := exists_positivePart_data hΩ u
  exact ⟨v, hv, fun z hz => valueCLM_injective hΩ (hz.trans hv.symm)⟩

/-- The canonical positive part in the Hilbert realization of spatial `H¹₀`. -/
noncomputable def h10PositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) : H10HilbertGraph hΩ :=
  Classical.choose (exists_unique_h10PositivePart hΩ u)

/-- The value component of the canonical `H¹₀` positive part is the
`L²` positive part of the original value component. -/
@[simp]
theorem valueCLM_h10PositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    valueCLM hΩ (h10PositivePart hΩ u) =
      MeasureTheory.Lp.posPart (valueCLM hΩ u) :=
  (Classical.choose_spec (exists_unique_h10PositivePart hΩ u)).1

/-- The weak gradient of the positive part is the original gradient on its
strictly positive set and zero elsewhere. -/
theorem gradientCLM_h10PositivePart
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ∀ᵐ x ∂(PDE.volumeOn Ω),
      gradientCLM hΩ (h10PositivePart hΩ u) x =
        {y | 0 < valueCLM hΩ u y}.indicator (gradientCLM hΩ u) x := by
  obtain ⟨v, hv, hvGrad⟩ := exists_positivePart_data hΩ u
  have heq : h10PositivePart hΩ u = v :=
    valueCLM_injective hΩ (valueCLM_h10PositivePart hΩ u |>.trans hv.symm)
  simpa only [heq] using hvGrad

/-- Taking the positive part contracts the value `L²` norm. -/
theorem norm_valueCLM_h10PositivePart_le
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ (h10PositivePart hΩ u)‖ ≤ ‖valueCLM hΩ u‖ := by
  rw [valueCLM_h10PositivePart]
  change ‖Lp.lipschitzWith_pos_part.compLp (max_eq_right le_rfl) (valueCLM hΩ u)‖ ≤ _
  simpa using Lp.lipschitzWith_pos_part.norm_compLp_le
    (max_eq_right le_rfl) (valueCLM hΩ u)

/-- Taking the positive part contracts the weak-gradient `L²` norm. -/
theorem norm_gradientCLM_h10PositivePart_le
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ‖gradientCLM hΩ (h10PositivePart hΩ u)‖ ≤ ‖gradientCLM hΩ u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  calc
    eLpNorm (gradientCLM hΩ (h10PositivePart hΩ u)) 2 (PDE.volumeOn Ω) =
        eLpNorm ({y | 0 < valueCLM hΩ u y}.indicator
          (gradientCLM hΩ u)) 2 (PDE.volumeOn Ω) :=
      eLpNorm_congr_ae (gradientCLM_h10PositivePart hΩ u)
    _ ≤ eLpNorm (gradientCLM hΩ u) 2 (PDE.volumeOn Ω) :=
      eLpNorm_indicator_le _
        (measurableSet_lt measurable_const (Lp.stronglyMeasurable (valueCLM hΩ u)).measurable)

end HypoellipticAleksandrov.Parabolic.Dirichlet
