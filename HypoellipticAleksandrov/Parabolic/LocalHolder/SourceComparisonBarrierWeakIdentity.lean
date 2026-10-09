module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierForm
import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalSmoothObstacleWeakIdentity
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-! # Classical integration by parts for stationary barriers

The stationary form is the negative classical operator against every smooth spatial test.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set Dirichlet
open scoped ENNReal

private theorem integrableOn_mul_compact_test {d : ℕ} {Ω : Set (PDE.Vec d)}
    {f g : PDE.Vec d → ℝ} (hf : ContinuousOn f Ω) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    IntegrableOn (fun y => f y * g y) Ω := by
  have hK : IntegrableOn (fun y => f y * g y) (tsupport g) :=
    ((hf.mono hgs).mul hg.continuousOn).integrableOn_compact hgc
  exact ((integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f g).trans (subset_tsupport g))).mp hK).integrableOn

/-- The smooth stationary barrier form equals its negative classical operator integral. -/
theorem reverseTimeSpatialForm_stationary_barrier_weakIdentity {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T τ : ℝ) (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (q : PDE.H10Function Ω) (hq : ContDiff ℝ 2 q.toH1Function.toFun)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun y => A (T - τ) y i j) Ω)
    (hb : ∀ j, ContinuousOn (fun y => b (T - τ) y j) Ω)
    (hc : ContinuousOn (fun y => c (T - τ) y) Ω)
    (ψ : PDE.WeakTestFunction Ω) :
    reverseTimeSpatialForm hΩ T τ A b c (h10HilbertGraphOfH10Function hΩ q)
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
      ∫ y in Ω, (-scalarParabolicZeroOrderOperator A b c
        (fun z => q.toH1Function.toFun z.2) (T - τ, y)) * ψ y := by
  let ell : TimeVelocity d → ℝ := fun z => q.toH1Function.toFun z.2
  have hell : IsScalarC12On ell ({T - τ} ×ˢ Ω) :=
    isScalarC12On_of_contDiff_two (hq.comp contDiff_snd) _
  have htime (y : PDE.Vec d) : scalarTimeDerivative ell (T - τ, y) = 0 := by
    change deriv (fun _ : ℝ => q.toH1Function.toFun y) (T - τ) = 0
    exact deriv_const _ _
  have hgrad (y : PDE.Vec d) (j : Fin d) :
      scalarSpatialGradient ell (T - τ, y) j =
        PDE.classicalGradient q.toH1Function.toFun y j := rfl
  have hpair : Continuous (fun y : PDE.Vec d => (T - τ, y)) :=
    continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun y : PDE.Vec d => (T - τ, y)) Ω ({T - τ} ×ˢ Ω) :=
    fun _ hy => ⟨mem_singleton _, hy⟩
  have hg (j : Fin d) : ContinuousOn
      (fun y => scalarSpatialGradient ell (T - τ, y) j) Ω :=
    ((continuous_apply j).comp_continuousOn hell.continuousOn_scalarSpatialGradient).comp
      hpair.continuousOn hmaps
  have hd (j : Fin d) : ContinuousOn
      (fun y => reverseTimeDivergenceDrift T A b τ y j) Ω := by
    have hsum : ContinuousOn
        (fun y => ∑ i : Fin d, spatialPartial i (fun x => A (T - τ) x i j) y) Ω := by
      apply continuousOn_finsetSum
      intro i _
      exact ((ha i j).fderiv_of_isOpen hΩ (m := 0) (by norm_num)).clm_apply
        contDiffOn_const |>.continuousOn
    simpa only [reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeMap_apply,
      reverseTimeVectorCoefficient_apply, scalarSpatialCoefficientDivergence,
      spatialPartial, Pi.sub_apply, Pi.sub_def] using hsum.sub (hb j)
  have hp (i j : Fin d) : IntegrableOn (fun y => A (T - τ) y i j *
      scalarSpatialGradient ell (T - τ, y) j * ψ.partialDeriv i y) Ω := by
    apply integrableOn_mul_compact_test ((ha i j).continuousOn.mul (hg j))
    · have hψ : ContDiff ℝ 1 (ψ : PDE.Vec d → ℝ) := ψ.contDiff.of_le (by simp)
      exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    · exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i)
    · exact (tsupport_fderiv_apply_subset ℝ (PDE.basisVec i)).trans ψ.tsupport_subset
  have hdi (j : Fin d) : IntegrableOn (fun y =>
      reverseTimeDivergenceDrift T A b τ y j *
        scalarSpatialGradient ell (T - τ, y) j * ψ y) Ω :=
    integrableOn_mul_compact_test ((hd j).mul (hg j)) ψ.contDiff.continuous
      ψ.hasCompactSupport ψ.tsupport_subset
  have hci : IntegrableOn (fun y => c (T - τ) y * ell (T - τ, y) * ψ y) Ω :=
    integrableOn_mul_compact_test
      (hc.mul (hell.continuousOn.comp hpair.continuousOn hmaps))
      ψ.contDiff.continuous ψ.hasCompactSupport ψ.tsupport_subset
  have hid := integral_reverseTimeClassicalResidual_weakTest_eq_neg_operator hΩ T τ
    A b c ell ψ ha hell
    (integrableOn_reverseTimeClassicalRemainder_weakTest hΩ T τ A b c ell ψ ha hb hc hell)
  simp_rw [htime, neg_zero, zero_mul, zero_add] at hid
  rw [integral_sub (f := fun y =>
      (∑ i : Fin d, ∑ j : Fin d, A (T - τ) y i j *
        scalarSpatialGradient ell (T - τ, y) j * ψ.partialDeriv i y) +
      ∑ j : Fin d, reverseTimeDivergenceDrift T A b τ y j *
        scalarSpatialGradient ell (T - τ, y) j * ψ y)
    (g := fun y => c (T - τ) y * ell (T - τ, y) * ψ y)
    ((integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j))).add
      (integrable_finsetSum Finset.univ (fun j _ => hdi j))) hci,
    integral_add (f := fun y => ∑ i : Fin d, ∑ j : Fin d, A (T - τ) y i j *
      scalarSpatialGradient ell (T - τ, y) j * ψ.partialDeriv i y)
      (g := fun y => ∑ j : Fin d, reverseTimeDivergenceDrift T A b τ y j *
        scalarSpatialGradient ell (T - τ, y) j * ψ y)
      (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j)))
      (integrable_finsetSum Finset.univ (fun j _ => hdi j)),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j)),
    integral_finsetSum Finset.univ (fun j _ => hdi j)] at hid
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hp _ j), hgrad] at hid
  rw [reverseTimeSpatialForm_smooth_barrier_test hΩ T τ A b c q
    (hq.of_le (by norm_num)) ψ]
  exact hid

end HypoellipticAleksandrov.Parabolic.LocalHolder
