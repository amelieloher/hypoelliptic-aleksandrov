module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyConstant
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierWeakIdentity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothNeighborhoodSpatialSlices
import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet

/-! # Stationary smooth barriers as literal variational solutions

Density extends the classical identity to every H10 test in the energy equation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

/-- A smooth stationary zero-boundary barrier solves its literal variational source equation. -/
theorem stationarySourceCurve_withDrift {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    (hA : IsSmoothCoefficient A) (F : TimeVelocity d → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (q : PDE.H10Function Ω)
    (hq : ContDiff ℝ 2 q.toH1Function.toFun)
    (heq : ∀ z ∈ Icc a T ×ˢ Ω,
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
        (fun z => q.toH1Function.toFun z.2) z = F z) :
    IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
      (valueCLM hΩ (h10HilbertGraphOfH10Function hΩ q))
      (stationarySourceCurve hΩ (T - a) (h10HilbertGraphOfH10Function hΩ q)) 0
      (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT)
        (h10HilbertGraphOfH10Function hΩ q)) := by
  let Q := h10HilbertGraphOfH10Function hΩ q
  let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  let hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
  let hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  let hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  constructor
  · change reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
      (stationarySourceCurve hΩ (T - a) Q) 0
      (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q)
      ⟨0, ⟨le_rfl, (sub_pos.mpr haT).le⟩⟩ = valueCLM hΩ Q
    rw [stationarySourceCurve_hilbertRepresentative]
    rfl
  · filter_upwards [stationarySourceCurve_ae hΩ (T - a) Q,
      Lp.coeFn_zero (H10HilbertGraphDual hΩ) 2 (reverseTimeVolume (T - a))]
      with τ hqτ hgτ
    intro hτ v
    rw [hqτ, hgτ]
    change 0 + reverseTimeSpatialForm hΩ T τ A b (fun _ _ => 0) Q v = _
    rw [zero_add]
    have hτc : τ ∈ Icc 0 (T - a) := ⟨hτ.1.le, hτ.2.le⟩
    let fτ := reverseTimeSourceSlice T τ (fun t y => F (t, y))
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
        (fun t y => F (t, y)) hFs τ hτc)
    let L := reverseTimeSpatialFormOperator a T haT hΩ hΩb A
      b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q
    let R := reverseTimeSourceFunctional hΩ fτ
    have hLR : L = R := by
      apply ContinuousLinearMap.coeFn_injective
      apply Continuous.ext_on
        (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
        L.continuous R.continuous
      rintro _ ⟨ψ, rfl⟩
      change L (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
        R (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)
      have ha : ∀ i j, ContDiffOn ℝ 1 (fun y => A (T - τ) y i j) Ω := by
        intro i j
        exact contDiffOn_one_coefficientEntry_spatialSlice_of_smoothOnNeighborhood
          a T (T - τ) A hAs (by constructor <;> linarith [hτ.1, hτ.2]) i j
      rw [show L _ = reverseTimeSpatialForm hΩ T τ A b
        (fun _ _ => 0) Q _ from reverseTimeSpatialFormOperator_apply
          a T haT hΩ hΩb A b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q _,
        reverseTimeSpatialForm_stationary_barrier_weakIdentity hΩ T τ A
          b (fun _ _ => 0) q hq ha
          (continuousOn_vectorEntry_spatialSlice_of_smoothOnNeighborhood
            a T (T - τ) b hbs (by constructor <;> linarith [hτ.1, hτ.2])) continuousOn_const ψ]
      change _ = reverseTimeSourceFunctional hΩ fτ _
      rw [reverseTimeSourceFunctional_apply, L2.inner_def, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [coeFn_reverseTimeSourceSlice T τ (fun t y => F (t, y))
        (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
          (fun t y => F (t, y)) hFs τ hτc),
        ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ,
        ae_restrict_mem hΩ.measurableSet] with y hFy hψ hy
      rw [hFy, hψ, heq (T - τ, y)
        ⟨by constructor <;> linarith [hτ.1, hτ.2], hy⟩]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [← reverseTimeSpatialFormOperator_apply a T haT hΩ hΩb A
      b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q v]
    exact congrArg (fun D : H10HilbertGraphDual hΩ => D v) hLR

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
