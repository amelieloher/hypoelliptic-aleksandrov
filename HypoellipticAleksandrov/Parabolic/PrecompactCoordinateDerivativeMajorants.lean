module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz
public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import Mathlib.Topology.Separation.Regular

/-!
# Coordinate derivative majorants on precompact neighborhoods

This file bounds a finite-order family of coordinate derivatives on the compact closure of one
common precompact neighborhood.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

private theorem order_le_parabolicWeight {d : ℕ}
    (beta : TimeVelocityMultiIndex d) :
    beta.order ≤ beta.parabolicWeight := by
  simp only [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight]
  omega

private theorem continuousOn_coordinateIteratedFDeriv
    {d M : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (f : TimeVelocity d → ℝ) (hf : ContDiffOn ℝ M f U)
    (alpha : ParabolicDerivativeIndex d M) :
    ContinuousOn
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f) U := by
  intro z hz
  have horder : alpha.1.order ≤ M :=
    (order_le_parabolicWeight alpha.1).trans alpha.2
  have hdiff : ContDiffAt ℝ M f z := hf.contDiffAt (hU.mem_nhds hz)
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hiter := hdiff.iteratedFDeriv_right
    (m := 0) (i := alpha.1.coordinateList.length) (by simpa)
  exact ((contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis
      (alpha.1.coordinateList.get i)))).clm_apply hiter).continuousAt.continuousWithinAt

/-- A compact subset of an open time--velocity set has one precompact open
neighborhood carrying nonnegative finite-order derivative majorants for an
arbitrary indexed scalar family. -/
theorem exists_precompactOpen_coordinateIteratedFDeriv_majorants
    {d M : ℕ} {ι : Type*}
    {U K : Set (TimeVelocity d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : ι → TimeVelocity d → ℝ)
    (hq : ∀ i, ContDiffOn ℝ M (q i) U) :
    ∃ (V : Set (TimeVelocity d))
      (B : ι → ParabolicDerivativeIndex d M → ℝ),
      IsOpen V ∧
      K ⊆ V ∧
      closure V ⊆ U ∧
      IsCompact (closure V) ∧
      (∀ i alpha, 0 ≤ B i alpha) ∧
      ∀ i alpha z, z ∈ closure V →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 (q i) z| ≤
          B i alpha := by
  classical
  obtain ⟨V, hVopen, hKV, hVU, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hbound : ∀ (i : ι) (alpha : ParabolicDerivativeIndex d M),
      ∃ C : ℝ, ∀ z ∈ closure V,
        ‖TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 (q i) z‖ ≤ C := by
    intro i alpha
    exact hVcompact.exists_bound_of_continuousOn
      ((continuousOn_coordinateIteratedFDeriv hU (q i) (hq i) alpha).mono hVU)
  choose C hC using hbound
  refine ⟨V, fun i alpha ↦ max 0 (C i alpha), hVopen, hKV, hVU, hVcompact, ?_, ?_⟩
  · exact fun i alpha ↦ le_max_left 0 (C i alpha)
  · intro i alpha z hz
    rw [← Real.norm_eq_abs]
    exact (hC i alpha z hz).trans (le_max_right 0 (C i alpha))

end HypoellipticAleksandrov.Parabolic
