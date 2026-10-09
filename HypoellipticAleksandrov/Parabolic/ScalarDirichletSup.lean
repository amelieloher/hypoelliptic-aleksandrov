module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Supremum envelopes for supplied scalar backward Dirichlet solutions

This module derives sharp pointwise and closed-cylinder envelopes for a
supplied classical backward Dirichlet solution.  The proof compares the
solution and its negative with the same affine-time barrier; it constructs no
solution and does not introduce a set supremum or coefficient norm.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

/-- The affine-time barrier used for the terminal, lateral, and source envelopes. -/
private def sourceBarrier {n : ℕ} (Phi H Fmax r1 : ℝ) : TimeVelocity n → ℝ :=
  fun z => Phi + H + (r1 - z.1) * Fmax

private theorem sourceBarrier_continuous {n : ℕ} (Phi H Fmax r1 : ℝ) :
    Continuous (sourceBarrier (n := n) Phi H Fmax r1) := by
  exact (continuous_const.add continuous_const).add
    ((continuous_const.sub continuous_fst).mul continuous_const)

private theorem scalarTimeDerivative_sourceBarrier {n : ℕ} (Phi H Fmax r1 : ℝ)
    (z : TimeVelocity n) :
    scalarTimeDerivative (sourceBarrier Phi H Fmax r1) z = -Fmax := by
  have hderiv : HasDerivAt
      (fun r : ℝ => sourceBarrier Phi H Fmax r1 (r, z.2)) (-Fmax) z.1 := by
    change HasDerivAt (fun r : ℝ => Phi + H + (r1 - r) * Fmax) (-Fmax) z.1
    convert (hasDerivAt_const (x := z.1) (c := Phi + H)).add
      (((hasDerivAt_const (x := z.1) (c := r1)).sub (hasDerivAt_id z.1)).mul
        (hasDerivAt_const (x := z.1) (c := Fmax))) using 1
    all_goals try funext r
    all_goals try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
    all_goals ring
  exact hderiv.deriv

private theorem scalarSpatialGradient_sourceBarrier {n : ℕ} (Phi H Fmax r1 : ℝ)
    (z : TimeVelocity n) :
    scalarSpatialGradient (sourceBarrier Phi H Fmax r1) z = 0 := by
  ext i
  change fderiv ℝ
      (Function.const (PDE.Vec n) (Phi + H + (r1 - z.1) * Fmax)) z.2
      (PDE.basisVec i) = 0
  rw [fderiv_const]
  rfl

private theorem scalarSpatialHessian_sourceBarrier {n : ℕ} (Phi H Fmax r1 : ℝ)
    (z : TimeVelocity n) :
    scalarSpatialHessian (sourceBarrier Phi H Fmax r1) z = 0 := by
  have hgradient : (fun y : PDE.Vec n =>
      PDE.classicalGradient
        (fun w : PDE.Vec n => sourceBarrier Phi H Fmax r1 (z.1, w)) y) =
      fun _ => 0 := by
    funext y
    ext j
    change fderiv ℝ
        (Function.const (PDE.Vec n) (Phi + H + (r1 - z.1) * Fmax)) y
        (PDE.basisVec j) = 0
    rw [fderiv_const]
    rfl
  ext i j
  unfold scalarSpatialHessian
  rw [hgradient]
  simp

private theorem isScalarC12On_sourceBarrier {n : ℕ} {D : Set (TimeVelocity n)}
    (Phi H Fmax r1 : ℝ) :
    IsScalarC12On (sourceBarrier Phi H Fmax r1) D := by
  refine ⟨(sourceBarrier_continuous Phi H Fmax r1).continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z _
    exact (show HasDerivAt (fun r : ℝ => sourceBarrier Phi H Fmax r1 (r, z.2))
      (-Fmax) z.1 by
      change HasDerivAt (fun r : ℝ => Phi + H + (r1 - r) * Fmax) (-Fmax) z.1
      convert (hasDerivAt_const (x := z.1) (c := Phi + H)).add
        (((hasDerivAt_const (x := z.1) (c := r1)).sub (hasDerivAt_id z.1)).mul
          (hasDerivAt_const (x := z.1) (c := Fmax))) using 1
      all_goals try funext r
      all_goals try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
      all_goals ring).differentiableAt
  · intro z _
    change ContDiffAt ℝ 2
      (Function.const (PDE.Vec n) (Phi + H + (r1 - z.1) * Fmax)) z.2
    exact contDiffAt_const
  · refine (continuous_const : Continuous (fun _ : TimeVelocity n => -Fmax)).continuousOn.congr
      ?_
    intro z _
    exact scalarTimeDerivative_sourceBarrier Phi H Fmax r1 z
  · refine (continuous_zero : Continuous
      (fun _ : TimeVelocity n => (0 : PDE.Vec n))).continuousOn.congr ?_
    intro z _
    exact scalarSpatialGradient_sourceBarrier Phi H Fmax r1 z
  · refine (continuous_zero : Continuous
      (fun _ : TimeVelocity n => (0 : PDE.Mat n))).continuousOn.congr ?_
    intro z _
    exact scalarSpatialHessian_sourceBarrier Phi H Fmax r1 z

private theorem scalarParabolicZeroOrderOperator_sourceBarrier {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) (Phi H Fmax r1 : ℝ) (z : TimeVelocity n) :
    scalarParabolicZeroOrderOperator a b c (sourceBarrier Phi H Fmax r1) z =
      -Fmax + c z.1 z.2 * sourceBarrier Phi H Fmax r1 z := by
  rw [scalarParabolicZeroOrderOperator_apply,
    scalarTimeDerivative_sourceBarrier, scalarSpatialHessian_sourceBarrier,
    scalarSpatialGradient_sourceBarrier]
  simp only [HypoellipticAleksandrov.matrixContraction_zero_right, PDE.vecDot,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]

private theorem isClassicalBackwardDirichletSolution_sourceBarrier {n : ℕ}
    {Omega : Set (PDE.Vec n)} {r0 r1 : ℝ} (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    (Phi H Fmax : ℝ) :
    IsClassicalBackwardDirichletSolution r0 r1 Omega a b c
      (fun r y => -Fmax + c r y * sourceBarrier Phi H Fmax r1 (r, y))
      (fun _ => Phi + H) (sourceBarrier Phi H Fmax r1)
      (sourceBarrier Phi H Fmax r1) := by
  refine ⟨(sourceBarrier_continuous Phi H Fmax r1).continuousOn,
    isScalarC12On_sourceBarrier Phi H Fmax r1, ?_, ?_, ?_⟩
  · intro z _
    exact scalarParabolicZeroOrderOperator_sourceBarrier a b c Phi H Fmax r1 z
  · intro y _
    dsimp [sourceBarrier]
    ring
  · intro z _
    rfl

private theorem sourceBarrier_nonneg_on_closedCylinder {n : ℕ}
    {Omega : Set (PDE.Vec n)} {r0 r1 : ℝ} {Phi H Fmax : ℝ}
    (hPhiNonneg : 0 ≤ Phi) (hHNonneg : 0 ≤ H) (hFmaxNonneg : 0 ≤ Fmax)
    {z : TimeVelocity n} (hz : z ∈ scalarParabolicClosedCylinder r0 r1 Omega) :
    0 ≤ sourceBarrier Phi H Fmax r1 z := by
  rcases hz with ⟨⟨hz0, hz1⟩, _⟩
  dsimp [sourceBarrier]
  exact add_nonneg (add_nonneg hPhiNonneg hHNonneg)
    (mul_nonneg (sub_nonneg.mpr hz1) hFmaxNonneg)

private theorem scalarTimeDerivative_neg {n : ℕ} {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) {z : TimeVelocity n}
    (hz : z ∈ D) :
    scalarTimeDerivative (fun q => -u q) z = -scalarTimeDerivative u z := by
  exact (hu.timeSlice_hasDerivAt hz).neg.deriv

private theorem scalarSpatialGradient_neg {n : ℕ} (u : TimeVelocity n → ℝ)
    (z : TimeVelocity n) :
    scalarSpatialGradient (fun q => -u q) z = -scalarSpatialGradient u z := by
  ext i
  change fderiv ℝ (-(fun y : PDE.Vec n => u (z.1, y))) z.2 (PDE.basisVec i) = _
  rw [fderiv_neg]
  rfl

private theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    intro j
    exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt
  change (fderiv ℝ (fun y : PDE.Vec n => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi hdiff]
  have hj := (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv
  have hjApply := congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hj
  simpa [ContinuousLinearMap.flip_apply] using hjApply

private theorem scalarSpatialHessian_neg {n : ℕ} {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) {z : TimeVelocity n}
    (hz : z ∈ D) :
    scalarSpatialHessian (fun q => -u q) z = -scalarSpatialHessian u z := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hfirst : fderiv ℝ (fun y => -g y) =ᶠ[𝓝 z.2]
      fun y => -fderiv ℝ g y := by
    filter_upwards [(hu.spatialSlice_contDiffAt hz).eventually (by norm_num)] with y hy
    exact fderiv_neg
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hsecondNeg : fderiv ℝ (fderiv ℝ (fun y => -g y)) z.2 =
      -fderiv ℝ (fderiv ℝ g) z.2 := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => -g y)) z.2 =
          fderiv ℝ (fun y => -fderiv ℝ g y) z.2 := hfirst.fderiv_eq
      _ = -fderiv ℝ (fderiv ℝ g) z.2 := fderiv_neg
  ext i j
  rw [Matrix.neg_apply]
  rw [scalarSpatialHessian_apply_eq_sndFDeriv
      ((hu.spatialSlice_contDiffAt hz).neg) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz) i j]
  simpa [g] using congrArg (fun L : PDE.Vec n →L[ℝ] PDE.Vec n →L[ℝ] ℝ =>
    L (PDE.basisVec i) (PDE.basisVec j)) hsecondNeg

private theorem isScalarC12On_neg {n : ℕ} {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) :
    IsScalarC12On (fun q => -u q) D := by
  refine ⟨hu.continuousOn.neg, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hu.timeSlice_differentiableAt hz).neg
  · intro z hz
    exact (hu.spatialSlice_contDiffAt hz).neg
  · apply hu.continuousOn_scalarTimeDerivative.neg.congr
    intro z hz
    exact scalarTimeDerivative_neg hu hz
  · apply hu.continuousOn_scalarSpatialGradient.neg.congr
    intro z hz
    exact scalarSpatialGradient_neg u z
  · apply hu.continuousOn_scalarSpatialHessian.neg.congr
    intro z hz
    exact scalarSpatialHessian_neg hu hz

private theorem scalarParabolicZeroOrderOperator_neg {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) {z : TimeVelocity n}
    (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => -u q) z =
      -scalarParabolicZeroOrderOperator a b c u z := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarParabolicZeroOrderOperator_apply,
    scalarTimeDerivative_neg hu hz, scalarSpatialGradient_neg u z,
    scalarSpatialHessian_neg hu hz]
  have hHessian : matrixContraction (a z.1 z.2) (-scalarSpatialHessian u z) =
      -matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) := by
    unfold matrixContraction
    simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hGradient : PDE.vecDot (b z.1 z.2) (-scalarSpatialGradient u z) =
      -PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) := by
    unfold PDE.vecDot
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [hHessian, hGradient]
  ring

private theorem isClassicalBackwardDirichletSolution_neg {n : ℕ}
    {Omega : Set (PDE.Vec n)} {r0 r1 : ℝ} (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c F : ℝ → PDE.Vec n → ℝ)
    (phi : PDE.Vec n → ℝ) (h u : TimeVelocity n → ℝ)
    (hu : IsClassicalBackwardDirichletSolution r0 r1 Omega a b c F phi h u) :
    IsClassicalBackwardDirichletSolution r0 r1 Omega a b c
      (fun r y => -F r y) (fun y => -phi y) (fun z => -h z) (fun z => -u z) := by
  refine ⟨hu.1.neg, isScalarC12On_neg hu.2.1, ?_, ?_, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_neg a b c hu.2.1 hz, hu.2.2.1 z hz]
  · intro y hy
    change -u (r1, y) = -phi y
    rw [hu.2.2.2.1 y hy]
  · intro z hz
    change -u z = -h z
    rw [hu.2.2.2.2 z hz]

/-- A supplied classical solution is bounded by explicit terminal, lateral, and source envelopes. -/
theorem abs_le_terminal_lateral_source_envelope_of_isClassicalBackwardDirichletSolution
    {n : Nat} {Omega : Set (PDE.Vec n)} {r0 r1 : Real}
    (hOmegaOpen : IsOpen Omega)
    (hOmegaBounded : Bornology.IsBounded Omega)
    (hr : r0 < r1)
    (a : CoefficientField n)
    (b : Real -> PDE.Vec n -> PDE.Vec n)
    (c F : Real -> PDE.Vec n -> Real)
    (phi : PDE.Vec n -> Real) (h u : TimeVelocity n -> Real)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r0 r1 Omega,
      c z.1 z.2 ≤ 0)
    (hu : IsClassicalBackwardDirichletSolution r0 r1 Omega a b c F phi h u)
    (Phi H Fmax : Real)
    (hPhiNonneg : 0 ≤ Phi) (hHNonneg : 0 ≤ H) (hFmaxNonneg : 0 ≤ Fmax)
    (hPhi : ∀ y ∈ closure Omega, |phi y| ≤ Phi)
    (hH : ∀ z ∈ scalarParabolicLateralFace r0 r1 Omega, |h z| ≤ H)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder r0 r1 Omega,
      |F z.1 z.2| ≤ Fmax)
    {z : TimeVelocity n} (hz : z ∈ scalarParabolicClosedCylinder r0 r1 Omega) :
    |u z| ≤ Phi + H + (r1 - z.1) * Fmax := by
  let B : TimeVelocity n → ℝ := sourceBarrier Phi H Fmax r1
  have hB : IsClassicalBackwardDirichletSolution r0 r1 Omega a b c
      (fun r y => -Fmax + c r y * B (r, y))
      (fun _ => Phi + H) B B := by
    simpa only [B] using
      isClassicalBackwardDirichletSolution_sourceBarrier (Omega := Omega) (r0 := r0)
        (r1 := r1) a b c Phi H Fmax
  have hBnonneg : ∀ q ∈ scalarParabolicClosedCylinder r0 r1 Omega, 0 ≤ B q := by
    intro q hq
    exact sourceBarrier_nonneg_on_closedCylinder hPhiNonneg hHNonneg hFmaxNonneg hq
  have huLeB : u z ≤ B z := by
    apply le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
      hOmegaOpen hOmegaBounded hr a b c haContinuous hbContinuous haPsd hc
      F (fun r y => -Fmax + c r y * B (r, y)) phi (fun _ => Phi + H) h B u B hu hB
    · intro q hq
      have hqClosed : q ∈ scalarParabolicClosedCylinder r0 r1 Omega :=
        ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, subset_closure hq.2⟩
      have hzero : c q.1 q.2 * B q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (hc q hq) (hBnonneg q hqClosed)
      have hsource : -Fmax ≤ F q.1 q.2 := (abs_le.mp (hF q hq)).1
      linarith
    · intro y hy
      have hphiUpper : phi y ≤ Phi := (le_abs_self (phi y)).trans (hPhi y hy)
      linarith
    · intro q hq
      have hqClosed : q ∈ scalarParabolicClosedCylinder r0 r1 Omega :=
        ⟨⟨hq.1.1, hq.1.2⟩, frontier_subset_closure hq.2⟩
      have hUpper : h q ≤ H := (le_abs_self (h q)).trans (hH q hq)
      have hRest : 0 ≤ Phi + (r1 - q.1) * Fmax := by
        exact add_nonneg hPhiNonneg
          (mul_nonneg (sub_nonneg.mpr hqClosed.1.2) hFmaxNonneg)
      change h q ≤ Phi + H + (r1 - q.1) * Fmax
      linarith
    · exact hz
  have hnegLeB : -u z ≤ B z := by
    apply le_on_closedCylinder_of_isClassicalBackwardDirichletSolution
      hOmegaOpen hOmegaBounded hr a b c haContinuous hbContinuous haPsd hc
      (fun r y => -F r y) (fun r y => -Fmax + c r y * B (r, y))
      (fun y => -phi y) (fun _ => Phi + H) (fun q => -h q) B (fun q => -u q) B
      (isClassicalBackwardDirichletSolution_neg a b c F phi h u hu) hB
    · intro q hq
      have hqClosed : q ∈ scalarParabolicClosedCylinder r0 r1 Omega :=
        ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, subset_closure hq.2⟩
      have hzero : c q.1 q.2 * B q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (hc q hq) (hBnonneg q hqClosed)
      have hsource : F q.1 q.2 ≤ Fmax := (abs_le.mp (hF q hq)).2
      linarith
    · intro y hy
      have hphiLower : -Phi ≤ phi y := (abs_le.mp (hPhi y hy)).1
      linarith
    · intro q hq
      have hqClosed : q ∈ scalarParabolicClosedCylinder r0 r1 Omega :=
        ⟨⟨hq.1.1, hq.1.2⟩, frontier_subset_closure hq.2⟩
      have hLower : -H ≤ h q := (abs_le.mp (hH q hq)).1
      have hRest : 0 ≤ Phi + (r1 - q.1) * Fmax := by
        exact add_nonneg hPhiNonneg
          (mul_nonneg (sub_nonneg.mpr hqClosed.1.2) hFmaxNonneg)
      change -h q ≤ Phi + H + (r1 - q.1) * Fmax
      linarith
    · exact hz
  apply (abs_le).mpr
  constructor
  · change -B z ≤ u z
    linarith
  · exact huLeB

/-- The sharp envelope is uniformly bounded on the whole closed cylinder. -/
theorem abs_le_uniform_terminal_lateral_source_envelope_of_isClassicalBackwardDirichletSolution
    {n : Nat} {Omega : Set (PDE.Vec n)} {r0 r1 : Real}
    (hOmegaOpen : IsOpen Omega)
    (hOmegaBounded : Bornology.IsBounded Omega)
    (hr : r0 < r1)
    (a : CoefficientField n)
    (b : Real -> PDE.Vec n -> PDE.Vec n)
    (c F : Real -> PDE.Vec n -> Real)
    (phi : PDE.Vec n -> Real) (h u : TimeVelocity n -> Real)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r0 r1 Omega,
      c z.1 z.2 ≤ 0)
    (hu : IsClassicalBackwardDirichletSolution r0 r1 Omega a b c F phi h u)
    (Phi H Fmax : Real)
    (hPhiNonneg : 0 ≤ Phi) (hHNonneg : 0 ≤ H) (hFmaxNonneg : 0 ≤ Fmax)
    (hPhi : ∀ y ∈ closure Omega, |phi y| ≤ Phi)
    (hH : ∀ z ∈ scalarParabolicLateralFace r0 r1 Omega, |h z| ≤ H)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder r0 r1 Omega,
      |F z.1 z.2| ≤ Fmax)
    {z : TimeVelocity n} (hz : z ∈ scalarParabolicClosedCylinder r0 r1 Omega) :
    |u z| ≤ Phi + H + (r1 - r0) * Fmax := by
  have hsharp := abs_le_terminal_lateral_source_envelope_of_isClassicalBackwardDirichletSolution
    hOmegaOpen hOmegaBounded hr a b c F phi h u haContinuous hbContinuous haPsd hc hu
    Phi H Fmax hPhiNonneg hHNonneg hFmaxNonneg hPhi hH hF (z := z) hz
  have htime : r1 - z.1 ≤ r1 - r0 := by
    linarith [hz.1.1]
  exact hsharp.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right htime hFmaxNonneg) (Phi + H))

/-- The sharp dissipative estimate implies the manuscript-shaped exponential envelope. -/
theorem abs_le_exp_mul_terminal_lateral_source_envelope_of_isClassicalBackwardDirichletSolution
    {n : Nat} {Omega : Set (PDE.Vec n)} {r0 r1 : Real}
    (hOmegaOpen : IsOpen Omega)
    (hOmegaBounded : Bornology.IsBounded Omega)
    (hr : r0 < r1)
    (a : CoefficientField n)
    (b : Real -> PDE.Vec n -> PDE.Vec n)
    (c F : Real -> PDE.Vec n -> Real)
    (phi : PDE.Vec n -> Real) (h u : TimeVelocity n -> Real)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r0 r1 Omega,
      c z.1 z.2 ≤ 0)
    (hu : IsClassicalBackwardDirichletSolution r0 r1 Omega a b c F phi h u)
    (Phi H Fmax : Real)
    (hPhiNonneg : 0 ≤ Phi) (hHNonneg : 0 ≤ H) (hFmaxNonneg : 0 ≤ Fmax)
    (hPhi : ∀ y ∈ closure Omega, |phi y| ≤ Phi)
    (hH : ∀ z ∈ scalarParabolicLateralFace r0 r1 Omega, |h z| ≤ H)
    (hF : ∀ z ∈ scalarParabolicOpenCylinder r0 r1 Omega,
      |F z.1 z.2| ≤ Fmax)
    (cBudget : Real) (hcBudget : 0 ≤ cBudget)
    {z : TimeVelocity n} (hz : z ∈ scalarParabolicClosedCylinder r0 r1 Omega) :
    |u z| ≤ Real.exp (cBudget * (r1 - r0)) * (Phi + H + (r1 - r0) * Fmax) := by
  have huniform :=
    abs_le_uniform_terminal_lateral_source_envelope_of_isClassicalBackwardDirichletSolution
    hOmegaOpen hOmegaBounded hr a b c F phi h u haContinuous hbContinuous haPsd hc hu
    Phi H Fmax hPhiNonneg hHNonneg hFmaxNonneg hPhi hH hF (z := z) hz
  have hgap : 0 ≤ r1 - r0 := sub_nonneg.mpr hr.le
  have harg : 0 ≤ cBudget * (r1 - r0) := mul_nonneg hcBudget hgap
  have hexp : 1 ≤ Real.exp (cBudget * (r1 - r0)) := by
    calc
      1 ≤ 1 + cBudget * (r1 - r0) := by linarith
      _ ≤ Real.exp (cBudget * (r1 - r0)) := by
        simpa [add_comm] using Real.add_one_le_exp (cBudget * (r1 - r0))
  have henvelope : 0 ≤ Phi + H + (r1 - r0) * Fmax := by
    exact add_nonneg (add_nonneg hPhiNonneg hHNonneg)
      (mul_nonneg hgap hFmaxNonneg)
  calc
    |u z| ≤ Phi + H + (r1 - r0) * Fmax := huniform
    _ = 1 * (Phi + H + (r1 - r0) * Fmax) := (one_mul _).symm
    _ ≤ Real.exp (cBudget * (r1 - r0)) * (Phi + H + (r1 - r0) * Fmax) :=
      mul_le_mul_of_nonneg_right hexp henvelope

end HypoellipticAleksandrov.Parabolic
