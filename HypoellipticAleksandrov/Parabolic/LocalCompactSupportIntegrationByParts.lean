module

public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Local compact-support integration by parts

This module localizes coordinate integration by parts to an open set.  The
compactly supported factor makes the relevant products globally smooth even
though the individual factors are assumed smooth only on the open set.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology

namespace HypoellipticAleksandrov.Parabolic

private theorem contDiff_mul_of_right_compactSupport
    {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (f g : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    (hgsupport : tsupport g ⊆ O) :
    ContDiff ℝ 1 (fun y => f y * g y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ O
  · exact (hf.contDiffAt (hO.mem_nhds hy)).mul (hg.contDiffAt (hO.mem_nhds hy))
  · have hyg : y ∉ tsupport g := fun h => hy (hgsupport h)
    have heq : (fun z => f z * g z) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyg] with z hz
      simp [hz]
    exact (contDiffAt_const (x := y) (n := 1) (c := (0 : ℝ))).congr_of_eventuallyEq heq

private theorem continuous_mul_spatialPartial_of_right_compactSupport
    {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O) (i : Fin d)
    (f g : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    (hgsupport : tsupport g ⊆ O) :
    Continuous (fun y => f y * spatialPartial i g y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ O
  · exact (hf.contDiffAt (hO.mem_nhds hy)).continuousAt.mul
      (((hg.contDiffAt (hO.mem_nhds hy)).continuousAt_fderiv (by norm_num)).clm_apply
        continuousAt_const)
  · have hyg : y ∉ tsupport g := fun h => hy (hgsupport h)
    have hzero : (fun z => spatialPartial i g z) =ᶠ[𝓝 y] fun _ => 0 := by
      have hd := (notMem_tsupport_iff_eventuallyEq.mp hyg).fderiv (𝕜 := ℝ)
      filter_upwards [hd] with z hz
      simp [spatialPartial, hz]
    have heq : (fun z => f z * spatialPartial i g z) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hzero] with z hz
      simp [hz]
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem continuous_spatialPartial_mul_of_right_compactSupport
    {d : ℕ} {O : Set (PDE.Vec d)} (hO : IsOpen O) (i : Fin d)
    (f g : PDE.Vec d → ℝ) (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    (hgsupport : tsupport g ⊆ O) :
    Continuous (fun y => spatialPartial i f y * g y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ O
  · exact (((hf.contDiffAt (hO.mem_nhds hy)).continuousAt_fderiv (by norm_num)).clm_apply
      continuousAt_const).mul
      (hg.contDiffAt (hO.mem_nhds hy)).continuousAt
  · have hyg : y ∉ tsupport g := fun h => hy (hgsupport h)
    have heq : (fun z => spatialPartial i f z * g z) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyg] with z hz
      simp [hz]
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- Integration by parts on an open set when the differentiated right factor
is compactly supported in that set. -/
theorem setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
    {d : ℕ} (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (i : Fin d) (f g : PDE.Vec d → ℝ)
    (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ O) :
    (∫ y in O, f y * spatialPartial i g y ∂volume) =
      -∫ y in O, spatialPartial i f y * g y ∂volume := by
  let p : PDE.Vec d → ℝ := fun y => f y * g y
  have hp : ContDiff ℝ 1 p :=
    contDiff_mul_of_right_compactSupport hO f g hf hg hgsupport
  have hpcompact : HasCompactSupport p := hgcompact.mul_left
  have hAcont : Continuous (fun y => f y * spatialPartial i g y) :=
    continuous_mul_spatialPartial_of_right_compactSupport hO i f g hf hg hgsupport
  have hBcont : Continuous (fun y => spatialPartial i f y * g y) :=
    continuous_spatialPartial_mul_of_right_compactSupport hO i f g hf hg hgsupport
  have hAcompact : HasCompactSupport (fun y => f y * spatialPartial i g y) :=
    (hgcompact.fderiv_apply ℝ (PDE.basisVec i)).mul_left
  have hBcompact : HasCompactSupport (fun y => spatialPartial i f y * g y) :=
    hgcompact.mul_left
  have hA : Integrable (fun y => f y * spatialPartial i g y) :=
    hAcont.integrable_of_hasCompactSupport hAcompact
  have hB : Integrable (fun y => spatialPartial i f y * g y) :=
    hBcont.integrable_of_hasCompactSupport hBcompact
  have hpint : Integrable p := hp.continuous.integrable_of_hasCompactSupport hpcompact
  have hdpint : Integrable (fun y => fderiv ℝ p y (PDE.basisVec i)) :=
    ((hp.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (hpcompact.fderiv_apply ℝ (PDE.basisVec i))
  have hzero : (∫ y, fderiv ℝ p y (PDE.basisVec i) ∂volume) = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := PDE.basisVec i) (f := fun _ : PDE.Vec d => (1 : ℝ)) (g := p)
      (by simp)
      (by simpa using hdpint) (by simpa using hpint)
      (by fun_prop) (fun x _ => hp.differentiable (by norm_num) x)
    simpa using h
  have hprod (y : PDE.Vec d) (hy : y ∈ O) :
      fderiv ℝ p y (PDE.basisVec i) =
        spatialPartial i f y * g y + f y * spatialPartial i g y := by
    rw [show p = fun z => f z * g z from rfl]
    rw [fderiv_fun_mul ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))
      ((hg.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))]
    simp [spatialPartial, add_comm, mul_comm]
  have houtside (y : PDE.Vec d) (hy : y ∉ O) :
      fderiv ℝ p y (PDE.basisVec i) = 0 := by
    exact congrArg (fun L => L (PDE.basisVec i))
      (fderiv_of_notMem_tsupport ℝ (fun hp' => hy (hgsupport (tsupport_mul_subset_right hp'))))
  have hglobal : (∫ y, fderiv ℝ p y (PDE.basisVec i) ∂volume) =
      ∫ y in O, (spatialPartial i f y * g y + f y * spatialPartial i g y) ∂volume := by
    rw [← integral_indicator hO.measurableSet]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ O
    · simp [Set.indicator_of_mem hy, hprod y hy]
    · simp [Set.indicator_of_notMem hy, houtside y hy]
  rw [hglobal] at hzero
  rw [integral_add hB.integrableOn hA.integrableOn] at hzero
  linarith

/-- Integration by parts on an open set when the differentiated left factor
is compactly supported in that set. -/
theorem setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_left
    {d : ℕ} (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (i : Fin d) (f g : PDE.Vec d → ℝ)
    (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    (hfcompact : HasCompactSupport f) (hfsupport : tsupport f ⊆ O) :
    (∫ y in O, f y * spatialPartial i g y ∂volume) =
      -∫ y in O, spatialPartial i f y * g y ∂volume := by
  have h := setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
    O hO i g f hg hf hfcompact hfsupport
  have h' : (∫ y in O, spatialPartial i f y * g y ∂volume) =
      -(∫ y in O, f y * spatialPartial i g y ∂volume) := by
    simpa [mul_comm] using h
  linarith

end HypoellipticAleksandrov.Parabolic
