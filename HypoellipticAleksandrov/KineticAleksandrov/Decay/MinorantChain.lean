module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.Parabolic.LocalClassical
import HypoellipticAleksandrov.Statements.ParabolicHarnack
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-!
# The Harnack chain of the common terminal minorant (companion paper, Lemma 3.6)

* `normalized_six_step_harnack`: six translated applications of the unit-cylinder
  Harnack inequality `parabolic_harnack_unit_cylinder` join `(1, 0)` to `(4, v)`, `|v| < 1`,
  inside `(0, ∞) × B₄`, giving `𝔥⁶ u (1, 0) ≤ u (4, v)`.
* `normalized_minorant_comparison`: the Harnack inequality is applied to the time-reversed
  classical scalar solutions supplied by the parabolic marginal bundle; testing against smooth
  compactly supported data gives the measure inequality
  `h • P (T-1, T, 0) ≤ P (T-4, T, v)` for `|v| < 1`, with `h = 𝔥⁶`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal MatrixOrder Topology

/-! ### Calculus for the affine change of scalar variables -/

/-- Spatial gradient under an affine change of variables. -/
theorem scalarSpatialGradient_comp_scalarAffine {d : ℕ} {V : TimeVelocity d → ℝ}
    {α a : ℝ} {c : PDE.Vec d} {e : ℝ} {z : TimeVelocity d}
    (hV : DifferentiableAt ℝ (fun y : PDE.Vec d => V (α + a * z.1, y)) (c + e • z.2)) :
    scalarSpatialGradient (fun p => V (scalarAffine α a c e p)) z =
      e • scalarSpatialGradient V (scalarAffine α a c e z) := by
  have hA : HasFDerivAt (fun y : PDE.Vec d => c + e • y)
      (e • ContinuousLinearMap.id ℝ (PDE.Vec d)) z.2 :=
    ((hasFDerivAt_id (𝕜 := ℝ) z.2).const_smul e).const_add c
  have hcomp := hV.hasFDerivAt.comp z.2 hA
  funext i
  change fderiv ℝ ((fun y : PDE.Vec d => V (α + a * z.1, y)) ∘ fun y => c + e • y) z.2
      (PDE.basisVec i) = e * fderiv ℝ (fun y : PDE.Vec d => V (α + a * z.1, y))
        (c + e • z.2) (PDE.basisVec i)
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- The anisotropic `C^{1,2}` class is stable under affine changes of variables. -/
theorem isScalarC12On_comp_scalarAffine {d : ℕ} {u : TimeVelocity d → ℝ}
    {S S' : Set (TimeVelocity d)} {α a : ℝ} {c : PDE.Vec d} {e : ℝ}
    (hu : IsScalarC12On u S') (hmaps : MapsTo (scalarAffine α a c e) S S') :
    IsScalarC12On (fun p => u (scalarAffine α a c e p)) S := by
  have hAff := contDiff_scalarAffine α a c e
  have hcont : Continuous (scalarAffine α a c e) := hAff.continuous
  have hdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun r : ℝ => u (r, c + e • z.2)) (α + a * z.1) :=
    fun z hz => hu.timeSlice_differentiableAt (hmaps hz)
  have hspace : ∀ z ∈ S, ContDiffAt ℝ 2 (fun y : PDE.Vec d => u (α + a * z.1, y))
      (c + e • z.2) := fun z hz => hu.spatialSlice_contDiffAt (hmaps hz)
  refine ⟨hu.continuousOn.comp hcont.continuousOn hmaps, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h1 : DifferentiableAt ℝ (fun r : ℝ => α + a * r) z.1 := by fun_prop
    exact DifferentiableAt.comp (g := fun r : ℝ => u (r, c + e • z.2)) z.1 (hdiff z hz) h1
  · intro z hz
    have h1 : ContDiffAt ℝ 2 (fun y : PDE.Vec d => c + e • y) z.2 := by fun_prop
    exact ContDiffAt.comp (g := fun y : PDE.Vec d => u (α + a * z.1, y)) z.2 (hspace z hz) h1
  · refine ContinuousOn.congr (f := fun z => a * scalarTimeDerivative u (scalarAffine α a c e z))
      (continuousOn_const.mul
        (hu.continuousOn_scalarTimeDerivative.comp hcont.continuousOn hmaps)) ?_
    intro z hz
    exact scalarTimeDerivative_comp_scalarAffine (hdiff z hz)
  · refine ContinuousOn.congr (f := fun z => e • scalarSpatialGradient u (scalarAffine α a c e z))
      (ContinuousOn.const_smul
        (hu.continuousOn_scalarSpatialGradient.comp hcont.continuousOn hmaps) e) ?_
    intro z hz
    exact scalarSpatialGradient_comp_scalarAffine
      ((hspace z hz).differentiableAt (by norm_num))
  · refine ContinuousOn.congr
      (f := fun z => e ^ 2 • scalarSpatialHessian u (scalarAffine α a c e z))
      (ContinuousOn.const_smul
        (hu.continuousOn_scalarSpatialHessian.comp hcont.continuousOn hmaps) (e ^ 2)) ?_
    intro z hz
    exact scalarSpatialHessian_comp_scalarAffine (hspace z hz)


/-! ### The six-step Harnack chain -/

/-- **Six-step Harnack chain** (companion paper, Lemma 3.6, analytic part).  Translated
applications of the unit-cylinder Harnack inequality along the points
`(1 + j/2, (j/6) v)`, `j = 0, ..., 6`, with cylinders in `(0, ∞) × B₄`. -/
theorem normalized_six_step_harnack (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ hfrak : ℝ, 0 < hfrak ∧
      ∀ (B : CoefficientField d) (u : TimeVelocity d → ℝ),
        IsContinuousCoefficientOn B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        (∀ p ∈ Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4, (coefficientAt B p).IsSymm) →
        HasLowerEllipticityOn lam B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        HasUpperEllipticityOn Lam B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        IsScalarC12On u (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        IsNonnegativeOn u (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        (∀ p ∈ Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4,
          scalarTimeDerivative u p =
            matrixContraction (coefficientAt B p) (scalarSpatialHessian u p)) →
        ∀ v ∈ PDE.euclideanBall 0 1, hfrak ^ 6 * u (1, 0) ≤ u (4, v) := by
  obtain ⟨hf, hfpos, hfH⟩ := parabolic_harnack_unit_cylinder d hd lam hlam Lam hlamLam
  refine ⟨hf, hfpos, ?_⟩
  intro B u hcont hsymm hlow hup hC12 hnn heq v hv
  have hv' : PDE.vecEuclideanNorm v < 1 := by
    have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
      (by norm_num : (0 : ℝ) < 1)).1 hv
    simpa only [sub_zero] using this
  -- one translated application of the Harnack inequality
  have step : ∀ (t0 : ℝ) (c p p' : PDE.Vec d), 0 < t0 → c ∈ PDE.euclideanBall 0 1 →
      p - c ∈ PDE.euclideanBall 0 (1 / 2) → p' - c ∈ PDE.euclideanBall 0 (1 / 2) →
      ∀ t t' : ℝ, t = t0 + 3 / 8 → t' = t0 + 7 / 8 → hf * u (t, p) ≤ u (t', p') := by
    intro t0 c p p' ht0 hc hp hp' t t' ht ht'
    have hc' : PDE.vecEuclideanNorm c < 1 := by
      have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
        (by norm_num : (0 : ℝ) < 1)).1 hc
      simpa only [sub_zero] using this
    have hmaps : MapsTo (scalarAffine t0 1 c 1)
        (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1)
        (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 4) := by
      rintro ⟨s, w⟩ ⟨⟨hs0, hs1⟩, hw⟩
      refine ⟨?_, ?_⟩
      · change 0 < t0 + 1 * s
        linarith
      · have hw' : PDE.vecEuclideanNorm w < 1 := by
          have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
            (by norm_num : (0 : ℝ) < 1)).1 hw
          simpa only [sub_zero] using this
        rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 4), sub_zero]
        change PDE.vecEuclideanNorm (c + (1 : ℝ) • w) < 4
        rw [one_smul]
        linarith [PDE.vecEuclideanNorm_add_le c w]
    have hu12 := isScalarC12On_comp_scalarAffine hC12 hmaps
    have hP0 : ((3 / 8 : ℝ), p - c) ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
        PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ) :=
      ⟨⟨by norm_num, by norm_num⟩, hp⟩
    have hP1 : ((7 / 8 : ℝ), p' - c) ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ
        PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ) :=
      ⟨⟨by norm_num, by norm_num⟩, hp'⟩
    have key := hfH (fun s w => B (t0 + 1 * s) (c + (1 : ℝ) • w))
      (fun z => u (scalarAffine t0 1 c 1 z))
      (hcont.comp (contDiff_scalarAffine t0 1 c 1).continuous.continuousOn hmaps)
      (fun z hz => hsymm _ (hmaps hz))
      (fun z hz => hlow _ (hmaps hz)) (fun z hz => hup _ (hmaps hz)) hu12
      (fun z hz => hnn _ (hmaps hz))
      (by
        intro z hz
        have h1 := hC12.timeSlice_differentiableAt (hmaps hz)
        have h2 := hC12.spatialSlice_contDiffAt (hmaps hz)
        rw [scalarTimeDerivative_comp_scalarAffine h1,
          scalarSpatialHessian_comp_scalarAffine h2,
          show coefficientAt (fun s w => B (t0 + 1 * s) (c + (1 : ℝ) • w)) z =
            coefficientAt B (scalarAffine t0 1 c 1 z) from rfl,
          one_pow, one_smul, one_mul]
        exact heq _ (hmaps hz))
      _ hP0 _ hP1
    have e0 : scalarAffine t0 1 c 1 ((3 / 8 : ℝ), p - c) = (t, p) := by
      simp only [scalarAffine, one_mul, one_smul, ht, add_sub_cancel]
    have e1 : scalarAffine t0 1 c 1 ((7 / 8 : ℝ), p' - c) = (t', p') := by
      simp only [scalarAffine, one_mul, one_smul, ht', add_sub_cancel]
    simpa only [e0, e1] using key
  -- the chain
  have chain : ∀ j : ℕ, j ≤ 6 →
      hf ^ j * u (1, 0) ≤ u (1 + (j : ℝ) / 2, ((j : ℝ) / 6) • v) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hjR : (j : ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hnv0 := PDE.vecEuclideanNorm_nonneg v
      have hc : (((2 * j + 1) / 12 : ℝ)) • v ∈ PDE.euclideanBall (0 : PDE.Vec d) 1 := by
        rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1), sub_zero,
          PDE.vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
        nlinarith
      have hp : ((j : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v ∈
          PDE.euclideanBall (0 : PDE.Vec d) (1 / 2) := by
        have : ((j : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v = (-(1 / 12 : ℝ)) • v := by
          module
        rw [this, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1 / 2),
          sub_zero, PDE.vecEuclideanNorm_smul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
        nlinarith
      have hp' : (((j + 1 : ℕ) : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v ∈
          PDE.euclideanBall (0 : PDE.Vec d) (1 / 2) := by
        have : (((j + 1 : ℕ) : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v =
            ((1 / 12 : ℝ)) • v := by
          push_cast
          module
        rw [this, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1 / 2),
          sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
        nlinarith
      have hstep := step (5 / 8 + (j : ℝ) / 2) (((2 * j + 1) / 12 : ℝ) • v)
        (((j : ℝ) / 6) • v) ((((j + 1 : ℕ) : ℝ) / 6) • v) (by positivity) hc hp hp'
        (1 + (j : ℝ) / 2) (1 + ((j + 1 : ℕ) : ℝ) / 2) (by ring) (by push_cast; ring)
      calc hf ^ (j + 1) * u (1, 0) = hf * (hf ^ j * u (1, 0)) := by ring
        _ ≤ hf * u (1 + (j : ℝ) / 2, ((j : ℝ) / 6) • v) :=
          mul_le_mul_of_nonneg_left ih' hfpos.le
        _ ≤ u (1 + ((j + 1 : ℕ) : ℝ) / 2, (((j + 1 : ℕ) : ℝ) / 6) • v) := hstep
  have h6 := chain 6 le_rfl
  norm_num at h6
  convert h6 using 2


/-! ### Time reversal of the supplied scalar solutions -/

/-- The time reversal `(θ, v) ↦ (T - θ, v)`, written as an affine scalar change of variables. -/
abbrev timeReversal {d : ℕ} (T : ℝ) : TimeVelocity d → TimeVelocity d :=
  scalarAffine T (-1) 0 1

theorem timeReversal_apply {d : ℕ} (T θ : ℝ) (v : PDE.Vec d) :
    timeReversal T (θ, v) = (T - θ, v) := by
  simp [timeReversal, scalarAffine, sub_eq_add_neg]

theorem timeReversal_mapsTo {d : ℕ} {Ω : Set (PDE.Vec d)} (T : ℝ) :
    MapsTo (timeReversal T) (Ioi (0 : ℝ) ×ˢ Ω)
      (ParabolicProbe.scalarPastOpenCylinder Ω stationary T) := by
  rintro ⟨θ, v⟩ ⟨hθ, hv⟩
  rw [mem_scalarPastOpenCylinder_stationary, timeReversal_apply]
  exact ⟨by simpa using hθ, hv⟩

/-- The time-reversed classical scalar solution is `C^{1,2}` on `(0, ∞) × Ω`. -/
theorem timeReversed_isScalarC12On {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    {B : CoefficientField d} {T : ℝ} {F : BoundedBorel (PDE.Vec d)} {V : TimeVelocity d → ℝ}
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
      (zIndependentCoefficient B) T F V) :
    IsScalarC12On (fun p => V (timeReversal T p)) (Ioi (0 : ℝ) ×ˢ Ω) :=
  isScalarC12On_comp_scalarAffine
    (isScalarC12On_of_isOpen_contDiffOn_two (isOpen_scalarPastOpenCylinder_stationary hΩ T)
      (hV.2.2.1.of_le (by norm_num))) (timeReversal_mapsTo T)

/-- The time-reversed classical scalar solution solves the forward equation with the
reversed coefficient. -/
theorem timeReversed_equation {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    {B : CoefficientField d} {T : ℝ} {F : BoundedBorel (PDE.Vec d)} {V : TimeVelocity d → ℝ}
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
      (zIndependentCoefficient B) T F V) :
    ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ω,
      scalarTimeDerivative (fun p => V (timeReversal T p)) p =
        matrixContraction (coefficientAt B (timeReversal T p))
          (scalarSpatialHessian (fun p => V (timeReversal T p)) p) := by
  intro p hp
  have hc12 := isScalarC12On_of_isOpen_contDiffOn_two
    (isOpen_scalarPastOpenCylinder_stationary hΩ T) (hV.2.2.1.of_le (by norm_num))
  have h1 := hc12.timeSlice_differentiableAt (timeReversal_mapsTo T hp)
  have h2 := hc12.spatialSlice_contDiffAt (timeReversal_mapsTo T hp)
  have hop := hV.2.2.2.1 _ (timeReversal_mapsTo T hp)
  have hgrad : PDE.vecDot ((0 : ℝ → PDE.Vec d → PDE.Vec d)
      (timeReversal T p).1 (timeReversal T p).2)
      (scalarSpatialGradient V (timeReversal T p)) = 0 := by
    simp [PDE.vecDot]
  rw [scalarParabolicOperator_apply, hgrad, add_zero] at hop
  rw [scalarTimeDerivative_comp_scalarAffine h1, scalarSpatialHessian_comp_scalarAffine h2,
    one_pow, one_smul]
  change -1 * scalarTimeDerivative V (timeReversal T p) = _
  have hop' : scalarTimeDerivative V (timeReversal T p) =
      -matrixContraction (coefficientAt B (timeReversal T p))
        (scalarSpatialHessian V (timeReversal T p)) := by
    have : zIndependentCoefficient B (timeReversal T p).1 (timeReversal T p).2 0 =
        coefficientAt B (timeReversal T p) := rfl
    rw [this] at hop
    linarith
  rw [hop']
  ring

/-- Smooth coefficients are jointly continuous. -/
theorem continuous_coefficientAt_of_smooth {d : ℕ} {B : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B)) :
    Continuous (coefficientAt B) := by
  refine continuous_matrix fun i j => ?_
  exact (hB i j).continuous.comp
    (continuous_fst.prodMk (continuous_snd.prodMk (continuous_const (y := (0 : PDE.Vec d)))))

/-! ### The measure comparison -/

/-- **Normalized minorant comparison** (companion paper, Lemma 3.6, measure part).  With
`h = 𝔥⁶` the marginal from `(T - 1, 0)` is dominated, up to the factor `h`, by the marginal
from `(T - 4, v)`, `|v| < 1`, for every supplied realization on `B₄(0)`. -/
theorem normalized_minorant_comparison (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (T : ℝ), (0 : PDE.Vec d) ∈ D →
        PDE.euclideanBall (0 : PDE.Vec d) 4 ⊆ D →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary)
        (K : MovingFiberKernel (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary),
        RealizesTerminalEvolution (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
          (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4).measurableSet
          (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
          (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4).measurableSet
          (zIndependentCoefficient B) K →
        IsDomainMonotoneEvolution (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
          (zIndependentCoefficient B) b K →
      ∀ (qearly qlate : ParabolicEvolutionQuery (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary),
        qearly.1 = (T - 4, T, qearly.1.2.2) →
        qlate.1 = (T - 1, T, (0 : PDE.Vec d)) →
        qearly.1.2.2 ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 : ℝ) →
        ENNReal.ofReal h • P K (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4).measurableSet qlate ≤
          P K (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4).measurableSet qearly := by
  obtain ⟨hf, hfpos, hfH⟩ := normalized_six_step_harnack d hd lam Lam hlam hlamLam
  refine ⟨hf ^ 6, pow_pos hfpos 6, ?_⟩
  intro m Lb D B b hset T h0 hsub S K hreal hpar hmono qearly qlate hqe hql hv
  have _ := And.intro h0 (And.intro hsub (And.intro hreal hmono))
  obtain ⟨hlamB, -, hsmooth, hsymm, hlow, hup⟩ := hset.1
  have hΩo := PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4
  rcases qearly with ⟨⟨σ, τ, y⟩, hστ, hy⟩
  rcases qlate with ⟨⟨σ', τ', y'⟩, hστ', hy'⟩
  dsimp only at hqe hql hv
  simp only [Prod.mk.injEq, and_true] at hqe hql
  obtain ⟨hσ, hτ⟩ := hqe
  obtain ⟨hσ', hτ', hy0⟩ := hql
  subst hσ hσ' hy0
  have hT1 : T = τ := hτ.symm
  have hT2 : T = τ' := hτ'.symm
  subst hT1 hT2
  have hfin : IsFiniteMeasure (ENNReal.ofReal (hf ^ 6) •
      P K hΩo.measurableSet ⟨(T - 1, T, 0), hστ', hy'⟩) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine measure_le_of_smooth_integral_le hΩo ?_ ?_
  · rw [Measure.smul_apply, P_compl_eq_zero_stationary, smul_zero]
  · intro φ hφ hc hsupp h01
    obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩo.measurableSet B K hpar φ hφ hc hsupp T
    have hcontB := continuous_coefficientAt_of_smooth hsmooth
    have hmaps : MapsTo (timeReversal T) (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 4)
        (ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall (0 : PDE.Vec d) 4)
          stationary T) := timeReversal_mapsTo T
    have key := hfH (fun θ v => B (T + -1 * θ) (0 + (1 : ℝ) • v))
      (fun p => V (timeReversal T p))
      (hcontB.continuousOn.comp (contDiff_scalarAffine T (-1) 0 1).continuous.continuousOn
        (fun p _ => mem_univ _))
      (fun p _ => hsymm _ _)
      (fun p _ => hlow _ _) (fun p _ => hup _ _)
      (timeReversed_isScalarC12On hΩo hV)
      (by
        intro p hp
        have hmem := hmaps hp
        rw [mem_scalarPastOpenCylinder_stationary] at hmem
        have hle : (timeReversal T p).1 ≤ T := hmem.1.le
        have := hVeval (timeReversal T p).1 hle (timeReversal T p).2
          (by simpa only [movingDomain_stationary] using hmem.2)
        change 0 ≤ V ((timeReversal T p).1, (timeReversal T p).2)
        rw [this]
        exact integral_nonneg fun x => (h01 x).1)
      (timeReversed_equation hΩo hV) y hv
    have e1 : timeReversal T ((1 : ℝ), (0 : PDE.Vec d)) = (T - 1, 0) := timeReversal_apply T 1 0
    have e4 : timeReversal T ((4 : ℝ), y) = (T - 4, y) := timeReversal_apply T 4 y
    have hlate := hVeval (T - 1) hστ' 0 hy'
    have hearly := hVeval (T - 4) hστ y hy
    simp only [e1, e4] at key
    rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hfpos 6).le, smul_eq_mul]
    change hf ^ 6 * ∫ x, φ x ∂(P K hΩo.measurableSet (scalarQuery (T - 1) T hστ' 0 hy')) ≤
      ∫ x, φ x ∂(P K hΩo.measurableSet (scalarQuery (T - 4) T hστ y hy))
    rw [← hlate, ← hearly]
    exact key

end HypoellipticAleksandrov.KineticAleksandrov.Decay
