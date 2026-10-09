module

public import HypoellipticAleksandrov.Parabolic.ABP
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.Linarith

/-!
# Reverse-time local Dirichlet estimate for the parabolic ABP theorem

This module applies the lower-ellipticity forward ABP corollary to
`H (θ, v) = h (1 - θ, v)`; the reflected function is not negated. It proves
the set, boundary, derivative, operator, and restricted-norm transport needed
for the reverse-time local Dirichlet estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- Reflection of a time--velocity point about the time slice `t = 1 / 2`. -/
def timeReflection {d : ℕ} (z : TimeVelocity d) : TimeVelocity d :=
  (1 - z.1, z.2)

/-- Pullback of a scalar field by the fixed time reflection. -/
def timeReflectedScalar {d : ℕ} (f : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  fun z => f (timeReflection z)

/-- Pullback of a curried coefficient field by the fixed time reflection. -/
def timeReflectedCoefficient {d : ℕ} (A : CoefficientField d) : CoefficientField d :=
  fun t v => A (1 - t) v

/-- Evaluation of a reflected scalar field. -/
@[simp] theorem timeReflectedScalar_apply {d : ℕ} (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    timeReflectedScalar f z = f (timeReflection z) :=
  rfl

/-- Evaluation of a reflected coefficient field at a time--velocity pair. -/
@[simp] theorem coefficientAt_timeReflectedCoefficient {d : ℕ}
    (A : CoefficientField d) (z : TimeVelocity d) :
    coefficientAt (timeReflectedCoefficient A) z =
      coefficientAt A (timeReflection z) :=
  rfl

/-- Time reflection is an involution. -/
@[simp] theorem timeReflection_involutive {d : ℕ} :
    Function.Involutive (@timeReflection d) := by
  intro z
  ext <;> simp [timeReflection]

/-- Time reflection is continuous. -/
theorem continuous_timeReflection {d : ℕ} : Continuous (@timeReflection d) := by
  exact (continuous_const.sub continuous_fst).prodMk continuous_snd

/-- Time reflection is globally smooth. -/
theorem contDiff_timeReflection {d : ℕ} : ContDiff ℝ 2 (@timeReflection d) := by
  exact (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

/-- Scalar pullback preserves continuity. -/
theorem continuous_timeReflectedScalar {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : Continuous f) : Continuous (timeReflectedScalar f) := by
  exact hf.comp continuous_timeReflection

/-- Scalar pullback preserves global `C²` regularity. -/
theorem contDiff_timeReflectedScalar {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (timeReflectedScalar f) := by
  exact hf.comp contDiff_timeReflection

/-- Coefficient pullback preserves continuity. -/
theorem isContinuousCoefficient_timeReflected {d : ℕ} {A : CoefficientField d}
    (hA : IsContinuousCoefficient A) :
    IsContinuousCoefficient (timeReflectedCoefficient A) := by
  change Continuous (coefficientAt A ∘ timeReflection)
  exact hA.comp continuous_timeReflection

private def timeReflectionLinear (d : ℕ) :
    TimeVelocity d →L[ℝ] TimeVelocity d :=
  (-ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).prod
    (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))

private theorem hasFDerivAt_timeReflection {d : ℕ} (z : TimeVelocity d) :
    HasFDerivAt timeReflection (timeReflectionLinear d) z := by
  change HasFDerivAt (fun w : TimeVelocity d => (1 - w.1, w.2))
    (timeReflectionLinear d) z
  simpa only [timeReflectionLinear] using
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_sub (1 : ℝ)).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z))

private theorem timeReflectionLinear_time {d : ℕ} :
    timeReflectionLinear d ((1, 0) : TimeVelocity d) = (-1, 0) := by
  simp [timeReflectionLinear]

private theorem timeReflectionLinear_velocity {d : ℕ} (i : Fin d) :
    timeReflectionLinear d ((0, Pi.single i 1) : TimeVelocity d) =
      (0, Pi.single i 1) := by
  simp [timeReflectionLinear]

private theorem fderiv_timeReflectedScalar {d : ℕ} {h : TimeVelocity d → ℝ}
    (hh : ContDiff ℝ 2 h) (z : TimeVelocity d) :
    fderiv ℝ (timeReflectedScalar h) z =
      (fderiv ℝ h (timeReflection z)).comp (timeReflectionLinear d) := by
  have hhAt : HasFDerivAt h (fderiv ℝ h (timeReflection z)) (timeReflection z) :=
    (hh.differentiable (by norm_num) (timeReflection z)).hasFDerivAt
  change fderiv ℝ (h ∘ timeReflection) z = _
  exact (hhAt.comp z (hasFDerivAt_timeReflection z)).fderiv

/-- Reflection reverses the literal project time derivative. -/
theorem timeDerivative_timeReflectedScalar {d : ℕ} {h : TimeVelocity d → ℝ}
    (hh : ContDiff ℝ 2 h) (z : TimeVelocity d) :
    timeDerivative (timeReflectedScalar h) z =
      -timeDerivative h (timeReflection z) := by
  unfold timeDerivative
  rw [fderiv_timeReflectedScalar hh]
  rw [ContinuousLinearMap.comp_apply, timeReflectionLinear_time]
  have hvec : ((-1, 0) : TimeVelocity d) = -((1, 0) : TimeVelocity d) := by
    ext <;> simp
  rw [hvec, map_neg]

/-- Reflection preserves the pure-velocity Hessian. -/
theorem velocityHessian_timeReflectedScalar {d : ℕ} {h : TimeVelocity d → ℝ}
    (hh : ContDiff ℝ 2 h) (z : TimeVelocity d) :
    velocityHessian (timeReflectedScalar h) z =
      velocityHessian h (timeReflection z) := by
  funext i j
  let R' : TimeVelocity d →L[ℝ] TimeVelocity d := timeReflectionLinear d
  have hfirst : fderiv ℝ (timeReflectedScalar h) =
      fun x => (fderiv ℝ h (timeReflection x)).comp R' := by
    funext x
    simpa only [R'] using fderiv_timeReflectedScalar hh x
  have hDh : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have houter : HasFDerivAt (fun x : TimeVelocity d =>
      fderiv ℝ h (timeReflection x))
      ((fderiv ℝ (fderiv ℝ h) (timeReflection z)).comp R') z := by
    simpa only [Function.comp_def, R'] using
      (hDh (timeReflection z)).hasFDerivAt.comp z
        (hasFDerivAt_timeReflection z)
  have hcomp := houter.clm_comp (hasFDerivAt_const R' z)
  change fderiv ℝ (fderiv ℝ (timeReflectedScalar h)) z
      ((0, Pi.single i 1) : TimeVelocity d)
      ((0, Pi.single j 1) : TimeVelocity d) = _
  rw [hfirst, hcomp.fderiv]
  simp only [R', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply,
    timeReflectionLinear_velocity, velocityHessian]

/-- The reflected forward operator is the negated original backward expression. -/
theorem parabolicOperator_timeReflectedScalar_eq {d : ℕ} (A : CoefficientField d)
    (h : TimeVelocity d → ℝ) (hh : ContDiff ℝ 2 h) (z : TimeVelocity d) :
    parabolicOperator (timeReflectedCoefficient A) (timeReflectedScalar h) z =
      -(timeDerivative h (timeReflection z) +
        matrixContraction (coefficientAt A (timeReflection z))
          (velocityHessian h (timeReflection z))) := by
  unfold parabolicOperator
  rw [timeDerivative_timeReflectedScalar hh,
    velocityHessian_timeReflectedScalar hh,
    coefficientAt_timeReflectedCoefficient]
  ring

/-- Reflection sends the original open cylinder to the forward one exactly. -/
theorem timeReflection_preimage_localInterior {d : ℕ} {a : ℝ}
    (yStar : PDE.Vec d) :
    timeReflection ⁻¹' (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) =
      parabolicInterior (1 - a) yStar := by
  ext z
  rcases z with ⟨t, v⟩
  change ((1 - t ∈ Set.Ioo a 1) ∧ v ∈ PDE.euclideanBall yStar 1) ↔
    ((t ∈ Set.Ioo 0 (1 - a)) ∧ v ∈ PDE.euclideanBall yStar 1)
  constructor
  · rintro ⟨⟨hleft, hright⟩, hv⟩
    exact ⟨⟨by linarith, by linarith⟩, hv⟩
  · rintro ⟨⟨hleft, hright⟩, hv⟩
    exact ⟨⟨by linarith, by linarith⟩, hv⟩

/-- Reflection sends the original closed cylinder to the forward closure exactly. -/
theorem timeReflection_preimage_localClosure {d : ℕ} {a : ℝ}
    (yStar : PDE.Vec d) :
    timeReflection ⁻¹' (Set.Icc a 1 ×ˢ PDE.euclideanClosedBall yStar 1) =
      closedParabolicCylinder (1 - a) yStar := by
  ext z
  rcases z with ⟨t, v⟩
  change ((1 - t ∈ Set.Icc a 1) ∧ v ∈ PDE.euclideanClosedBall yStar 1) ↔
    ((t ∈ Set.Icc 0 (1 - a)) ∧ v ∈ PDE.euclideanClosedBall yStar 1)
  constructor
  · rintro ⟨⟨hleft, hright⟩, hv⟩
    exact ⟨⟨by linarith, by linarith⟩, hv⟩
  · rintro ⟨⟨hleft, hright⟩, hv⟩
    exact ⟨⟨by linarith, by linarith⟩, hv⟩

/-- Reflection maps the forward open cylinder onto the original open cylinder. -/
theorem timeReflection_image_localInterior {d : ℕ} {a : ℝ}
    (yStar : PDE.Vec d) :
    timeReflection '' parabolicInterior (1 - a) yStar =
      Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1 := by
  rw [← timeReflection_preimage_localInterior yStar]
  exact Set.image_preimage_eq _ timeReflection_involutive.surjective

/-- Reflection maps the forward closed cylinder onto the original closed cylinder. -/
theorem timeReflection_image_localClosure {d : ℕ} {a : ℝ}
    (yStar : PDE.Vec d) :
    timeReflection '' closedParabolicCylinder (1 - a) yStar =
      Set.Icc a 1 ×ˢ PDE.euclideanClosedBall yStar 1 := by
  rw [← timeReflection_preimage_localClosure yStar]
  exact Set.image_preimage_eq _ timeReflection_involutive.surjective

/-- Lower ellipticity transports from the original closed cylinder. -/
theorem lowerEllipticity_timeReflected_on_closedCylinder {d : ℕ}
    {a lam : ℝ} {yStar : PDE.Vec d} {A : CoefficientField d}
    (hlo : ∀ z ∈ Set.Icc a 1 ×ˢ PDE.euclideanClosedBall yStar 1,
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z) :
    ∀ z ∈ closedParabolicCylinder (1 - a) yStar,
      lam • (1 : PDE.Mat d) ≤ coefficientAt (timeReflectedCoefficient A) z := by
  intro z hz
  rw [coefficientAt_timeReflectedCoefficient]
  apply hlo (timeReflection z)
  change z ∈ timeReflection ⁻¹'
    (Set.Icc a 1 ×ˢ PDE.euclideanClosedBall yStar 1)
  rw [timeReflection_preimage_localClosure yStar]
  exact hz

/-- Nonnegativity of the source transports to the reflected interior. -/
theorem source_nonnegative_timeReflected_on_interior {d : ℕ}
    {a : ℝ} {yStar : PDE.Vec d} {F : TimeVelocity d → ℝ}
    (hF : ∀ z ∈ Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1, 0 ≤ F z) :
    ∀ z ∈ parabolicInterior (1 - a) yStar, 0 ≤ timeReflectedScalar F z := by
  intro z hz
  rw [timeReflectedScalar_apply]
  apply hF (timeReflection z)
  change z ∈ timeReflection ⁻¹'
    (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1)
  rw [timeReflection_preimage_localInterior yStar]
  exact hz

/-- A continuous lateral zero trace extends from the open interval to its left endpoint. -/
theorem lateral_zero_at_left_endpoint_of_continuous
    {d : ℕ} {a : ℝ} (ha : a < 1) {yStar : PDE.Vec d}
    {h : TimeVelocity d → ℝ} (hh : Continuous h)
    (hlateral : ∀ t ∈ Set.Ioo a 1, ∀ v ∈ PDE.euclideanSphere yStar 1,
      h (t, v) = 0) :
    ∀ v ∈ PDE.euclideanSphere yStar 1, h (a, v) = 0 := by
  intro v hv
  let s : Set (TimeVelocity d) := Set.Ioo a 1 ×ˢ PDE.euclideanSphere yStar 1
  have hmaps : Set.MapsTo h s ({0} : Set ℝ) := by
    intro z hz
    rcases hz with ⟨ht, hv'⟩
    simpa only [Set.mem_singleton_iff] using hlateral z.1 ht z.2 hv'
  have hz : (a, v) ∈ closure s := by
    rw [show s = Set.Ioo a 1 ×ˢ PDE.euclideanSphere yStar 1 by rfl,
      closure_prod_eq, closure_Ioo ha.ne]
    exact ⟨⟨le_rfl, ha.le⟩, subset_closure hv⟩
  have hzero : h (a, v) ∈ ({0} : Set ℝ) :=
    hmaps.closure_left hh isClosed_singleton hz
  simpa only [Set.mem_singleton_iff] using hzero

private theorem lateral_zero_on_closed_interval
    {d : ℕ} {a : ℝ} (ha : a < 1) {yStar : PDE.Vec d}
    {h : TimeVelocity d → ℝ} (hh : Continuous h)
    (hlateral : ∀ t ∈ Set.Ioo a 1, ∀ v ∈ PDE.euclideanSphere yStar 1,
      h (t, v) = 0)
    (hterminal : ∀ v ∈ PDE.euclideanClosedBall yStar 1, h (1, v) = 0) :
    ∀ t ∈ Set.Icc a 1, ∀ v ∈ PDE.euclideanSphere yStar 1, h (t, v) = 0 := by
  intro t ht v hv
  rcases lt_or_eq_of_le ht.1 with hat | rfl
  · rcases lt_or_eq_of_le ht.2 with htone | rfl
    · exact hlateral t ⟨hat, htone⟩ v hv
    · apply hterminal v
      change PDE.euclideanSqDist v yStar = 1 ^ 2 at hv
      change PDE.euclideanSqDist v yStar ≤ 1 ^ 2
      exact le_of_eq hv
  · exact lateral_zero_at_left_endpoint_of_continuous ha hh hlateral v hv

/-- The reflected function vanishes on the forward parabolic boundary. -/
theorem timeReflectedScalar_zero_on_forwardParabolicBoundary
    {d : ℕ} {a : ℝ} (ha : a < 1) {yStar : PDE.Vec d}
    {h : TimeVelocity d → ℝ} (hh : Continuous h)
    (hlateral : ∀ t ∈ Set.Ioo a 1, ∀ v ∈ PDE.euclideanSphere yStar 1,
      h (t, v) = 0)
    (hterminal : ∀ v ∈ PDE.euclideanClosedBall yStar 1, h (1, v) = 0) :
    ∀ z ∈ forwardParabolicBoundary (1 - a) yStar,
      timeReflectedScalar h z = 0 := by
  intro z hz
  rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral'
  · rcases hinitial with ⟨hztime, hzball⟩
    rcases z with ⟨t, v⟩
    change t = 0 at hztime
    change v ∈ PDE.euclideanClosedBall yStar 1 at hzball
    subst t
    simpa only [timeReflectedScalar_apply, timeReflection, sub_zero] using
      hterminal v hzball
  · rcases hlateral' with ⟨hzero, hT, hsphere⟩
    rcases z with ⟨t, v⟩
    have htime : 1 - t ∈ Set.Icc a 1 := by
      constructor <;> linarith
    simpa only [timeReflectedScalar_apply, timeReflection] using
      lateral_zero_on_closed_interval ha hh hlateral hterminal
        (1 - t) htime v hsphere

/-- Reflection preserves product Lebesgue volume. -/
theorem timeReflection_measurePreserving {d : ℕ} :
    MeasurePreserving (@timeReflection d) (volume : Measure (TimeVelocity d)) volume := by
  let htime : MeasurePreserving (fun t : ℝ => 1 - t)
      (volume : Measure ℝ) volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left (volume : Measure ℝ) 1).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hprod := htime.prod (MeasurePreserving.id (volume : Measure (PDE.Vec d)))
  rw [volume_timeVelocity_eq_prod d]
  change MeasurePreserving (fun p : ℝ × PDE.Vec d => (1 - p.1, p.2)) _ _
  simpa only [Prod.map_def, id_eq] using hprod

/-- Restriction of time reflection to the exact reversed interior is measure-preserving. -/
theorem timeReflection_measurePreserving_restrict_localInterior
    {d : ℕ} {a : ℝ} (yStar : PDE.Vec d) :
    MeasurePreserving (@timeReflection d)
      (volume.restrict (parabolicInterior (1 - a) yStar))
      (volume.restrict (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1)) := by
  have hS : MeasurableSet (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) :=
    measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall yStar 1)
  simpa only [timeReflection_preimage_localInterior yStar] using
    (timeReflection_measurePreserving (d := d)).restrict_preimage hS

/-- The reflected restricted `L^(d+1)` norm equals the original one. -/
theorem parabolicELpNormOn_timeReflectedScalar_eq
    {d : ℕ} {a : ℝ} (yStar : PDE.Vec d) {f : TimeVelocity d → ℝ}
    (hf : Continuous f) :
    parabolicELpNormOn d (timeReflectedScalar f)
        (parabolicInterior (1 - a) yStar) =
      parabolicELpNormOn d f
        (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) := by
  unfold parabolicELpNormOn timeReflectedScalar
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
    (timeReflection_measurePreserving_restrict_localInterior yStar)

/-- The reflected restricted real `L^(d+1)` norm equals the original one. -/
theorem parabolicLpNormOn_timeReflectedScalar_eq
    {d : ℕ} {a : ℝ} (yStar : PDE.Vec d) {f : TimeVelocity d → ℝ}
    (hf : Continuous f) :
    parabolicLpNormOn d (timeReflectedScalar f)
        (parabolicInterior (1 - a) yStar) =
      parabolicLpNormOn d f
        (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) := by
  unfold parabolicLpNormOn
  exact congrArg ENNReal.toReal
    (parabolicELpNormOn_timeReflectedScalar_eq yStar hf)

private theorem parabolicLpNormOn_max_eq_of_nonnegative
    {d : ℕ} {f : TimeVelocity d → ℝ} {s : Set (TimeVelocity d)}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, 0 ≤ f z) :
    parabolicLpNormOn d (fun z => max (f z) 0) s =
      parabolicLpNormOn d f s := by
  unfold parabolicLpNormOn parabolicELpNormOn
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hs] with z hz
  exact max_eq_left (hf z hz)

private theorem reflected_subsolution_of_backward_equation
    {d : ℕ} {a : ℝ} {yStar : PDE.Vec d} {A : CoefficientField d}
    {F h : TimeVelocity d → ℝ} (hh : ContDiff ℝ 2 h)
    (hpde : ∀ z ∈ Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1,
      timeDerivative h z +
          matrixContraction (coefficientAt A z) (velocityHessian h z) = -F z) :
    IsParabolicSubsolutionOn (timeReflectedCoefficient A) (timeReflectedScalar F)
      (timeReflectedScalar h) (parabolicInterior (1 - a) yStar) := by
  intro z hz
  have hz' : timeReflection z ∈ Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1 := by
    change z ∈ timeReflection ⁻¹'
      (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1)
    rw [timeReflection_preimage_localInterior yStar]
    exact hz
  rw [parabolicOperator_timeReflectedScalar_eq A h hh, hpde (timeReflection z) hz']
  simp only [neg_neg, timeReflectedScalar_apply]
  exact le_rfl

/-- The reverse-time local Dirichlet estimate under the global classical leaf package. -/
theorem local_dirichlet_estimate_of_smooth
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ), 0 ≤ a → a < 1 →
      ∀ (yStar : PDE.Vec d) (A : CoefficientField d)
        (F h : TimeVelocity d → ℝ),
        IsContinuousCoefficient A → Continuous F → ContDiff ℝ 2 h →
        (∀ z ∈ Set.Icc a 1 ×ˢ PDE.euclideanClosedBall yStar 1,
          lam • (1 : PDE.Mat d) ≤ coefficientAt A z) →
        (∀ z ∈ Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1,
          timeDerivative h z +
              matrixContraction (coefficientAt A z) (velocityHessian h z) =
            -F z) →
        (∀ z ∈ Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1, 0 ≤ F z) →
        (∀ t ∈ Set.Ioo a 1, ∀ v ∈ PDE.euclideanSphere yStar 1,
          h (t, v) = 0) →
        (∀ v ∈ PDE.euclideanClosedBall yStar 1, h (1, v) = 0) →
        h (a, yStar) ≤
          C * parabolicLpNormOn d F
            (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) := by
  obtain ⟨C, hC, hABP⟩ :=
    parabolic_abp_unit_of_lower_ellipticity d hd lam hlam
  refine ⟨C, hC, ?_⟩
  intro a ha0 ha1 yStar A F h hAcont hFcont hh hlo hpde hFnonneg hlateral hterminal
  let T : ℝ := 1 - a
  have hT : 0 < T := by dsimp [T]; linarith
  have hT_le_one : T ≤ 1 := by dsimp [T]; linarith
  have hAref : IsContinuousCoefficient (timeReflectedCoefficient A) :=
    isContinuousCoefficient_timeReflected hAcont
  have hFref : Continuous (timeReflectedScalar F) :=
    continuous_timeReflectedScalar hFcont
  have hhref : ContDiff ℝ 2 (timeReflectedScalar h) :=
    contDiff_timeReflectedScalar hh
  have hloRef : ∀ z ∈ closedParabolicCylinder T yStar,
      lam • (1 : PDE.Mat d) ≤ coefficientAt (timeReflectedCoefficient A) z := by
    simpa only [T] using lowerEllipticity_timeReflected_on_closedCylinder hlo
  have hsubRef : IsParabolicSubsolutionOn (timeReflectedCoefficient A)
      (timeReflectedScalar F)
      (timeReflectedScalar h) (parabolicInterior T yStar) := by
    simpa only [T] using reflected_subsolution_of_backward_equation hh hpde
  have hboundaryRef : ∀ z ∈ forwardParabolicBoundary T yStar,
      timeReflectedScalar h z ≤ 0 := by
    intro z hz
    simpa only [T] using
      (timeReflectedScalar_zero_on_forwardParabolicBoundary ha1
        hh.continuous hlateral hterminal z hz).le
  have hzStar : (T, yStar) ∈ closedParabolicCylinder T yStar := by
    rw [mem_closedParabolicCylinder_iff]
    refine ⟨hT.le, le_rfl, ?_⟩
    change PDE.euclideanSqDist yStar yStar ≤ 1 ^ 2
    simp
  have hABPbound := hABP hT hT_le_one yStar (timeReflectedCoefficient A)
    (timeReflectedScalar F) (timeReflectedScalar h)
    hAref hFref hhref hloRef hsubRef hboundaryRef (T, yStar) hzStar
  have hnormReflection :
      parabolicLpNormOn d (fun z => max (timeReflectedScalar F z) 0)
          (parabolicInterior T yStar) =
        parabolicLpNormOn d (fun z => max (F z) 0)
          (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) := by
    change parabolicLpNormOn d (timeReflectedScalar (fun z => max (F z) 0))
      (parabolicInterior (1 - a) yStar) = _
    exact parabolicLpNormOn_timeReflectedScalar_eq yStar (hFcont.max continuous_const)
  have hnormOriginal :
      parabolicLpNormOn d (fun z => max (F z) 0)
          (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) =
        parabolicLpNormOn d F
          (Set.Ioo a 1 ×ˢ PDE.euclideanBall yStar 1) :=
    parabolicLpNormOn_max_eq_of_nonnegative
      (measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall yStar 1)) hFnonneg
  have hevaluation : timeReflectedScalar h (T, yStar) = h (a, yStar) := by
    simp only [timeReflectedScalar_apply, timeReflection, T, sub_sub_cancel]
  rw [hevaluation, hnormReflection, hnormOriginal] at hABPbound
  exact hABPbound

end HypoellipticAleksandrov.Parabolic
