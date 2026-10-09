module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyReferenceHolder
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyReferenceCollarCutoff
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyScaling
public import HypoellipticAleksandrov.Parabolic.DensityToPoint
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjectionRecovery

/-!
# Physical local parabolic Morrey Holder estimate

The private scaling lemmas below use only the local regularity on the source
box.  They are restricted-set versions of the global componentwise API.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

private theorem parabolicELpNormOn_timeDerivative_pullbackScalar_local
    {d : Nat} {U s : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {t0 r : Real} {v0 : PDE.Vec d} (hU : IsOpen U)
    (hs : MeasurableSet s) (hr : 0 < r) (hu : ContDiffOn Real 2 u U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) s U) :
    parabolicELpNormOn d (timeDerivative (pullbackScalar u t0 v0 r)) s =
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (timeDerivative u) (parabolicAffine t0 v0 r '' s) := by
  have heq : timeDerivative (pullbackScalar u t0 v0 r) =ᵐ[volume.restrict s]
      fun x => r ^ 2 * timeDerivative u (parabolicAffine t0 v0 r x) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hs]
    exact Eventually.of_forall fun x hx =>
      timeDerivative_pullbackScalar (q := u) (z := x) (t₀ := t0) (v₀ := v0) (r := r)
        (hu.contDiffAt (hU.mem_nhds (hmap hx)))
  calc
    parabolicELpNormOn d (timeDerivative (pullbackScalar u t0 v0 r)) s =
        eLpNorm (fun x => r ^ 2 * timeDerivative u (parabolicAffine t0 v0 r x))
          (parabolicExponent d) (volume.restrict s) := eLpNorm_congr_ae heq
    _ = ‖r ^ 2‖ₑ * parabolicELpNormOn d
        (pullbackScalar (timeDerivative u) t0 v0 r) s := by
      change eLpNorm ((r ^ 2) • pullbackScalar (timeDerivative u) t0 v0 r)
        (parabolicExponent d) (volume.restrict s) = _
      rw [eLpNorm_const_smul]
      rfl
    _ = _ := by
      rw [parabolicELpNormOn_pullbackScalar t0 v0 hr]
      ac_rfl

private theorem parabolicELpNormOn_velocityGradient_pullbackScalar_local
    {d : Nat} {U s : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {t0 r : Real} {v0 : PDE.Vec d} (hU : IsOpen U)
    (hs : MeasurableSet s) (hr : 0 < r) (hu : ContDiffOn Real 2 u U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) s U) (i : Fin d) :
    parabolicELpNormOn d (fun x => velocityGradient (pullbackScalar u t0 v0 r) x i) s =
      (‖r‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (fun x => velocityGradient u x i)
          (parabolicAffine t0 v0 r '' s) := by
  have heq : (fun x => velocityGradient (pullbackScalar u t0 v0 r) x i) =ᵐ[volume.restrict s]
      fun x => r * velocityGradient u (parabolicAffine t0 v0 r x) i := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hs]
    exact Eventually.of_forall fun x hx => by
      have h := congrFun (velocityGradient_pullbackScalar (q := u) (z := x)
        (t₀ := t0) (v₀ := v0) (r := r)
        ((hu.contDiffAt (hU.mem_nhds (hmap hx))).of_le (by norm_num))) i
      simpa only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] using h
  calc
    parabolicELpNormOn d (fun x => velocityGradient (pullbackScalar u t0 v0 r) x i) s =
        eLpNorm (fun x => r * velocityGradient u (parabolicAffine t0 v0 r x) i)
          (parabolicExponent d) (volume.restrict s) := eLpNorm_congr_ae heq
    _ = ‖r‖ₑ * parabolicELpNormOn d
        (pullbackScalar (fun x => velocityGradient u x i) t0 v0 r) s := by
      change eLpNorm (r • pullbackScalar (fun x => velocityGradient u x i) t0 v0 r)
        (parabolicExponent d) (volume.restrict s) = _
      rw [eLpNorm_const_smul]
      rfl
    _ = _ := by
      rw [parabolicELpNormOn_pullbackScalar t0 v0 hr]
      ac_rfl

private theorem parabolicELpNormOn_velocityHessian_pullbackScalar_local
    {d : Nat} {U s : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {t0 r : Real} {v0 : PDE.Vec d} (hU : IsOpen U)
    (hs : MeasurableSet s) (hr : 0 < r) (hu : ContDiffOn Real 2 u U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) s U) (i j : Fin d) :
    parabolicELpNormOn d
        (fun x => velocityHessian (pullbackScalar u t0 v0 r) x i j) s =
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r) *
        parabolicELpNormOn d (fun x => velocityHessian u x i j)
          (parabolicAffine t0 v0 r '' s) := by
  have heq : (fun x => velocityHessian (pullbackScalar u t0 v0 r) x i j) =ᵐ[volume.restrict s]
      fun x => r ^ 2 * velocityHessian u (parabolicAffine t0 v0 r x) i j := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hs]
    exact Eventually.of_forall fun x hx => by
      have h := congrFun (congrFun (velocityHessian_pullbackScalar (q := u) (z := x)
        (t₀ := t0) (v₀ := v0) (r := r) (hu.contDiffAt (hU.mem_nhds (hmap hx)))) i) j
      simpa only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] using h
  calc
    parabolicELpNormOn d
        (fun x => velocityHessian (pullbackScalar u t0 v0 r) x i j) s =
        eLpNorm (fun x => r ^ 2 * velocityHessian u (parabolicAffine t0 v0 r x) i j)
          (parabolicExponent d) (volume.restrict s) := eLpNorm_congr_ae heq
    _ = ‖r ^ 2‖ₑ * parabolicELpNormOn d
        (pullbackScalar (fun x => velocityHessian u x i j) t0 v0 r) s := by
      change eLpNorm ((r ^ 2) • pullbackScalar (fun x => velocityHessian u x i j) t0 v0 r)
        (parabolicExponent d) (volume.restrict s) = _
      rw [eLpNorm_const_smul]
      rfl
    _ = _ := by
      rw [parabolicELpNormOn_pullbackScalar t0 v0 hr]
      ac_rfl

private theorem parabolicLpNormOn_timeDerivative_pullbackScalar_local_finite
    {d : Nat} {U s : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {t0 r : Real} {v0 : PDE.Vec d} (hU : IsOpen U)
    (hs : MeasurableSet s) (hr : 0 < r) (hu : ContDiffOn Real 2 u U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) s U)
    (hfin : parabolicELpNormOn d (timeDerivative u)
      (parabolicAffine t0 v0 r '' s) ≠ ⊤) :
    parabolicELpNormOn d (timeDerivative (pullbackScalar u t0 v0 r)) s ≠ ⊤ ∧
      parabolicLpNormOn d (timeDerivative (pullbackScalar u t0 v0 r)) s =
        (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal *
          parabolicLpNormOn d (timeDerivative u) (parabolicAffine t0 v0 r '' s) := by
  have hscale := parabolicELpNormOn_timeDerivative_pullbackScalar_local
    hU hs hr hu hmap
  constructor
  · rw [hscale]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)) hfin
  · unfold parabolicLpNormOn
    rw [hscale, ENNReal.toReal_mul]

private theorem parabolicLpNormOn_velocityGradient_pullbackScalar_local_finite
    {d : Nat} {U s : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {t0 r : Real} {v0 : PDE.Vec d} (hU : IsOpen U)
    (hs : MeasurableSet s) (hr : 0 < r) (hu : ContDiffOn Real 2 u U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) s U) (i : Fin d)
    (hfin : parabolicELpNormOn d (fun x => velocityGradient u x i)
      (parabolicAffine t0 v0 r '' s) ≠ ⊤) :
    parabolicELpNormOn d (fun x => velocityGradient (pullbackScalar u t0 v0 r) x i) s ≠ ⊤ ∧
      parabolicLpNormOn d (fun x => velocityGradient (pullbackScalar u t0 v0 r) x i) s =
        (‖r‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal *
          parabolicLpNormOn d (fun x => velocityGradient u x i)
            (parabolicAffine t0 v0 r '' s) := by
  have hscale := parabolicELpNormOn_velocityGradient_pullbackScalar_local
    hU hs hr hu hmap i
  constructor
  · rw [hscale]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)) hfin
  · unfold parabolicLpNormOn
    rw [hscale, ENNReal.toReal_mul]

private theorem parabolicLpNormOn_velocityHessian_pullbackScalar_local_finite
    {d : Nat} {U s : Set (TimeVelocity d)} {u : TimeVelocity d -> Real}
    {t0 r : Real} {v0 : PDE.Vec d} (hU : IsOpen U)
    (hs : MeasurableSet s) (hr : 0 < r) (hu : ContDiffOn Real 2 u U)
    (hmap : MapsTo (parabolicAffine t0 v0 r) s U) (i j : Fin d)
    (hfin : parabolicELpNormOn d (fun x => velocityHessian u x i j)
      (parabolicAffine t0 v0 r '' s) ≠ ⊤) :
    parabolicELpNormOn d
        (fun x => velocityHessian (pullbackScalar u t0 v0 r) x i j) s ≠ ⊤ ∧
      parabolicLpNormOn d
          (fun x => velocityHessian (pullbackScalar u t0 v0 r) x i j) s =
        (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal *
          parabolicLpNormOn d (fun x => velocityHessian u x i j)
            (parabolicAffine t0 v0 r '' s) := by
  have hscale := parabolicELpNormOn_velocityHessian_pullbackScalar_local
    hU hs hr hu hmap i j
  constructor
  · rw [hscale]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)) hfin
  · unfold parabolicLpNormOn
    rw [hscale, ENNReal.toReal_mul]

private theorem mem_parabolicAffine_inner_box_iff
    {d : Nat} {t0 r : Real} {v0 : PDE.Vec d} (hr : 0 < r)
    (x : TimeVelocity d) :
    parabolicAffine (t0 - r ^ 2) v0 (2 * r) x ∈ parabolicBox 1 r t0 v0 ↔
      x ∈ parabolicBox 1 (1 / 2 : Real) (1 / 4 : Real) 0 := by
  rw [mem_parabolicBox_iff, mem_parabolicBox_iff]
  constructor
  · rintro ⟨ha, hb, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp [parabolicAffine] at ha
      nlinarith [sq_pos_of_pos hr]
    · dsimp [parabolicAffine] at hb
      nlinarith [sq_pos_of_pos hr]
    · intro i
      have hi := hv i
      dsimp [parabolicAffine] at hi
      rw [show v0 i + 2 * r * x.2 i - v0 i = (2 * r) * x.2 i by ring,
        abs_mul, abs_of_pos (by positivity : 0 < 2 * r)] at hi
      rw [Pi.zero_apply, sub_zero]
      nlinarith [abs_nonneg (x.2 i)]
  · rintro ⟨ha, hb, hv⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp [parabolicAffine]
      nlinarith [sq_pos_of_pos hr]
    · dsimp [parabolicAffine]
      nlinarith [sq_pos_of_pos hr]
    · intro i
      have hi := hv i
      dsimp [parabolicAffine]
      rw [show v0 i + 2 * r * x.2 i - v0 i = (2 * r) * x.2 i by ring,
        abs_mul, abs_of_pos (by positivity : 0 < 2 * r)]
      rw [Pi.zero_apply, sub_zero] at hi
      nlinarith [abs_nonneg (x.2 i)]

private theorem inner_box_subset_reference_collar (d : Nat) :
    parabolicBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0 ⊆
      parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0 := by
  intro x hx
  rcases mem_parabolicBox_iff.mp hx with ⟨ha, hb, hv⟩
  exact mem_parabolicClosedBox_iff.mpr ⟨ha.le, hb.le, fun i => (hv i).le⟩

private theorem inner_box_subset_reference_cell (d : Nat) :
    parabolicBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0 ⊆
      parabolicDyadicReferenceCell d := by
  intro x hx
  rcases mem_parabolicBox_iff.mp hx with ⟨ha, hb, hv⟩
  change x.1 ∈ Ioc (0 : Real) 1 ∧
    x.2 ∈ Set.univ.pi (fun _ : Fin d => Ioc (-1 : Real) 1)
  constructor
  · constructor <;> linarith
  · intro i _
    have hi := abs_lt.mp (by simpa only [Pi.zero_apply, sub_zero] using hv i)
    constructor <;> linarith

private theorem contDiff_cutoff_mul_of_contDiffOn
    {d : Nat} {eta q : TimeVelocity d -> Real} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (heta : ContDiff Real 2 eta) (hetaU : tsupport eta ⊆ U)
    (hq : ContDiffOn Real 2 q U) : ContDiff Real 2 (fun x => eta x * q x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact heta.contDiffAt.mul (hq.contDiffAt (hU.mem_nhds hx))
  · have hnot : x ∉ tsupport eta := fun h => hx (hetaU h)
    have hzero : eta =ᶠ[𝓝 x] fun _ : TimeVelocity d => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hz : (fun y : TimeVelocity d => eta y * q y) =ᶠ[𝓝 x]
        (fun _ : TimeVelocity d => (0 : Real)) := by
      filter_upwards [hzero] with y hy
      simp only [hy, zero_mul]
    exact (contDiff_const.contDiffAt.congr_of_eventuallyEq hz)

private theorem parabolic_pullback_factor_toReal (d : Nat) {r : Real} (hr : 0 < r) :
    (parabolicELpNormPullbackMeasureFactor d r).toReal =
      r ^ ((-(d : Real) - 2) / ((d : Real) + 1)) := by
  unfold parabolicELpNormPullbackMeasureFactor
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (pow_pos hr _).le), ENNReal.toReal_div, ENNReal.toReal_one]
  rw [show (parabolicExponent d).toReal = (d : Real) + 1 by
    unfold parabolicExponent
    have hcast : (d : ENNReal) + 1 = ((d + 1 : Nat) : ENNReal) := by norm_num
    rw [hcast, ENNReal.toReal_natCast]
    norm_num]
  rw [← Real.rpow_natCast, ← Real.rpow_neg hr.le, ← Real.rpow_mul hr.le]
  congr 1
  field_simp
  push_cast
  ring

private theorem parabolic_pullback_value_factor (d : Nat) {r : Real} (hr : 0 < r) :
    r⁻¹ ^ parabolicMorreyExponent d *
      (parabolicELpNormPullbackMeasureFactor d r).toReal = r ^ (-2 : Real) := by
  rw [parabolic_pullback_factor_toReal d hr]
  unfold parabolicMorreyExponent
  rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
  congr 1
  field_simp
  ring

private theorem parabolic_pullback_time_factor (d : Nat) {r : Real} (hr : 0 < r) :
    r⁻¹ ^ parabolicMorreyExponent d *
      (‖r ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal = 1 := by
  rw [ENNReal.toReal_mul, Real.enorm_of_nonneg (sq_nonneg r),
    ENNReal.toReal_ofReal (sq_nonneg r), parabolic_pullback_factor_toReal d hr]
  unfold parabolicMorreyExponent
  rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_natCast,
    ← mul_assoc, ← Real.rpow_add hr, ← Real.rpow_add hr]
  convert Real.rpow_zero r using 1
  field_simp
  push_cast
  ring_nf

private theorem parabolic_pullback_gradient_factor (d : Nat) {r : Real} (hr : 0 < r) :
    r⁻¹ ^ parabolicMorreyExponent d *
      (‖r‖ₑ * parabolicELpNormPullbackMeasureFactor d r).toReal = r⁻¹ := by
  rw [ENNReal.toReal_mul, Real.enorm_of_nonneg hr.le,
    ENNReal.toReal_ofReal hr.le, parabolic_pullback_factor_toReal d hr]
  unfold parabolicMorreyExponent
  rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
  calc
    r ^ (-((d : Real) / ((d : Real) + 1))) *
        (r * r ^ ((-(d : Real) - 2) / ((d : Real) + 1))) =
        r ^ (-((d : Real) / ((d : Real) + 1)))*
          (r ^ (1 : Real) * r ^ ((-(d : Real) - 2) / ((d : Real) + 1))) := by
          rw [Real.rpow_one]
    _ = r ^ (-1 : Real) := by
      rw [← mul_assoc, ← Real.rpow_add hr, ← Real.rpow_add hr]
      congr 1
      field_simp
      ring
    _ = r⁻¹ := by rw [Real.rpow_neg_one]

/-- Smooth local parabolic Holder control on a literal physical inner box,
obtained by a fixed reference collar cutoff. -/
theorem exists_parabolicMorreyPhysicalLocalHolderFullJetConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (t0 : Real) (v0 : PDE.Vec d) (r : Real), 0 < r ->
      ∀ (z : TimeVelocity d),
        z ∈ parabolicBox 1 r t0 v0 ->
      ∀ (w : TimeVelocity d),
        w ∈ parabolicBox 1 r t0 v0 ->
      ∀ u : TimeVelocity d -> Real,
        ContDiffOn Real 2 u (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0) ->
        ParabolicMemLpOn (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0)
          (parabolicExponent d) u ->
        ParabolicMemLpOn (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0)
          (parabolicExponent d) (timeDerivative u) ->
        (∀ i : Fin d, ParabolicMemLpOn
          (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0)
          (parabolicExponent d) (fun x => velocityGradient u x i)) ->
        (∀ i j : Fin d, ParabolicMemLpOn
          (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0)
          (parabolicExponent d) (fun x => velocityHessian u x i j)) ->
        |u z - u w| <=
          C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
            ((r ^ 2)⁻¹ * parabolicLpNormOn d u
                (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0) +
              parabolicLpNormOn d (timeDerivative u)
                (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0) +
              r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
                (fun x => velocityGradient u x i)
                (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0) +
              ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                (fun x => velocityHessian u x i j)
                (parabolicBox 1 (2 * r) (t0 - r ^ 2) v0)) := by
  obtain ⟨Cref, hCref, href⟩ := exists_parabolicMorreyReferenceHolderFullNormConst d hd
  obtain ⟨eta, Ceta, hCeta, heta, hetaCompact, hetaOne, hetaU, hcutoff⟩ :=
    exists_parabolicMorreyReferenceCollarCutoffJetConst d
  refine ⟨Cref * Ceta, mul_pos hCref hCeta, ?_⟩
  intro t0 v0 r hr z hz w hw u hu huMem hutMem hugMem huhMem
  let R : Real := 2 * r
  let tau : Real := t0 - r ^ 2
  let A : TimeVelocity d -> TimeVelocity d := parabolicAffine tau v0 R
  let U0 : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  let U : Set (TimeVelocity d) := parabolicBox 1 R tau v0
  let I0 : Set (TimeVelocity d) := parabolicBox 1 (1 / 2 : Real) (1 / 4 : Real) 0
  let q : TimeVelocity d -> Real := pullbackScalar u tau v0 R
  have hR : 0 < R := by dsimp [R]; positivity
  have hU0meas : MeasurableSet U0 := by
    dsimp [U0]
    exact measurableSet_parabolicBox 1 1 0 0
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_parabolicBox 1 R tau v0
  have hmap : MapsTo A U0 U := by
    dsimp [A, U0, U]
    exact mapsTo_parabolicAffine_parabolicBox hR
  have himage : A '' U0 = U := by
    dsimp [A, U0, U]
    exact parabolicAffine_image_parabolicBox hR
  have hq : ContDiffOn Real 2 q U0 := by
    dsimp [q, A]
    exact ContDiffOn.pullbackScalar hu hmap
  obtain ⟨zhat, hzhat⟩ := parabolicAffine_surjective (t₀ := tau) (v₀ := v0) hR z
  obtain ⟨what, hwhat⟩ := parabolicAffine_surjective (t₀ := tau) (v₀ := v0) hR w
  have hzhatI : zhat ∈ I0 := by
    dsimp [I0]
    apply (mem_parabolicAffine_inner_box_iff hr zhat).mp
    change parabolicAffine (t0 - r ^ 2) v0 (2 * r) zhat ∈ parabolicBox 1 r t0 v0
    have hzhat' : parabolicAffine (t0 - r ^ 2) v0 (2 * r) zhat = z := by
      simpa only [tau, R] using hzhat
    rw [hzhat']
    exact hz
  have hwhatI : what ∈ I0 := by
    dsimp [I0]
    apply (mem_parabolicAffine_inner_box_iff hr what).mp
    change parabolicAffine (t0 - r ^ 2) v0 (2 * r) what ∈ parabolicBox 1 r t0 v0
    have hwhat' : parabolicAffine (t0 - r ^ 2) v0 (2 * r) what = w := by
      simpa only [tau, R] using hwhat
    rw [hwhat']
    exact hw
  have hzhatK : zhat ∈ parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0 :=
    inner_box_subset_reference_collar d hzhatI
  have hwhatK : what ∈ parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0 :=
    inner_box_subset_reference_collar d hwhatI
  have hetaZ : eta zhat = 1 :=
    (eventually_nhdsSet_iff_forall.mp hetaOne zhat hzhatK).self_of_nhds
  have hetaW : eta what = 1 :=
    (eventually_nhdsSet_iff_forall.mp hetaOne what hwhatK).self_of_nhds
  have hzhatCell : zhat ∈ parabolicDyadicReferenceCell d :=
    inner_box_subset_reference_cell d hzhatI
  have hwhatCell : what ∈ parabolicDyadicReferenceCell d :=
    inner_box_subset_reference_cell d hwhatI
  have hdistOne : parabolicCoordinateDist zhat what <= 1 := by
    simpa using parabolicCoordinateDist_le_two_mul_radius_of_mem_parabolicClosedBox
      (1 / 4 : Real) (0 : PDE.Vec d) (by norm_num : 0 < (1 / 2 : Real)) hzhatK hwhatK
  have hg : ContDiff Real 2 (fun x => eta x * q x) :=
    contDiff_cutoff_mul_of_contDiffOn (isOpen_parabolicBox 1 1 0 0)
      (heta.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hetaU hq
  have hgCompact : HasCompactSupport (fun x => eta x * q x) := hetaCompact.mul_right
  have hfinValue : parabolicELpNormOn d u (A '' U0) ≠ ⊤ := by
    rw [himage]
    simpa only [U, R, tau, parabolicELpNormOn] using huMem.eLpNorm_ne_top
  have hfinTime : parabolicELpNormOn d (timeDerivative u) (A '' U0) ≠ ⊤ := by
    rw [himage]
    simpa only [U, R, tau, parabolicELpNormOn] using hutMem.eLpNorm_ne_top
  have hfinGrad (i : Fin d) : parabolicELpNormOn d
      (fun x => velocityGradient u x i) (A '' U0) ≠ ⊤ := by
    rw [himage]
    simpa only [U, R, tau, parabolicELpNormOn] using (hugMem i).eLpNorm_ne_top
  have hfinHess (i j : Fin d) : parabolicELpNormOn d
      (fun x => velocityHessian u x i j) (A '' U0) ≠ ⊤ := by
    rw [himage]
    simpa only [U, R, tau, parabolicELpNormOn] using (huhMem i j).eLpNorm_ne_top
  obtain ⟨hqValueFin, hqValue⟩ :=
    parabolicLpNormOn_pullbackScalar_finite tau v0 hR u U0 hfinValue
  obtain ⟨hqTimeFin, hqTime⟩ :=
    parabolicLpNormOn_timeDerivative_pullbackScalar_local_finite hUopen hU0meas hR hu hmap
      hfinTime
  have hqGradFin (i : Fin d) :=
    parabolicLpNormOn_velocityGradient_pullbackScalar_local_finite hUopen hU0meas hR hu hmap i
      (hfinGrad i)
  have hqHessFin (i j : Fin d) :=
    parabolicLpNormOn_velocityHessian_pullbackScalar_local_finite hUopen hU0meas hR hu hmap i j
      (hfinHess i j)
  have hU0open : IsOpen U0 := by
    dsimp [U0]
    exact isOpen_parabolicBox 1 1 0 0
  have hD1 : ContDiffOn Real 1 (fderiv Real q) U0 :=
    hq.fderiv_of_isOpen hU0open (by norm_num)
  have hD2 : ContDiffOn Real 0 (fderiv Real (fderiv Real q)) U0 :=
    hD1.fderiv_of_isOpen hU0open (by norm_num)
  have hqTimeCont : ContinuousOn (timeDerivative q) U0 := by
    unfold timeDerivative
    simpa using hD1.continuousOn.clm_apply continuousOn_const
  have hqGradCont (i : Fin d) : ContinuousOn (fun x => velocityGradient q x i) U0 := by
    unfold velocityGradient
    simpa using hD1.continuousOn.clm_apply continuousOn_const
  have hqHessCont (i j : Fin d) : ContinuousOn (fun x => velocityHessian q x i j) U0 := by
    unfold velocityHessian
    simpa using hD2.continuousOn.clm_apply continuousOn_const |>.clm_apply continuousOn_const
  have hqMem : ParabolicMemLpOn U0 (parabolicExponent d) q :=
    lt_top_iff_ne_top.mpr hqValueFin
  have hqTimeMem : ParabolicMemLpOn U0 (parabolicExponent d) (timeDerivative q) :=
    lt_top_iff_ne_top.mpr hqTimeFin
  have hqGradMem (i : Fin d) : ParabolicMemLpOn U0 (parabolicExponent d)
      (fun x => velocityGradient q x i) :=
    lt_top_iff_ne_top.mpr (hqGradFin i).1
  have hqHessMem (i j : Fin d) : ParabolicMemLpOn U0 (parabolicExponent d)
      (fun x => velocityHessian q x i j) :=
    lt_top_iff_ne_top.mpr (hqHessFin i j).1
  have hjet := hcutoff q hq hqMem hqTimeMem hqGradMem hqHessMem
  have hholder := href zhat hzhatCell what hwhatCell hdistOne
    (fun x => eta x * q x) hg hgCompact
  have hdist : parabolicCoordinateDist zhat what =
      R⁻¹ * parabolicCoordinateDist z w := by
    rw [← hzhat, ← hwhat, parabolicCoordinateDist_parabolicAffine,
      abs_of_pos hR]
    field_simp [hR.ne']
  have hvalueScaled : R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d q U0 =
      R ^ (-2 : Real) * parabolicLpNormOn d u U := by
    rw [hqValue, himage]
    calc
      R⁻¹ ^ parabolicMorreyExponent d *
          ((parabolicELpNormPullbackMeasureFactor d R).toReal * parabolicLpNormOn d u U) =
          (R⁻¹ ^ parabolicMorreyExponent d *
            (parabolicELpNormPullbackMeasureFactor d R).toReal) * parabolicLpNormOn d u U := by ring
      _ = _ := by rw [parabolic_pullback_value_factor d hR]
  have htimeScaled : R⁻¹ ^ parabolicMorreyExponent d *
      parabolicLpNormOn d (timeDerivative q) U0 = parabolicLpNormOn d (timeDerivative u) U := by
    rw [hqTime, himage]
    calc
      R⁻¹ ^ parabolicMorreyExponent d *
          ((‖R ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d R).toReal *
            parabolicLpNormOn d (timeDerivative u) U) =
          (R⁻¹ ^ parabolicMorreyExponent d *
            (‖R ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d R).toReal) *
              parabolicLpNormOn d (timeDerivative u) U := by ring
      _ = _ := by rw [parabolic_pullback_time_factor d hR, one_mul]
  have hgradScaled (i : Fin d) : R⁻¹ ^ parabolicMorreyExponent d *
      parabolicLpNormOn d (fun x => velocityGradient q x i) U0 =
        R⁻¹ * parabolicLpNormOn d (fun x => velocityGradient u x i) U := by
    rw [(hqGradFin i).2, himage]
    calc
      R⁻¹ ^ parabolicMorreyExponent d *
          ((‖R‖ₑ * parabolicELpNormPullbackMeasureFactor d R).toReal *
            parabolicLpNormOn d (fun x => velocityGradient u x i) U) =
          (R⁻¹ ^ parabolicMorreyExponent d *
            (‖R‖ₑ * parabolicELpNormPullbackMeasureFactor d R).toReal) *
              parabolicLpNormOn d (fun x => velocityGradient u x i) U := by ring
      _ = _ := by rw [parabolic_pullback_gradient_factor d hR]
  have hhessScaled (i j : Fin d) : R⁻¹ ^ parabolicMorreyExponent d *
      parabolicLpNormOn d (fun x => velocityHessian q x i j) U0 =
        parabolicLpNormOn d (fun x => velocityHessian u x i j) U := by
    rw [(hqHessFin i j).2, himage]
    calc
      R⁻¹ ^ parabolicMorreyExponent d *
          ((‖R ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d R).toReal *
            parabolicLpNormOn d (fun x => velocityHessian u x i j) U) =
          (R⁻¹ ^ parabolicMorreyExponent d *
            (‖R ^ 2‖ₑ * parabolicELpNormPullbackMeasureFactor d R).toReal) *
              parabolicLpNormOn d (fun x => velocityHessian u x i j) U := by ring
      _ = _ := by rw [parabolic_pullback_time_factor d hR, one_mul]
  let S : Real := parabolicLpNormOn d q U0 + parabolicLpNormOn d (timeDerivative q) U0 +
    ∑ i : Fin d, parabolicLpNormOn d (fun x => velocityGradient q x i) U0 +
      ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
        (fun x => velocityHessian q x i j) U0
  let PR : Real := R ^ (-2 : Real) * parabolicLpNormOn d u U +
    parabolicLpNormOn d (timeDerivative u) U +
      R⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
        (fun x => velocityGradient u x i) U +
      ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
        (fun x => velocityHessian u x i j) U
  have hS : R⁻¹ ^ parabolicMorreyExponent d * S = PR := by
    dsimp [S, PR]
    calc
      R⁻¹ ^ parabolicMorreyExponent d *
          (parabolicLpNormOn d q U0 + parabolicLpNormOn d (timeDerivative q) U0 +
            ∑ i : Fin d, parabolicLpNormOn d (fun x => velocityGradient q x i) U0 +
              ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                (fun x => velocityHessian q x i j) U0) =
          R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d q U0 +
            R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d (timeDerivative q) U0 +
              R⁻¹ ^ parabolicMorreyExponent d * ∑ i : Fin d, parabolicLpNormOn d
                (fun x => velocityGradient q x i) U0 +
                R⁻¹ ^ parabolicMorreyExponent d * ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                  (fun x => velocityHessian q x i j) U0 := by ring
      _ = R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d q U0 +
            R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d (timeDerivative q) U0 +
              ∑ i : Fin d, R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d
                (fun x => velocityGradient q x i) U0 +
                ∑ i : Fin d, ∑ j : Fin d, R⁻¹ ^ parabolicMorreyExponent d * parabolicLpNormOn d
                  (fun x => velocityHessian q x i j) U0 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
    rw [hvalueScaled, htimeScaled]
    simp_rw [hgradScaled, hhessScaled]
    rw [← Finset.mul_sum]
  let P : Real := (r ^ 2)⁻¹ * parabolicLpNormOn d u U +
    parabolicLpNormOn d (timeDerivative u) U +
      r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
        (fun x => velocityGradient u x i) U +
      ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
        (fun x => velocityHessian u x i j) U
  have hRinv : R⁻¹ = (1 / 2 : Real) * r⁻¹ := by
    dsimp [R]
    field_simp [hr.ne']
  have hRinvTwo : R ^ (-2 : Real) = (1 / 4 : Real) * r ^ (-2 : Real) := by
    dsimp [R]
    rw [Real.rpow_neg (mul_nonneg (by norm_num) hr.le), Real.rpow_neg hr.le]
    norm_num [pow_two]
    field_simp [hr.ne']
    norm_num
  have hrpow : r ^ (-2 : Real) = (r ^ 2)⁻¹ := by
    rw [Real.rpow_neg hr.le]
    exact congrArg Inv.inv (Real.rpow_natCast r 2)
  have hPR : PR <= P := by
    dsimp [PR, P]
    rw [hRinv, hRinvTwo, hrpow]
    have hvalueNonneg : 0 <= (r ^ 2)⁻¹ * parabolicLpNormOn d u U :=
      mul_nonneg (inv_nonneg.mpr (sq_nonneg r)) ENNReal.toReal_nonneg
    have hgradSumNonneg : 0 <= ∑ i : Fin d, parabolicLpNormOn d
        (fun x => velocityGradient u x i) U := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hgradNonneg : 0 <= r⁻¹ * ∑ i : Fin d, parabolicLpNormOn d
        (fun x => velocityGradient u x i) U := mul_nonneg (inv_nonneg.mpr hr.le) hgradSumNonneg
    nlinarith
  have hjetScaled : R⁻¹ ^ parabolicMorreyExponent d *
      parabolicSmoothJetLpNorm d (fun x => eta x * q x) <= Ceta * P := by
    calc
      R⁻¹ ^ parabolicMorreyExponent d * parabolicSmoothJetLpNorm d (fun x => eta x * q x) <=
          R⁻¹ ^ parabolicMorreyExponent d * (Ceta * S) := by
            apply mul_le_mul_of_nonneg_left
            · simpa only [S] using hjet
            · exact Real.rpow_nonneg (inv_nonneg.mpr hR.le) _
      _ = Ceta * (R⁻¹ ^ parabolicMorreyExponent d * S) := by ring
      _ = Ceta * PR := by rw [hS]
      _ <= Ceta * P := mul_le_mul_of_nonneg_left hPR hCeta.le
  have hleft : |u z - u w| = |(fun x => eta x * q x) zhat -
      (fun x => eta x * q x) what| := by
    simp only [q, pullbackScalar_apply, hetaZ, hetaW, hzhat, hwhat, one_mul]
  rw [hleft]
  calc
    |(fun x => eta x * q x) zhat - (fun x => eta x * q x) what| <=
        Cref * (parabolicCoordinateDist zhat what) ^ parabolicMorreyExponent d *
          parabolicSmoothJetLpNorm d (fun x => eta x * q x) := hholder
    _ = Cref * (R⁻¹ ^ parabolicMorreyExponent d *
        (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d) *
          parabolicSmoothJetLpNorm d (fun x => eta x * q x) := by
      rw [hdist, Real.mul_rpow (inv_nonneg.mpr hR.le)
        (parabolicCoordinateDist_nonneg z w)]
    _ = Cref * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
        (R⁻¹ ^ parabolicMorreyExponent d *
          parabolicSmoothJetLpNorm d (fun x => eta x * q x)) := by ring
    _ <= Cref * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d * (Ceta * P) := by
      apply mul_le_mul_of_nonneg_left hjetScaled
      exact mul_nonneg hCref.le (Real.rpow_nonneg (parabolicCoordinateDist_nonneg z w) _)
    _ = (Cref * Ceta) * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d * P := by
      ring
    _ = _ := by
      dsimp [P, U, R, tau]

end HypoellipticAleksandrov.Parabolic
