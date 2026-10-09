module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff

/-!
This module fixes a normalized reference collar cutoff and derives its exact
selected-jet product estimate from the four restricted-component `MemLp`
certificates. It proves no Hölder, PDE, or representative theorem.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- The literal closed reference collar is contained in the open unit source box. -/
private theorem reference_closed_collar_subset_unit_box (d : Nat) :
    parabolicClosedBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0 ⊆
      parabolicBox (d := d) 1 1 0 0 := by
  rintro ⟨t, v⟩ hz
  rw [mem_parabolicClosedBox_iff] at hz
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · norm_num at hz ⊢
    linarith
  · norm_num at hz ⊢
    linarith
  · intro i
    simpa only [Pi.zero_apply, sub_zero] using lt_of_le_of_lt (hz.2.2 i) (by norm_num)

/-- The closed unit coordinate box contains the closure of the open unit source box. -/
private theorem closure_reference_unit_box_subset_closed (d : Nat) :
    closure (parabolicBox (d := d) 1 1 0 (0 : PDE.Vec d)) ⊆
      parabolicClosedBox (d := d) 1 1 0 0 := by
  refine closure_minimal ?_ (isClosed_parabolicClosedBox 1 1 0 0)
  rintro ⟨t, v⟩ hz
  rw [mem_parabolicBox_iff] at hz
  rw [mem_parabolicClosedBox_iff]
  exact ⟨hz.1.le, hz.2.1.le, fun i => (hz.2.2 i).le⟩

/-- The open unit source box has compact closure. -/
private theorem isCompact_closure_reference_unit_box (d : Nat) :
    IsCompact (closure (parabolicBox (d := d) 1 1 0 (0 : PDE.Vec d))) := by
  exact IsCompact.of_isClosed_subset (isCompact_parabolicClosedBox 1 1 0 0)
    isClosed_closure (closure_reference_unit_box_subset_closed d)

/-- The literal time derivative of a cutoff product, valid also outside the
locality set because the cutoff is zero on a neighbourhood there. -/
private theorem timeDerivative_cutoff_mul
    {d : Nat} {U : Set (TimeVelocity d)} {eta q : TimeVelocity d → Real}
    (hU : IsOpen U) (heta : ContDiff Real 2 eta) (hetaU : tsupport eta ⊆ U)
    (hq : ContDiffOn Real 2 q U) (z : TimeVelocity d) :
    timeDerivative (fun y => eta y * q y) z =
      eta z * timeDerivative q z + q z * timeDerivative eta z := by
  by_cases hz : z ∈ U
  · unfold timeDerivative
    change (fderiv Real (eta * q) z) (1, 0) = _
    rw [fderiv_mul (heta.differentiable (by norm_num) z)
      ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  · have hnot : z ∉ tsupport eta := fun hzeta => hz (hetaU hzeta)
    have hzero : eta =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : Real) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hproduct : (fun y => eta y * q y) =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : Real) := by
      filter_upwards [hzero] with y hy
      simp [hy]
    have heta_zero : eta z = 0 := hzero.self_of_nhds
    have htime_eta : timeDerivative eta z = 0 := by
      unfold timeDerivative
      rw [hzero.fderiv_eq]
      simp
    have htime_product : timeDerivative (fun y => eta y * q y) z = 0 := by
      unfold timeDerivative
      rw [hproduct.fderiv_eq]
      simp
    rw [htime_product, heta_zero, htime_eta]
    ring

/-- The literal velocity-gradient product rule for a locally smooth scalar
and a compact cutoff. -/
private theorem velocityGradient_cutoff_mul
    {d : Nat} {U : Set (TimeVelocity d)} {eta q : TimeVelocity d → Real}
    (hU : IsOpen U) (heta : ContDiff Real 2 eta) (hetaU : tsupport eta ⊆ U)
    (hq : ContDiffOn Real 2 q U) (z : TimeVelocity d) (i : Fin d) :
    velocityGradient (fun y => eta y * q y) z i =
      eta z * velocityGradient q z i + q z * velocityGradient eta z i := by
  by_cases hz : z ∈ U
  · unfold velocityGradient
    change (fderiv Real (eta * q) z) (0, Pi.single i 1) = _
    rw [fderiv_mul (heta.differentiable (by norm_num) z)
      ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  · have hnot : z ∉ tsupport eta := fun hzeta => hz (hetaU hzeta)
    have hzero : eta =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : Real) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hproduct : (fun y => eta y * q y) =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : Real) := by
      filter_upwards [hzero] with y hy
      simp [hy]
    have heta_zero : eta z = 0 := hzero.self_of_nhds
    have hgrad_eta : velocityGradient eta z i = 0 := by
      unfold velocityGradient
      rw [hzero.fderiv_eq]
      simp
    have hgrad_product : velocityGradient (fun y => eta y * q y) z i = 0 := by
      unfold velocityGradient
      rw [hproduct.fderiv_eq]
      simp
    rw [hgrad_product, heta_zero, hgrad_eta]
    ring

/-- The ordered velocity-Hessian product formula for a compact cutoff and a
locally `C²` scalar.  The middle terms have the project-wide `(i,j)`
orientation. -/
private theorem velocityHessian_cutoff_mul
    {d : Nat} {U : Set (TimeVelocity d)} {eta q : TimeVelocity d → Real}
    (hU : IsOpen U) (heta : ContDiff Real 2 eta) (hetaU : tsupport eta ⊆ U)
    (hq : ContDiffOn Real 2 q U) (z : TimeVelocity d) (i j : Fin d) :
    velocityHessian (fun y => eta y * q y) z i j =
      eta z * velocityHessian q z i j + velocityGradient eta z j * velocityGradient q z i +
        velocityGradient q z j * velocityGradient eta z i +
          q z * velocityHessian eta z i j := by
  have hproduct_cont : ContDiff Real 2 (fun y => eta y * q y) :=
    contDiff_cutoff_mul_of_tsupport_subset hU heta hetaU hq
  by_cases hz : z ∈ U
  · have heta_at : ContDiffAt Real 2 eta z := heta.contDiffAt
    have hq_at : ContDiffAt Real 2 q z := hq.contDiffAt (hU.mem_nhds hz)
    have heta_diff : DifferentiableAt Real eta z := heta_at.differentiableAt (by norm_num)
    have hq_diff : DifferentiableAt Real q z := hq_at.differentiableAt (by norm_num)
    have heta_deriv_diff : DifferentiableAt Real (fderiv Real eta) z :=
      (heta_at.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hq_deriv_diff : DifferentiableAt Real (fderiv Real q) z :=
      (hq_at.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hq_near : ∀ᶠ y in 𝓝 z, ContDiffAt Real 2 q y :=
      hq_at.eventually (by norm_num)
    have hfirst : fderiv Real (eta * q) =ᶠ[𝓝 z]
        fun y => eta y • fderiv Real q y + q y • fderiv Real eta y := by
      filter_upwards [hq_near] with y hy
      rw [fderiv_mul (heta.differentiable (by norm_num) y)
        (hy.differentiableAt (by norm_num))]
    have hsecond : fderiv Real (fderiv Real (eta * q)) z =
        eta z • fderiv Real (fderiv Real q) z +
          (fderiv Real eta z).smulRight (fderiv Real q z) +
            q z • fderiv Real (fderiv Real eta) z +
              (fderiv Real q z).smulRight (fderiv Real eta z) := by
      calc
        fderiv Real (fderiv Real (eta * q)) z =
            fderiv Real (fun y => eta y • fderiv Real q y +
              q y • fderiv Real eta y) z := hfirst.fderiv_eq
        _ = fderiv Real (fun y => eta y • fderiv Real q y) z +
            fderiv Real (fun y => q y • fderiv Real eta y) z := by
              change fderiv Real ((fun y => eta y • fderiv Real q y) +
                fun y => q y • fderiv Real eta y) z = _
              exact fderiv_add (heta_diff.smul hq_deriv_diff)
                (hq_diff.smul heta_deriv_diff)
        _ = _ := by
              change fderiv Real (eta • fderiv Real q) z +
                fderiv Real (q • fderiv Real eta) z = _
              rw [fderiv_smul heta_diff hq_deriv_diff,
                fderiv_smul hq_diff heta_deriv_diff]
              ac_rfl
    have hproduct_symm := velocityHessian_isSymm hproduct_cont z
    have hq_symm := (hq_at.isSymmSndFDerivAt (by norm_num)).eq
      ((0 : Real), Pi.single j 1) ((0 : Real), Pi.single i 1)
    have heta_symm := (heta_at.isSymmSndFDerivAt (by norm_num)).eq
      ((0 : Real), Pi.single j 1) ((0 : Real), Pi.single i 1)
    have heval := congrArg (fun H : TimeVelocity d →L[Real]
        TimeVelocity d →L[Real] Real => H ((0, Pi.single j 1) : TimeVelocity d)
          ((0, Pi.single i 1) : TimeVelocity d)) hsecond
    calc
      velocityHessian (fun y => eta y * q y) z i j =
          velocityHessian (fun y => eta y * q y) z j i := hproduct_symm.apply j i
      _ = eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j := by
        change (fderiv Real (fderiv Real (eta * q)) z)
            ((0, Pi.single j 1) : TimeVelocity d) ((0, Pi.single i 1) : TimeVelocity d) = _
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply, smul_eq_mul] at heval
        have heval' :
            (fderiv Real (fderiv Real (eta * q)) z)
                ((0, Pi.single j 1) : TimeVelocity d) ((0, Pi.single i 1) : TimeVelocity d) =
              eta z * (fderiv Real (fderiv Real q) z)
                  ((0, Pi.single i 1) : TimeVelocity d) ((0, Pi.single j 1) : TimeVelocity d) +
                (fderiv Real eta z) ((0, Pi.single j 1) : TimeVelocity d) *
                    (fderiv Real q z) ((0, Pi.single i 1) : TimeVelocity d) +
                  (fderiv Real q z) ((0, Pi.single j 1) : TimeVelocity d) *
                    (fderiv Real eta z) ((0, Pi.single i 1) : TimeVelocity d) +
                      q z * (fderiv Real (fderiv Real eta) z)
                        ((0, Pi.single i 1) : TimeVelocity d)
                        ((0, Pi.single j 1) : TimeVelocity d) := by
          rw [heval, hq_symm, heta_symm]
          ring
        simpa only [velocityHessian, velocityGradient] using heval'
  · have hnot : z ∉ tsupport eta := fun hzeta => hz (hetaU hzeta)
    have hzero : eta =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : Real) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hproduct : (fun y => eta y * q y) =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : Real) := by
      filter_upwards [hzero] with y hy
      simp [hy]
    have heta_zero : eta z = 0 := hzero.self_of_nhds
    have hgrad_eta : velocityGradient eta z = 0 := by
      funext k
      unfold velocityGradient
      rw [hzero.fderiv_eq]
      simp
    have hhess_eta : velocityHessian eta z = 0 := by
      ext k l
      unfold velocityHessian
      rw [hzero.fderiv.fderiv_eq, fderiv_fun_const]
      simp
    have hhess_product : velocityHessian (fun y => eta y * q y) z = 0 := by
      ext k l
      unfold velocityHessian
      rw [hproduct.fderiv.fderiv_eq, fderiv_fun_const]
      simp
    rw [hhess_product, heta_zero, hgrad_eta, hhess_eta]
    simp only [Pi.zero_apply, Matrix.zero_apply]
    ring

private theorem timeDerivative_cutoff_continuous {d : Nat} {eta : TimeVelocity d → Real}
    (heta : ContDiff Real 2 eta) : Continuous (timeDerivative eta) := by
  unfold timeDerivative
  exact ((heta.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem timeDerivative_cutoff_hasCompactSupport {d : Nat} {eta : TimeVelocity d → Real}
    (heta : HasCompactSupport eta) : HasCompactSupport (timeDerivative eta) := by
  unfold timeDerivative
  simpa using heta.fderiv_apply (𝕜 := Real) ((1, 0) : TimeVelocity d)

private theorem velocityGradient_cutoff_continuous {d : Nat} {eta : TimeVelocity d → Real}
    {i : Fin d} (heta : ContDiff Real 2 eta) :
    Continuous (fun z => velocityGradient eta z i) := by
  unfold velocityGradient
  exact ((heta.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem velocityGradient_cutoff_hasCompactSupport
    {d : Nat} {eta : TimeVelocity d → Real} {i : Fin d}
    (heta : HasCompactSupport eta) :
    HasCompactSupport (fun z => velocityGradient eta z i) := by
  unfold velocityGradient
  simpa using heta.fderiv_apply (𝕜 := Real) ((0, Pi.single i 1) : TimeVelocity d)

private theorem velocityHessian_cutoff_continuous {d : Nat} {eta : TimeVelocity d → Real}
    {i j : Fin d} (heta : ContDiff Real 2 eta) :
    Continuous (fun z => velocityHessian eta z i j) := by
  unfold velocityHessian
  have hfirst : ContDiff Real 1 (fderiv Real eta) :=
    heta.fderiv_right (m := 1) (by norm_num)
  simpa using (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
    continuous_const

private theorem velocityHessian_cutoff_hasCompactSupport
    {d : Nat} {eta : TimeVelocity d → Real} {i j : Fin d}
    (heta : HasCompactSupport eta) :
    HasCompactSupport (fun z => velocityHessian eta z i j) := by
  unfold velocityHessian
  have hfirst : HasCompactSupport (fderiv Real eta) := heta.fderiv Real
  have hsecond : HasCompactSupport (fderiv Real (fderiv Real eta)) := hfirst.fderiv Real
  simpa only [Function.comp_def] using hsecond.comp_left
    (g := fun H : TimeVelocity d →L[Real] TimeVelocity d →L[Real] Real =>
      H ((0, Pi.single i 1) : TimeVelocity d) ((0, Pi.single j 1) : TimeVelocity d)) rfl

private theorem timeDerivative_tsupport_subset {d : Nat} (eta : TimeVelocity d → Real) :
    tsupport (timeDerivative eta) ⊆ tsupport eta := by
  unfold timeDerivative
  change closure (Function.support (fun z => fderiv Real eta z (1, 0))) ⊆ tsupport eta
  refine (closure_mono ?_).trans (tsupport_fderiv_subset Real)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityGradient_tsupport_subset {d : Nat} {i : Fin d}
    (eta : TimeVelocity d → Real) :
    tsupport (fun z => velocityGradient eta z i) ⊆ tsupport eta := by
  unfold velocityGradient
  change closure (Function.support (fun z => fderiv Real eta z (0, Pi.single i 1))) ⊆ tsupport eta
  refine (closure_mono ?_).trans (tsupport_fderiv_subset Real)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityHessian_tsupport_subset {d : Nat} {i j : Fin d}
    (eta : TimeVelocity d → Real) :
    tsupport (fun z => velocityHessian eta z i j) ⊆ tsupport eta := by
  unfold velocityHessian
  have hfirst : tsupport (fderiv Real eta) ⊆ tsupport eta := tsupport_fderiv_subset Real
  have hsecond : tsupport (fderiv Real (fderiv Real eta)) ⊆ tsupport (fderiv Real eta) :=
    tsupport_fderiv_subset Real
  change closure (Function.support (fun z =>
    fderiv Real (fderiv Real eta) z (0, Pi.single i 1) (0, Pi.single j 1))) ⊆ tsupport eta
  refine (closure_mono ?_).trans (hsecond.trans hfirst)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

/-- A bounded cutoff supported in `U` multiplies a locally finite `Lᵖ`
function with the corresponding restricted-norm bound. -/
private theorem eLpNorm_cutoff_mul_le
    {d : Nat} {U : Set (TimeVelocity d)} {p : ENNReal}
    {a f : TimeVelocity d → Real}
    (haf : AEStronglyMeasurable (fun z => a z * f z) volume)
    (hU : MeasurableSet U) (haU : tsupport a ⊆ U)
    {B : Real} (hB : ∀ z, ‖a z‖ ≤ B) :
    eLpNorm (fun z => a z * f z) p volume ≤
      ENNReal.ofReal B * eLpNorm f p (volume.restrict U) := by
  have hzero : ∀ z ∉ U, a z = 0 := by
    intro z hz
    have hnot : z ∉ tsupport a := fun hza => hz (haU hza)
    exact (notMem_tsupport_iff_eventuallyEq.mp hnot).self_of_nhds
  have hproduct : (fun z => a z * f z) = fun z => a z * U.indicator f z := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hzero z hz]
  rw [hproduct]
  calc
    eLpNorm (fun z => a z * U.indicator f z) p volume ≤
        ENNReal.ofReal B * eLpNorm (U.indicator f) p volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hproduct ▸ haf) _ p
      filter_upwards [] with z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
    _ = ENNReal.ofReal B * eLpNorm f p (volume.restrict U) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hU]

private theorem memLp_cutoff_mul
    {d : Nat} {U : Set (TimeVelocity d)} {p : ENNReal}
    {a f : TimeVelocity d → Real} (hU : MeasurableSet U) (ha : Continuous a)
    (haCompact : HasCompactSupport a) (haU : tsupport a ⊆ U)
    (hf : MemLp f p (volume.restrict U)) :
    MemLp (fun z => a z * f z) p volume := by
  have hzero : ∀ z ∉ U, a z = 0 := by
    intro z hz
    have hnot : z ∉ tsupport a := fun hza => hz (haU hza)
    exact (notMem_tsupport_iff_eventuallyEq.mp hnot).self_of_nhds
  have hproduct : (fun z => a z * f z) = fun z => a z * U.indicator f z := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hzero z hz]
  rw [hproduct]
  have ha_top : MemLp a ∞ volume := ha.memLp_of_hasCompactSupport haCompact
  have hf_indicator : MemLp (U.indicator f) p volume :=
    (memLp_indicator_iff_restrict hU).mpr hf
  simpa only [mul_comm] using hf_indicator.mul' ha_top

/-- The fixed normalized collar admits the smooth compact cutoff required for
the later quantitative product estimate. -/
private theorem exists_reference_collar_cutoff (d : Nat) :
    ∃ eta : TimeVelocity d → Real,
      ContDiff Real (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
        (∀ᶠ z in 𝓝ˢ
          (parabolicClosedBox (d := d) 1 (1 / 2 : Real) (1 / 4 : Real) 0), eta z = 1) ∧
          tsupport eta ⊆ parabolicBox (d := d) 1 1 0 0 := by
  let K : Set (TimeVelocity d) := parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0
  let U : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  obtain ⟨eta, heta, heta_one, hetaU⟩ := exists_smooth_cutoff_tsupport_subset
    (isCompact_parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0)
    (isOpen_parabolicBox 1 1 0 0) (reference_closed_collar_subset_unit_box d)
  refine ⟨eta, heta, ?_, heta_one, hetaU⟩
  exact hasCompactSupport_of_tsupport_subset_of_isCompact_closure hetaU
    (isCompact_closure_reference_unit_box d)

private theorem cutoff_uniform_bound {d : Nat} {a : TimeVelocity d → Real}
    (ha : Continuous a) (haCompact : HasCompactSupport a) :
    ∃ B : Real, 0 ≤ B ∧ ∀ z, ‖a z‖ ≤ B := by
  obtain ⟨B, hB⟩ := ha.bounded_above_of_compact_support haCompact
  refine ⟨max 0 B, le_max_left _ _, fun z => (hB z).trans (le_max_right _ _)⟩

private theorem parabolicExponent_one_le (d : Nat) :
    (1 : ENNReal) ≤ parabolicExponent d := by
  unfold parabolicExponent
  exact le_add_of_nonneg_left bot_le

private theorem eLpNorm_cutoff_mul_le_of_bound_le
    {d : Nat} {U : Set (TimeVelocity d)} {p : ENNReal}
    {a f : TimeVelocity d → Real}
    (haf : AEStronglyMeasurable (fun z => a z * f z) volume)
    (hU : MeasurableSet U) (haU : tsupport a ⊆ U)
    {B M : Real} (hB : ∀ z, ‖a z‖ ≤ B) (hBM : B ≤ M) :
    eLpNorm (fun z => a z * f z) p volume ≤
      ENNReal.ofReal M * eLpNorm f p (volume.restrict U) := by
  calc
    eLpNorm (fun z => a z * f z) p volume ≤
        ENNReal.ofReal B * eLpNorm f p (volume.restrict U) :=
      eLpNorm_cutoff_mul_le haf hU haU hB
    _ ≤ ENNReal.ofReal M * eLpNorm f p (volume.restrict U) := by
      gcongr

/-- The normalized reference collar cutoff has a selected-jet product bound
against the literal unit source box. -/
theorem exists_parabolicMorreyReferenceCollarCutoffJetConst (d : Nat) :
    ∃ eta : TimeVelocity d -> Real, ∃ C : Real, 0 < C ∧
      ContDiff Real (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
      (∀ᶠ z in 𝓝ˢ
        (parabolicClosedBox 1 (1 / 2 : Real) (1 / 4 : Real) 0), eta z = 1) ∧
      tsupport eta ⊆ parabolicBox 1 1 0 0 ∧
      ∀ q : TimeVelocity d -> Real,
        ContDiffOn Real 2 q (parabolicBox 1 1 0 0) ->
        ParabolicMemLpOn (parabolicBox 1 1 0 0) (parabolicExponent d) q ->
        ParabolicMemLpOn (parabolicBox 1 1 0 0) (parabolicExponent d)
          (timeDerivative q) ->
        (∀ i : Fin d, ParabolicMemLpOn (parabolicBox 1 1 0 0)
          (parabolicExponent d) (fun z => velocityGradient q z i)) ->
        (∀ i j : Fin d, ParabolicMemLpOn (parabolicBox 1 1 0 0)
          (parabolicExponent d) (fun z => velocityHessian q z i j)) ->
        parabolicSmoothJetLpNorm d (fun z => eta z * q z) <=
          C * (parabolicLpNormOn d q (parabolicBox 1 1 0 0) +
               parabolicLpNormOn d (timeDerivative q) (parabolicBox 1 1 0 0) +
               ∑ i : Fin d, parabolicLpNormOn d
                 (fun z => velocityGradient q z i) (parabolicBox 1 1 0 0) +
               ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
                 (fun z => velocityHessian q z i j) (parabolicBox 1 1 0 0)) := by
  let U : Set (TimeVelocity d) := parabolicBox 1 1 0 0
  obtain ⟨eta, heta, hetaCompact, heta_one, hetaU⟩ := exists_reference_collar_cutoff d
  have heta₂ : ContDiff Real 2 eta := heta.of_le (by
    exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨B₀, hB₀nonneg, hB₀⟩ := cutoff_uniform_bound heta.continuous hetaCompact
  obtain ⟨Bt, hBtnonneg, hBt⟩ := cutoff_uniform_bound
    (timeDerivative_cutoff_continuous heta₂)
    (timeDerivative_cutoff_hasCompactSupport hetaCompact)
  choose Bg hBgnonneg hBg using fun i : Fin d => cutoff_uniform_bound
    (velocityGradient_cutoff_continuous heta₂)
    (velocityGradient_cutoff_hasCompactSupport hetaCompact)
  choose Bh hBhnonneg hBh using fun i : Fin d => fun j : Fin d => cutoff_uniform_bound
    (velocityHessian_cutoff_continuous heta₂)
    (velocityHessian_cutoff_hasCompactSupport hetaCompact)
  let M : Real := 1 + B₀ + Bt + ∑ i : Fin d, Bg i + ∑ i : Fin d, ∑ j : Fin d, Bh i j
  have hBgSum : 0 ≤ ∑ i : Fin d, Bg i :=
    Finset.sum_nonneg fun i _ => hBgnonneg i
  have hBhSum : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, Bh i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hBhnonneg i j
  have hMpos : 0 < M := by
    dsimp [M]
    linarith
  have hB₀M : B₀ ≤ M := by
    dsimp [M]
    have : 0 ≤ Bt + ∑ i : Fin d, Bg i + ∑ i : Fin d, ∑ j : Fin d, Bh i j := by
      linarith
    linarith
  have hBtM : Bt ≤ M := by
    dsimp [M]
    have : 0 ≤ B₀ + ∑ i : Fin d, Bg i + ∑ i : Fin d, ∑ j : Fin d, Bh i j := by
      linarith
    linarith
  have hBgM (i : Fin d) : Bg i ≤ M := by
    dsimp [M]
    have hsum : Bg i ≤ ∑ j : Fin d, Bg j := Finset.single_le_sum
      (fun j _ => hBgnonneg j) (Finset.mem_univ i)
    have : 0 ≤ B₀ + Bt + ∑ i : Fin d, ∑ j : Fin d, Bh i j := by linarith
    linarith
  have hBhM (i j : Fin d) : Bh i j ≤ M := by
    dsimp [M]
    have hinner : Bh i j ≤ ∑ k : Fin d, Bh i k := Finset.single_le_sum
      (fun k _ => hBhnonneg i k) (Finset.mem_univ j)
    have houter : (∑ k : Fin d, Bh i k) ≤ ∑ l : Fin d, ∑ k : Fin d, Bh l k :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => hBhnonneg l k)
        (Finset.mem_univ i)
    have : 0 ≤ B₀ + Bt + ∑ i : Fin d, Bg i := by linarith
    linarith
  let N : Nat := 3 + d * 2 + d ^ 2 * 4
  let C : Real := (N : Real) * M
  have hCpos : 0 < C := by
    dsimp [C, N]
    positivity
  refine ⟨eta, C, hCpos, heta, hetaCompact, heta_one, hetaU, ?_⟩
  intro q hq hqMem hqtMem hqgMem hqhMem
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_parabolicBox 1 1 0 0
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hp : (1 : ENNReal) ≤ parabolicExponent d := parabolicExponent_one_le d
  have hetaU' : tsupport eta ⊆ U := by simpa only [U] using hetaU
  have htimeU : tsupport (timeDerivative eta) ⊆ U :=
    (timeDerivative_tsupport_subset eta).trans hetaU'
  have hgradU (i : Fin d) : tsupport (fun z => velocityGradient eta z i) ⊆ U :=
    (velocityGradient_tsupport_subset eta).trans hetaU'
  have hhessU (i j : Fin d) : tsupport (fun z => velocityHessian eta z i j) ⊆ U :=
    (velocityHessian_tsupport_subset eta).trans hetaU'
  have hvalueMem : MemLp (fun z => eta z * q z) (parabolicExponent d) volume :=
    memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' hqMem
  have htimeLeftMem : MemLp (fun z => eta z * timeDerivative q z)
      (parabolicExponent d) volume :=
    memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' hqtMem
  have htimeRightMem : MemLp (fun z => q z * timeDerivative eta z)
      (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (timeDerivative_cutoff_continuous heta₂)
      (timeDerivative_cutoff_hasCompactSupport hetaCompact) htimeU hqMem
  have htimeMem : MemLp (timeDerivative (fun z => eta z * q z))
      (parabolicExponent d) volume := by
    have hformula : timeDerivative (fun z => eta z * q z) = fun z =>
        eta z * timeDerivative q z + q z * timeDerivative eta z := by
      funext z
      exact timeDerivative_cutoff_mul hUopen heta₂ hetaU' hq z
    rw [hformula]
    exact htimeLeftMem.add htimeRightMem
  have hgradLeftMem (i : Fin d) : MemLp (fun z => eta z * velocityGradient q z i)
      (parabolicExponent d) volume :=
    memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' (hqgMem i)
  have hgradRightMem (i : Fin d) : MemLp (fun z => q z * velocityGradient eta z i)
      (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (velocityGradient_cutoff_continuous heta₂)
      (velocityGradient_cutoff_hasCompactSupport hetaCompact) (hgradU i) hqMem
  have hgradMem (i : Fin d) : MemLp (fun z => velocityGradient (fun y => eta y * q y) z i)
      (parabolicExponent d) volume := by
    have hformula : (fun z => velocityGradient (fun y => eta y * q y) z i) = fun z =>
        eta z * velocityGradient q z i + q z * velocityGradient eta z i := by
      funext z
      exact velocityGradient_cutoff_mul hUopen heta₂ hetaU' hq z i
    rw [hformula]
    exact (hgradLeftMem i).add (hgradRightMem i)
  have hhessOneMem (i j : Fin d) : MemLp (fun z => eta z * velocityHessian q z i j)
      (parabolicExponent d) volume :=
    memLp_cutoff_mul hUmeas heta.continuous hetaCompact hetaU' (hqhMem i j)
  have hhessTwoMem (i j : Fin d) : MemLp (fun z =>
      velocityGradient eta z j * velocityGradient q z i) (parabolicExponent d) volume :=
    memLp_cutoff_mul hUmeas (velocityGradient_cutoff_continuous heta₂)
      (velocityGradient_cutoff_hasCompactSupport hetaCompact) (hgradU j) (hqgMem i)
  have hhessThreeMem (i j : Fin d) : MemLp (fun z =>
      velocityGradient q z j * velocityGradient eta z i) (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (velocityGradient_cutoff_continuous heta₂)
      (velocityGradient_cutoff_hasCompactSupport hetaCompact) (hgradU i) (hqgMem j)
  have hhessFourMem (i j : Fin d) : MemLp (fun z => q z * velocityHessian eta z i j)
      (parabolicExponent d) volume := by
    simpa only [mul_comm] using memLp_cutoff_mul hUmeas
      (velocityHessian_cutoff_continuous heta₂)
      (velocityHessian_cutoff_hasCompactSupport hetaCompact) (hhessU i j) hqMem
  have hhessMem (i j : Fin d) : MemLp (fun z =>
      velocityHessian (fun y => eta y * q y) z i j) (parabolicExponent d) volume := by
    have hformula : (fun z => velocityHessian (fun y => eta y * q y) z i j) = fun z =>
        eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j := by
      funext z
      exact velocityHessian_cutoff_mul hUopen heta₂ hetaU' hq z i j
    rw [hformula]
    simpa only [Pi.add_def, add_assoc] using ((hhessOneMem i j).add (hhessTwoMem i j)).add
      ((hhessThreeMem i j).add (hhessFourMem i j))
  have hjetMem : ParabolicSmoothJetMemLp d (fun z => eta z * q z) :=
    ⟨hvalueMem, htimeMem, hgradMem, hhessMem⟩
  let m : ENNReal := ENNReal.ofReal M
  let Q : ENNReal := eLpNorm q (parabolicExponent d) (volume.restrict U)
  let T : ENNReal := eLpNorm (timeDerivative q) (parabolicExponent d) (volume.restrict U)
  let G : Fin d → ENNReal := fun i =>
    eLpNorm (fun z => velocityGradient q z i) (parabolicExponent d) (volume.restrict U)
  let H : Fin d → Fin d → ENNReal := fun i j =>
    eLpNorm (fun z => velocityHessian q z i j) (parabolicExponent d) (volume.restrict U)
  let R : ENNReal := Q + T + ∑ i : Fin d, G i + ∑ i : Fin d, ∑ j : Fin d, H i j
  have hQR : Q ≤ R := by
    dsimp [R]
    exact le_self_add.trans (le_self_add.trans le_self_add)
  have hTR : T ≤ R := by
    dsimp [R]
    exact (le_add_of_nonneg_left (by positivity : 0 ≤ Q)).trans
      (le_self_add.trans le_self_add)
  have hGR (i : Fin d) : G i ≤ R := by
    dsimp [R]
    exact le_trans (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i))
      ((le_add_of_nonneg_left (by positivity : 0 ≤ Q + T)).trans le_self_add)
  have hHR (i j : Fin d) : H i j ≤ R := by
    dsimp [R]
    calc
      H i j ≤ ∑ k : Fin d, H i k := Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)
      _ ≤ ∑ l : Fin d, ∑ k : Fin d, H l k :=
        Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => bot_le) (Finset.mem_univ i)
      _ ≤ R := le_add_of_nonneg_left (by positivity : 0 ≤ Q + T + ∑ i : Fin d, G i)
  have hvalueE : eLpNorm (fun z => eta z * q z) (parabolicExponent d) volume ≤ m * Q := by
    simpa only [m, Q] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hvalueMem).aestronglyMeasurable) hUmeas hetaU' hB₀ hB₀M
  have htimeLeftE : eLpNorm (fun z => eta z * timeDerivative q z)
      (parabolicExponent d) volume ≤ m * T := by
    simpa only [m, T] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (htimeLeftMem).aestronglyMeasurable) hUmeas hetaU' hB₀ hB₀M
  have htimeRightE : eLpNorm (fun z => q z * timeDerivative eta z)
      (parabolicExponent d) volume ≤ m * Q := by
    simpa only [m, Q, mul_comm] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (htimeRightMem).aestronglyMeasurable) hUmeas htimeU hBt hBtM
  have hgradLeftE (i : Fin d) : eLpNorm (fun z => eta z * velocityGradient q z i)
      (parabolicExponent d) volume ≤ m * G i := by
    simpa only [m, G] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hgradLeftMem i).aestronglyMeasurable) hUmeas hetaU' hB₀ hB₀M
  have hgradRightE (i : Fin d) : eLpNorm (fun z => q z * velocityGradient eta z i)
      (parabolicExponent d) volume ≤ m * Q := by
    simpa only [m, Q, mul_comm] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hgradRightMem i).aestronglyMeasurable) hUmeas (hgradU i)
      (hBg i) (hBgM i)
  have hhessOneE (i j : Fin d) : eLpNorm (fun z => eta z * velocityHessian q z i j)
      (parabolicExponent d) volume ≤ m * H i j := by
    simpa only [m, H] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hhessOneMem i j).aestronglyMeasurable) hUmeas hetaU' hB₀ hB₀M
  have hhessTwoE (i j : Fin d) : eLpNorm (fun z =>
      velocityGradient eta z j * velocityGradient q z i)
      (parabolicExponent d) volume ≤ m * G i := by
    simpa only [m, G] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hhessTwoMem i j).aestronglyMeasurable)
      hUmeas (hgradU j) (hBg j) (hBgM j)
  have hhessThreeE (i j : Fin d) : eLpNorm (fun z =>
      velocityGradient q z j * velocityGradient eta z i)
      (parabolicExponent d) volume ≤ m * G j := by
    have hraw := eLpNorm_cutoff_mul_le_of_bound_le (d := d) (U := U)
      (p := parabolicExponent d)
      (a := fun z => velocityGradient eta z i)
      (f := fun z => velocityGradient q z j)
      (by simpa only [mul_comm] using (hhessThreeMem i j).aestronglyMeasurable)
      hUmeas (hgradU i) (hBg i) (hBgM i)
    simpa only [m, G, mul_comm] using hraw
  have hhessFourE (i j : Fin d) : eLpNorm (fun z => q z * velocityHessian eta z i j)
      (parabolicExponent d) volume ≤ m * Q := by
    simpa only [m, Q, mul_comm] using eLpNorm_cutoff_mul_le_of_bound_le
      (by simpa only [mul_comm] using (hhessFourMem i j).aestronglyMeasurable) hUmeas (hhessU i j)
      (hBh i j) (hBhM i j)
  have hvalueR : eLpNorm (fun z => eta z * q z) (parabolicExponent d) volume ≤ m * R :=
    hvalueE.trans (mul_le_mul_right hQR m)
  have htimeR : eLpNorm (timeDerivative (fun z => eta z * q z))
      (parabolicExponent d) volume ≤ 2 * (m * R) := by
    rw [show timeDerivative (fun z => eta z * q z) = fun z =>
        eta z * timeDerivative q z + q z * timeDerivative eta z by
      funext z
      exact timeDerivative_cutoff_mul hUopen heta₂ hetaU' hq z]
    calc
      eLpNorm (fun z => eta z * timeDerivative q z + q z * timeDerivative eta z)
          (parabolicExponent d) volume ≤
          eLpNorm (fun z => eta z * timeDerivative q z) (parabolicExponent d) volume +
            eLpNorm (fun z => q z * timeDerivative eta z) (parabolicExponent d) volume :=
        eLpNorm_add_le hp
      _ ≤ m * R + m * R := add_le_add
        (htimeLeftE.trans (mul_le_mul_right hTR m))
        (htimeRightE.trans (mul_le_mul_right hQR m))
      _ = 2 * (m * R) := by ring
  have hgradR (i : Fin d) : eLpNorm (fun z => velocityGradient (fun y => eta y * q y) z i)
      (parabolicExponent d) volume ≤ 2 * (m * R) := by
    rw [show (fun z => velocityGradient (fun y => eta y * q y) z i) = fun z =>
        eta z * velocityGradient q z i + q z * velocityGradient eta z i by
      funext z
      exact velocityGradient_cutoff_mul hUopen heta₂ hetaU' hq z i]
    calc
      eLpNorm (fun z => eta z * velocityGradient q z i + q z * velocityGradient eta z i)
          (parabolicExponent d) volume ≤
          eLpNorm (fun z => eta z * velocityGradient q z i) (parabolicExponent d) volume +
            eLpNorm (fun z => q z * velocityGradient eta z i) (parabolicExponent d) volume :=
        eLpNorm_add_le hp
      _ ≤ m * R + m * R := add_le_add
        ((hgradLeftE i).trans (mul_le_mul_right (hGR i) m))
        ((hgradRightE i).trans (mul_le_mul_right hQR m))
      _ = 2 * (m * R) := by ring
  have hhessR (i j : Fin d) : eLpNorm (fun z => velocityHessian (fun y => eta y * q y) z i j)
      (parabolicExponent d) volume ≤ 4 * (m * R) := by
    rw [show (fun z => velocityHessian (fun y => eta y * q y) z i j) = fun z =>
        eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j by
      funext z
      exact velocityHessian_cutoff_mul hUopen heta₂ hetaU' hq z i j]
    rw [show (fun z =>
        eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j) =
        ((fun z => eta z * velocityHessian q z i j) +
          (fun z => velocityGradient eta z j * velocityGradient q z i) +
            (fun z => velocityGradient q z j * velocityGradient eta z i)) +
          fun z => q z * velocityHessian eta z i j by
      funext z
      simp only [Pi.add_def, add_assoc]]
    calc
      eLpNorm (fun z => eta z * velocityHessian q z i j +
          velocityGradient eta z j * velocityGradient q z i +
            velocityGradient q z j * velocityGradient eta z i +
              q z * velocityHessian eta z i j) (parabolicExponent d) volume ≤
          (eLpNorm (fun z => eta z * velocityHessian q z i j) (parabolicExponent d) volume +
            eLpNorm (fun z => velocityGradient eta z j * velocityGradient q z i)
              (parabolicExponent d) volume +
              eLpNorm (fun z => velocityGradient q z j * velocityGradient eta z i)
                (parabolicExponent d) volume) +
            eLpNorm (fun z => q z * velocityHessian eta z i j) (parabolicExponent d) volume := by
        calc
          _ ≤ eLpNorm (fun z => eta z * velocityHessian q z i j +
              velocityGradient eta z j * velocityGradient q z i +
                velocityGradient q z j * velocityGradient eta z i) (parabolicExponent d) volume +
              eLpNorm (fun z => q z * velocityHessian eta z i j) (parabolicExponent d) volume :=
            eLpNorm_add_le hp
          _ ≤ _ := by
            have htwo := eLpNorm_add_le (μ := volume)
              (f := fun z => eta z * velocityHessian q z i j)
              (g := fun z => velocityGradient eta z j * velocityGradient q z i) hp
            have hthree := eLpNorm_add_le (μ := volume)
              (f := (fun z => eta z * velocityHessian q z i j) +
                fun z => velocityGradient eta z j * velocityGradient q z i)
              (g := fun z => velocityGradient q z j * velocityGradient eta z i) hp
            have hthree' : eLpNorm (fun z => eta z * velocityHessian q z i j +
                velocityGradient eta z j * velocityGradient q z i +
                  velocityGradient q z j * velocityGradient eta z i)
                (parabolicExponent d) volume ≤
                eLpNorm (fun z => eta z * velocityHessian q z i j) (parabolicExponent d) volume +
                  eLpNorm (fun z => velocityGradient eta z j * velocityGradient q z i)
                    (parabolicExponent d) volume +
                    eLpNorm (fun z => velocityGradient q z j * velocityGradient eta z i)
                      (parabolicExponent d) volume := by
              rw [show (fun z => eta z * velocityHessian q z i j +
                  velocityGradient eta z j * velocityGradient q z i +
                    velocityGradient q z j * velocityGradient eta z i) =
                  ((fun z => eta z * velocityHessian q z i j) +
                    fun z => velocityGradient eta z j * velocityGradient q z i) +
                      fun z => velocityGradient q z j * velocityGradient eta z i by
                funext z
                simp only [Pi.add_def, add_assoc]]
              exact hthree.trans (add_le_add_left htwo _)
            exact add_le_add_left hthree' _
      _ ≤ (m * R + m * R + m * R) + m * R := by
        gcongr
        · exact (hhessOneE i j).trans (mul_le_mul_right (hHR i j) m)
        · exact (hhessTwoE i j).trans (mul_le_mul_right (hGR i) m)
        · exact (hhessThreeE i j).trans (mul_le_mul_right (hGR j) m)
        · exact (hhessFourE i j).trans (mul_le_mul_right hQR m)
      _ = 4 * (m * R) := by ring
  have hENN : parabolicSmoothJetELpNorm d (fun z => eta z * q z) ≤ ENNReal.ofReal C * R := by
    unfold parabolicSmoothJetELpNorm parabolicELpNorm
    calc
      eLpNorm (fun z => eta z * q z) (parabolicExponent d) volume +
          eLpNorm (timeDerivative (fun z => eta z * q z)) (parabolicExponent d) volume +
          ∑ i : Fin d, eLpNorm (fun z => velocityGradient (fun y => eta y * q y) z i)
            (parabolicExponent d) volume +
          ∑ i : Fin d, ∑ j : Fin d, eLpNorm
            (fun z => velocityHessian (fun y => eta y * q y) z i j) (parabolicExponent d) volume ≤
          m * R + 2 * (m * R) + ∑ _i : Fin d, 2 * (m * R) +
            ∑ _i : Fin d, ∑ _j : Fin d, 4 * (m * R) := by
        exact add_le_add
          (add_le_add
            (add_le_add hvalueR htimeR)
            (Finset.sum_le_sum fun i _ => hgradR i))
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hhessR i j)
      _ = (N : ENNReal) * (m * R) := by
        dsimp [N]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
        ring
      _ = ENNReal.ofReal C * R := by
        dsimp [C, m]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp only [ENNReal.ofReal_natCast]
        ring
  have hQtop : Q ≠ ⊤ := by simpa only [Q] using hqMem.eLpNorm_ne_top
  have hTtop : T ≠ ⊤ := by simpa only [T] using hqtMem.eLpNorm_ne_top
  have hGtop (i : Fin d) : G i ≠ ⊤ := by simpa only [G] using (hqgMem i).eLpNorm_ne_top
  have hHtop (i j : Fin d) : H i j ≠ ⊤ := by simpa only [H] using (hqhMem i j).eLpNorm_ne_top
  have hRtop : R ≠ ⊤ := by
    dsimp [R]
    apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.add_ne_top.mpr ⟨hQtop, hTtop⟩
      · exact ENNReal.sum_ne_top.mpr fun i _ => hGtop i
    · exact ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHtop i j
  have hCRtop : ENNReal.ofReal C * R ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRtop
  have hreal := ENNReal.toReal_mono hCRtop hENN
  have hRreal : R.toReal =
      parabolicLpNormOn d q (parabolicBox 1 1 0 0) +
        parabolicLpNormOn d (timeDerivative q) (parabolicBox 1 1 0 0) +
        ∑ i : Fin d, parabolicLpNormOn d (fun z => velocityGradient q z i)
          (parabolicBox 1 1 0 0) +
        ∑ i : Fin d, ∑ j : Fin d, parabolicLpNormOn d
          (fun z => velocityHessian q z i j) (parabolicBox 1 1 0 0) := by
    dsimp [R, Q, T, G, H, U, parabolicLpNormOn, parabolicELpNormOn]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hQtop, hTtop⟩, ENNReal.sum_ne_top.mpr fun i _ => hGtop i⟩)
      (ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHtop i j)]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hQtop, hTtop⟩)
      (ENNReal.sum_ne_top.mpr fun i _ => hGtop i)]
    rw [ENNReal.toReal_add hQtop hTtop]
    rw [ENNReal.toReal_sum fun i _ => hGtop i]
    rw [ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHtop i j]
    simp_rw [ENNReal.toReal_sum fun j _ => hHtop _ j]
    rfl
  simpa only [parabolicSmoothJetLpNorm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hCpos.le, hRreal] using hreal

end HypoellipticAleksandrov.Parabolic
