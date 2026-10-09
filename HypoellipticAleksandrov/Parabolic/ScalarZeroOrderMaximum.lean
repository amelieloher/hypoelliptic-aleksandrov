module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum

/-!
# Scalar zero-order backward parabolic maximum principle

This file proves the scalar backward maximum principle with a nonpositive
zero-order coefficient on an arbitrary open bounded velocity domain.  The
initial face is handled by compact cylinders whose lower time is strictly later
than the original initial time, followed by closed-cylinder continuity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

private def insetCylinder {n : ℕ} (α r₁ : ℝ) (Ω : Set (PDE.Vec n)) :
    Set (TimeVelocity n) :=
  Set.Icc α r₁ ×ˢ closure Ω

private def insetActive {n : ℕ} (α r₁ : ℝ) (Ω : Set (PDE.Vec n)) :
    Set (TimeVelocity n) :=
  Set.Ico α r₁ ×ˢ Ω

private def terminalTilt {n : ℕ} (u : TimeVelocity n → ℝ) (ε r₁ : ℝ) :
    TimeVelocity n → ℝ :=
  fun z => u z - ε * (r₁ - z.1)

private theorem insetActive_subset_insetCylinder {n : ℕ} {α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} :
    insetActive α r₁ Ω ⊆ insetCylinder α r₁ Ω := by
  rintro z ⟨⟨hzα, hz₁⟩, hzΩ⟩
  exact ⟨⟨hzα, le_of_lt hz₁⟩, subset_closure hzΩ⟩

private theorem isCompact_insetCylinder {n : ℕ} {α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hΩbounded : Bornology.IsBounded Ω) :
    IsCompact (insetCylinder α r₁ Ω) :=
  isCompact_Icc.prod hΩbounded.isCompact_closure

private theorem insetActive_subset_original_open {n : ℕ} {r₀ α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hr₀α : r₀ < α) :
    insetActive α r₁ Ω ⊆ scalarParabolicOpenCylinder r₀ r₁ Ω := by
  rintro z ⟨⟨hzα, hzr₁⟩, hzΩ⟩
  exact ⟨⟨lt_of_lt_of_le hr₀α hzα, hzr₁⟩, hzΩ⟩

private theorem insetCylinder_diff_insetActive_eq {n : ℕ} {α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hΩopen : IsOpen Ω) (hαr₁ : α < r₁) :
    insetCylinder α r₁ Ω \ insetActive α r₁ Ω =
      scalarParabolicTerminalFace r₁ Ω ∪
        (Set.Icc α r₁ ×ˢ frontier Ω) := by
  ext z
  rcases z with ⟨r, y⟩
  rw [hΩopen.frontier_eq]
  constructor
  · rintro ⟨⟨⟨hrα, hr₁⟩, hycl⟩, hnot⟩
    by_cases hr : r = r₁
    · left
      exact ⟨hr, hycl⟩
    · right
      refine ⟨⟨hrα, hr₁⟩, ?_⟩
      exact ⟨hycl, fun hy => hnot ⟨⟨hrα, lt_of_le_of_ne hr₁ hr⟩, hy⟩⟩
  · rintro (hterminal | hlateral)
    · rcases hterminal with ⟨hr, hycl⟩
      simp only [mem_singleton_iff] at hr
      subst r
      refine ⟨⟨⟨le_of_lt hαr₁, le_rfl⟩, hycl⟩, ?_⟩
      simp [insetActive]
    · rcases hlateral with ⟨⟨hrα, hr₁⟩, hycl, hynot⟩
      refine ⟨⟨⟨hrα, hr₁⟩, hycl⟩, ?_⟩
      intro hactive
      exact hynot hactive.2

private theorem hasDerivAt_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa only [one_smul] using
    ((hasDerivAt_id' (𝕜 := ℝ) s).smul_const q).const_add x

private theorem deriv_deriv_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    c ≤ 0 := by
  by_contra hc
  have hcpos : 0 < c := lt_of_not_ge hc
  have hmin : IsLocalMin f a :=
    isLocalMin_of_deriv_deriv_pos
      (by simpa only [hsecond.deriv] using hcpos)
      hmax.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    rw [hy]
    exact deriv_const y (f a)
  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  exact hcpos.ne' this

private theorem hasDerivAt_fderiv_restrict_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by
  have hline : HasDerivAt (fun r : ℝ => x + r • q) q 0 :=
    hasDerivAt_affine_line x q 0
  have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hsecond
  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 :=
    hsecond'.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero, map_zero] using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

private theorem hasDerivAt_deriv_restrict_affine_line_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
  have hgGradDiffAt : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEvalLine : HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (fderiv ℝ (fderiv ℝ g) x q q) 0 :=
    hasDerivAt_fderiv_restrict_affine_line hgGradDiffAt.hasFDerivAt
  have hgEventually : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g y :=
    hg.eventually (by norm_num)
  have hgEventuallyAtLineZero :
      ∀ᶠ y in 𝓝 (x + (0 : ℝ) • q), ContDiffAt ℝ 2 g y := by
    simpa only [zero_smul, add_zero] using hgEventually
  apply hEvalLine.congr_of_eventuallyEq
  filter_upwards [
    (hasDerivAt_affine_line x q 0).continuousAt hgEventuallyAtLineZero] with r hr
  change ContDiffAt ℝ 2 g (x + r • q) at hr
  exact (hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    r (hasDerivAt_affine_line x q r) |>.deriv

private theorem fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x)
    (hmax : IsLocalMax (fun r : ℝ => g (x + r • q)) 0) :
    fderiv ℝ (fderiv ℝ g) x q q ≤ 0 := by
  have hlineCont : ContinuousAt (fun r : ℝ => x + r • q) 0 :=
    (hasDerivAt_affine_line x q 0).continuousAt
  have hgAtLineZero : ContinuousAt g (x + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hg.continuousAt
  have hcompCont : ContinuousAt (fun r : ℝ => g (x + r • q)) 0 :=
    hgAtLineZero.comp' (f := fun r : ℝ => x + r • q) hlineCont
  exact deriv_deriv_nonpos_of_isLocalMax hmax
    (hasDerivAt_deriv_restrict_affine_line_of_contDiffAt hg) hcompCont

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
  have hjapply := congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hj
  simpa [ContinuousLinearMap.flip_apply] using hjapply

private theorem scalarSpatialHessian_quadratic_eq {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (q : PDE.Vec n) :
    dotProduct q ((scalarSpatialHessian u z).mulVec q) =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2 q q := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  let H := fderiv ℝ (fderiv ℝ g) z.2
  change (∑ i : Fin n, q i * ∑ j : Fin n,
      scalarSpatialHessian u z i j * q j) = H q q
  simp_rw [scalarSpatialHessian_apply_eq_sndFDeriv hu]
  change (∑ i : Fin n, q i * ∑ j : Fin n,
      H (PDE.basisVec i) (PDE.basisVec j) * q j) = H q q
  calc
    (∑ i : Fin n, q i * ∑ j : Fin n,
        H (PDE.basisVec i) (PDE.basisVec j) * q j) =
        ∑ i : Fin n, q i * H (PDE.basisVec i)
          (∑ j : Fin n, q j • PDE.basisVec j) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin n, q i * H (PDE.basisVec i) q := by
      rw [PDE.sum_smul_basisVec]
    _ = H (∑ i : Fin n, q i • PDE.basisVec i) q := by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = H q q := by rw [PDE.sum_smul_basisVec]

private theorem scalarSpatialHessian_isSymm_of_contDiffAt {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    (scalarSpatialHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  rw [scalarSpatialHessian_apply_eq_sndFDeriv hu,
    scalarSpatialHessian_apply_eq_sndFDeriv hu]
  exact
    (hu.isSymmSndFDerivAt (by norm_num)).eq (PDE.basisVec j) (PDE.basisVec i)

private theorem neg_scalarSpatialHessian_posSemidef_of_spatial_localMax
    {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    (-scalarSpatialHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    change -scalarSpatialHessian u z j i = -scalarSpatialHessian u z i j
    exact
      congrArg Neg.neg ((scalarSpatialHessian_isSymm_of_contDiffAt hu).apply i j)
  · intro q
    rw [neg_mulVec, dotProduct_neg]
    have hlineMax : IsLocalMax
        (fun r : ℝ => u (z.1, z.2 + r • q)) 0 := by
      have hmaxAtLineZero : IsLocalMax (fun y : PDE.Vec n => u (z.1, y))
          (z.2 + (0 : ℝ) • q) := by
        simpa only [zero_smul, add_zero] using hmax
      simpa only [Function.comp_def, id_eq] using hmaxAtLineZero.comp_continuous
        (g := fun r : ℝ => z.2 + r • q)
        (hasDerivAt_affine_line z.2 q 0).continuousAt
    change -dotProduct q
      ((scalarSpatialHessian u z).mulVec q) ≥ 0
    rw [scalarSpatialHessian_quadratic_eq hu q]
    exact neg_nonneg.mpr
      (fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine hu hlineMax)

private theorem scalarSpatialGradient_eq_zero_of_spatial_localMax
    {n : ℕ} {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (hmax : IsLocalMax (fun y : PDE.Vec n => u (z.1, y)) z.2) :
    scalarSpatialGradient u z = 0 := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u (z.1, y)) z.2 (PDE.basisVec i) = 0
  have hzero := hmax.hasFDerivAt_eq_zero
    ((hu.differentiableAt (by norm_num)).hasFDerivAt)
  simpa using congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hzero

private theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  classical
  let S : PDE.Mat n := CFC.sqrt H
  have hS : S.PosSemidef := by
    dsimp [S]
    exact CFC.sqrt_nonneg H |>.posSemidef
  have hconj : (S * A * Sᴴ).PosSemidef := hA.mul_mul_conjTranspose_same S
  calc
    0 ≤ (S * A * Sᴴ).trace := hconj.trace_nonneg
    _ = (S * A * S).trace := by rw [hS.isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * H).trace := by rw [show S * S = H by
      dsimp [S]
      exact CFC.sqrt_mul_sqrt_self H hH.nonneg]

private theorem matrixContraction_nonpos_of_psd_neg {n : ℕ} {A H : PDE.Mat n}
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) (hHsymm : H.IsSymm) :
    matrixContraction A H ≤ 0 := by
  have htrace : 0 ≤ (A * (-H)).trace := trace_mul_nonneg_of_posSemidef hA hH
  rw [matrixContraction_eq_trace_mul_of_isSymm A H hHsymm]
  calc
    (A * H).trace = -((A * (-H)).trace) := by simp
    _ ≤ 0 := neg_nonpos.mpr htrace

private theorem terminalTilt_spatialGradient_eq {n : ℕ} (u : TimeVelocity n → ℝ)
    (ε r₁ : ℝ) (z : TimeVelocity n) :
    scalarSpatialGradient (terminalTilt u ε r₁) z = scalarSpatialGradient u z := by
  ext i
  simp [terminalTilt, scalarSpatialGradient, PDE.classicalGradient,
    fderiv_sub_const]

private theorem terminalTilt_spatialHessian_eq {n : ℕ} (u : TimeVelocity n → ℝ)
    (ε r₁ : ℝ) (z : TimeVelocity n) :
    scalarSpatialHessian (terminalTilt u ε r₁) z = scalarSpatialHessian u z := by
  have hgradient :
      (fun y : PDE.Vec n =>
        PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w) - ε * (r₁ - z.1)) y) =
        fun y => PDE.classicalGradient (fun w : PDE.Vec n => u (z.1, w)) y := by
    funext y
    ext i
    exact congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i))
      (fderiv_sub_const (𝕜 := ℝ) (f := fun w : PDE.Vec n => u (z.1, w))
        (x := y) (ε * (r₁ - z.1)))
  change (fun i j => fderiv ℝ
      (fun y : PDE.Vec n => PDE.classicalGradient
        (fun w : PDE.Vec n => u (z.1, w) - ε * (r₁ - z.1)) y)
      z.2 (PDE.basisVec i) j) = _
  simp only [hgradient]
  rfl

private theorem terminalTilt_timeDerivative_eq {n : ℕ} {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    scalarTimeDerivative (terminalTilt u ε r₁) z = scalarTimeDerivative u z + ε := by
  have hderiv : HasDerivAt (fun r : ℝ => terminalTilt u ε r₁ (r, z.2))
      (scalarTimeDerivative u z + ε) z.1 := by
    change HasDerivAt (fun r : ℝ => u (r, z.2) - ε * (r₁ - r))
      (scalarTimeDerivative u z + ε) z.1
    convert (hu.timeSlice_hasDerivAt hz).sub
      ((hasDerivAt_const (x := z.1) (c := ε)).mul
        ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
    all_goals
      try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, terminalTilt]
      first | rfl | (funext r; ring) | ring
  exact hderiv.deriv

private theorem terminalTilt_continuousOn {n : ℕ} {u : TimeVelocity n → ℝ}
    {K : Set (TimeVelocity n)} (hu : ContinuousOn u K) (ε r₁ : ℝ) :
    ContinuousOn (terminalTilt u ε r₁) K := by
  apply hu.sub
  fun_prop

private theorem spatial_localMax_of_inset_localMax {n : ℕ} {α r₁ : ℝ}
    {Ω : Set (PDE.Vec n)} (hΩopen : IsOpen Ω) {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (insetCylinder α r₁ Ω) z) :
    IsLocalMax (fun y : PDE.Vec n => w (z.1, y)) z.2 := by
  have hslice : IsLocalMaxOn (fun y : PDE.Vec n => w (z.1, y)) Ω z.2 := by
    simpa only [Function.comp_def, id_eq] using hmax.comp_continuousOn
      (s := Ω)
      (by intro y hy; exact ⟨⟨hz.1.1, le_of_lt hz.1.2⟩, subset_closure hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn hz.2
  exact hslice.isLocalMax (hΩopen.mem_nhds hz.2)

private theorem terminalTilt_spatialContDiffAt {n : ℕ} {u : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} {z : TimeVelocity n} (hu : IsScalarC12On u D)
    (hz : z ∈ D) (ε r₁ : ℝ) :
    ContDiffAt ℝ 2 (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 := by
  simpa [terminalTilt] using (hu.spatialSlice_contDiffAt hz).sub contDiffAt_const

private theorem timeDerivative_terminalTilt_nonpos_of_inset_localMax
    {n : ℕ} {α r₁ : ℝ} {Ω : Set (PDE.Vec n)} {w : TimeVelocity n → ℝ}
    {z : TimeVelocity n} (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn w (insetCylinder α r₁ Ω) z)
    (hderiv : HasDerivAt (fun r : ℝ => w (r, z.2)) (scalarTimeDerivative w z) z.1) :
    scalarTimeDerivative w z ≤ 0 := by
  have htime : IsLocalMaxOn (fun r : ℝ => w (r, z.2)) (Set.Icc α r₁) z.1 := by
    simpa only [Function.comp_def, id_eq] using hmax.comp_continuousOn
      (s := Set.Icc α r₁)
      (by intro r hr; exact ⟨hr, subset_closure hz.2⟩)
      (continuous_id.prodMk continuous_const).continuousOn ⟨hz.1.1, le_of_lt hz.1.2⟩
  have hdirection : r₁ - z.1 ∈ posTangentConeAt (Set.Icc α r₁) z.1 := by
    apply sub_mem_posTangentConeAt_of_segment_subset
    intro s hs
    exact ⟨le_trans hz.1.1 (segment_subset_Icc (𝕜 := ℝ) (le_of_lt hz.1.2) hs).1,
      (segment_subset_Icc (𝕜 := ℝ) (le_of_lt hz.1.2) hs).2⟩
  have hnonpos := htime.hasFDerivWithinAt_nonpos hderiv.hasFDerivAt.hasFDerivWithinAt
    hdirection
  have hpos : 0 < r₁ - z.1 := sub_pos.mpr hz.1.2
  have hproduct : (r₁ - z.1) * scalarTimeDerivative w z ≤ 0 := by
    simpa [smul_eq_mul] using hnonpos
  exact nonpos_of_mul_nonpos_right hproduct hpos

private theorem scalarOperator_nonpos_at_inset_tilt_max
    {n : ℕ} {r₀ α r₁ : ℝ} {Ω : Set (PDE.Vec n)} (hΩopen : IsOpen Ω)
    (hr₀α : r₀ < α) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (u : TimeVelocity n → ℝ)
    (huC12 : IsScalarC12On u (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (haPsd : ∀ r y, (a r y).PosSemidef) {ε : ℝ} {z : TimeVelocity n}
    (hz : z ∈ insetActive α r₁ Ω)
    (hmax : IsLocalMaxOn (terminalTilt u ε r₁) (insetCylinder α r₁ Ω) z) :
    scalarParabolicOperator a b u z + ε ≤ 0 := by
  have hzopen : z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω :=
    insetActive_subset_original_open hr₀α hz
  have hspatialMax : IsLocalMax (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 :=
    spatial_localMax_of_inset_localMax hΩopen hz hmax
  have htiltDiff : ContDiffAt ℝ 2
      (fun y : PDE.Vec n => terminalTilt u ε r₁ (z.1, y)) z.2 :=
    terminalTilt_spatialContDiffAt huC12 hzopen ε r₁
  have hgradientTilt : scalarSpatialGradient (terminalTilt u ε r₁) z = 0 :=
    scalarSpatialGradient_eq_zero_of_spatial_localMax htiltDiff hspatialMax
  have hgradient : scalarSpatialGradient u z = 0 := by
    rw [← terminalTilt_spatialGradient_eq]
    exact hgradientTilt
  have hhessianTilt : (-scalarSpatialHessian (terminalTilt u ε r₁) z).PosSemidef :=
    neg_scalarSpatialHessian_posSemidef_of_spatial_localMax htiltDiff hspatialMax
  have hhessian : (-scalarSpatialHessian u z).PosSemidef := by
    rw [← terminalTilt_spatialHessian_eq]
    exact hhessianTilt
  have hsymmetric : (scalarSpatialHessian u z).IsSymm :=
    scalarSpatialHessian_isSymm_of_contDiffAt (huC12.spatialSlice_contDiffAt hzopen)
  have hcontraction : matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) ≤ 0 :=
    matrixContraction_nonpos_of_psd_neg (haPsd z.1 z.2) hhessian hsymmetric
  have htimeTilt : scalarTimeDerivative (terminalTilt u ε r₁) z ≤ 0 := by
    have hderivTilt : HasDerivAt (fun r : ℝ => terminalTilt u ε r₁ (r, z.2))
        (scalarTimeDerivative (terminalTilt u ε r₁) z) z.1 := by
      rw [terminalTilt_timeDerivative_eq huC12 hzopen ε r₁]
      convert (huC12.timeSlice_hasDerivAt hzopen).sub
        ((hasDerivAt_const (x := z.1) (c := ε)).mul
          ((hasDerivAt_const (x := z.1) (c := r₁)).sub (hasDerivAt_id z.1))) using 1
      all_goals
      try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, terminalTilt]
      first | rfl | (funext r; ring) | ring
    exact timeDerivative_terminalTilt_nonpos_of_inset_localMax hz hmax
      hderivTilt
  rw [terminalTilt_timeDerivative_eq huC12 hzopen ε r₁] at htimeTilt
  rw [scalarParabolicOperator_apply, hgradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  linarith

private theorem le_on_insetCylinder_of_zeroOrder_terminal_lateral_le
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ α r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀α : r₀ < α) (hαr₁ : α < r₁) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    {ε : ℝ} (hε : 0 < ε)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0) :
    ∀ z ∈ insetCylinder α r₁ Ω, terminalTilt w ε r₁ z ≤ 0 := by
  intro z hz
  by_cases hKempty : (insetCylinder α r₁ Ω).Nonempty
  · obtain ⟨zmax, hzmax, hmax⟩ :=
      (isCompact_insetCylinder hΩbounded).exists_isMaxOn hKempty
        (terminalTilt_continuousOn (hw.mono (by
          rintro q ⟨⟨hqα, hqr₁⟩, hqΩ⟩
          exact ⟨⟨le_trans (le_of_lt hr₀α) hqα, hqr₁⟩, hqΩ⟩)) ε r₁)
    refine (hmax hz).trans ?_
    by_cases hzactive : zmax ∈ insetActive α r₁ Ω
    · by_contra hnot
      have htiltPos : 0 < terminalTilt w ε r₁ zmax := lt_of_not_ge hnot
      have hzopen : zmax ∈ scalarParabolicOpenCylinder r₀ r₁ Ω :=
        insetActive_subset_original_open hr₀α hzactive
      have hprincipal := scalarOperator_nonpos_at_inset_tilt_max hΩopen hr₀α a b w
        hwC12 haPsd hzactive hmax.localize
      have hcAt : c zmax.1 zmax.2 ≤ 0 := hc zmax hzopen
      have hctilt : c zmax.1 zmax.2 * terminalTilt w ε r₁ zmax ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcAt htiltPos.le
      have hzeroTiltNonpos :
          scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax ≤ 0 := by
        rw [scalarParabolicZeroOrderOperator_apply,
          terminalTilt_timeDerivative_eq hwC12 hzopen ε r₁,
          terminalTilt_spatialHessian_eq, terminalTilt_spatialGradient_eq]
        rw [scalarParabolicOperator_apply] at hprincipal
        linarith
      have hfactor : 0 ≤ ε * (r₁ - zmax.1) :=
        mul_nonneg hε.le (sub_nonneg.mpr hzactive.1.2.le)
      have hcorrection : 0 ≤ -c zmax.1 zmax.2 * (ε * (r₁ - zmax.1)) :=
        mul_nonneg (neg_nonneg.mpr hcAt) hfactor
      have hzeroTiltEq :
          scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax =
            scalarParabolicZeroOrderOperator a b c w zmax + ε -
              c zmax.1 zmax.2 * (ε * (r₁ - zmax.1)) := by
        simp only [scalarParabolicZeroOrderOperator_apply,
          terminalTilt_timeDerivative_eq hwC12 hzopen ε r₁,
          terminalTilt_spatialHessian_eq, terminalTilt_spatialGradient_eq]
        dsimp [terminalTilt]
        ring
      have hzeroTiltPos :
          0 < scalarParabolicZeroOrderOperator a b c (terminalTilt w ε r₁) zmax := by
        rw [hzeroTiltEq]
        linarith [hPDE zmax hzopen]
      exact (not_lt_of_ge hzeroTiltNonpos) hzeroTiltPos
    · have hzmaxBoundary : zmax ∈ insetCylinder α r₁ Ω \ insetActive α r₁ Ω :=
        ⟨hzmax, hzactive⟩
      rw [insetCylinder_diff_insetActive_eq hΩopen hαr₁] at hzmaxBoundary
      rcases hzmaxBoundary with hterminalFace | hlateralFace
      · calc
          terminalTilt w ε r₁ zmax ≤ w zmax := by
            dsimp [terminalTilt]
            exact sub_le_self _ (mul_nonneg hε.le
              (sub_nonneg.mpr hterminalFace.1.le))
          _ ≤ 0 := hterminal zmax hterminalFace
      · calc
          terminalTilt w ε r₁ zmax ≤ w zmax := by
            dsimp [terminalTilt]
            exact sub_le_self _ (mul_nonneg hε.le
              (sub_nonneg.mpr hlateralFace.1.2))
          _ ≤ 0 := hlateral zmax
            ⟨⟨le_trans (le_of_lt hr₀α) hlateralFace.1.1, hlateralFace.1.2⟩,
              hlateralFace.2⟩
  · exact (hKempty ⟨z, hz⟩).elim

/-
The remaining comparison assembly is deliberately kept below the pointwise
calculus lemmas so the initial-face continuity argument never enters the
active-set branch.
-/

private theorem le_zero_at_strictly_later_time
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r r₁ : ℝ}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hr₀r : r₀ < r) (hrr₁ : r < r₁) (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n) (c : ℝ → PDE.Vec n → ℝ)
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω, c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0)
    {y : PDE.Vec n} (hyclosure : y ∈ closure Ω) :
    w (r, y) ≤ 0 := by
  by_contra hnot
  have hpositive : 0 < w (r, y) := lt_of_not_ge hnot
  let α : ℝ := (r₀ + r) / 2
  have hα0 : r₀ < α := by dsimp [α]; linarith
  have hα1 : α < r₁ := by dsimp [α]; linarith
  have hzinset : (r, y) ∈ insetCylinder α r₁ Ω :=
    ⟨⟨le_of_lt (by dsimp [α]; linarith), le_of_lt hrr₁⟩, hyclosure⟩
  let ε : ℝ := w (r, y) / (2 * (r₁ - r))
  have hgap : 0 < r₁ - r := sub_pos.mpr hrr₁
  have hε : 0 < ε := div_pos hpositive (by positivity)
  have htilt := le_on_insetCylinder_of_zeroOrder_terminal_lateral_le
    hΩopen hΩbounded hα0 hα1 a b c haPsd hc w hw hwC12 hPDE hε hterminal hlateral
    (z := (r, y)) hzinset
  dsimp [terminalTilt, ε] at htilt
  have hdenom : 2 * (r₁ - r) ≠ 0 := by positivity
  have hhalf : w (r, y) / (2 * (r₁ - r)) * (r₁ - r) = w (r, y) / 2 := by
    field_simp [hdenom]
  rw [hhalf] at htilt
  linarith

/--
If the backward scalar operator with a nonpositive zero-order coefficient is
nonnegative on the open cylinder, then nonpositive terminal and lateral data
control the whole closed cylinder.  The proof uses strictly inset cylinders
before passing to the initial face by continuity.
-/
theorem scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
    {n : ℕ} {Ω : Set (PDE.Vec n)} {r₀ r₁ : ℝ}
    (hΩOpen : IsOpen Ω)
    (hΩBounded : Bornology.IsBounded Ω)
    (hr : r₀ < r₁)
    (a : CoefficientField n)
    (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ)
    (haContinuous : IsContinuousCoefficient a)
    (hbContinuous : Continuous (fun z : TimeVelocity n => b z.1 z.2))
    (haPsd : ∀ r y, (a r y).PosSemidef)
    (hc : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      c z.1 z.2 ≤ 0)
    (w : TimeVelocity n → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hwC12 : IsScalarC12On w (scalarParabolicOpenCylinder r₀ r₁ Ω))
    (hPDE : ∀ z ∈ scalarParabolicOpenCylinder r₀ r₁ Ω,
      0 ≤ scalarParabolicZeroOrderOperator a b c w z)
    (hTerminal : ∀ z ∈ scalarParabolicTerminalFace r₁ Ω, w z ≤ 0)
    (hLateral : ∀ z ∈ scalarParabolicLateralFace r₀ r₁ Ω, w z ≤ 0) :
    ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω, w z ≤ 0 := by
  have _hCoefficientContinuity := haContinuous
  have _hDriftContinuity := hbContinuous
  intro z hz
  rcases z with ⟨r, y⟩
  rcases hz with ⟨⟨hr₀, hr₁⟩, hyclosure⟩
  by_cases hyr₀ : r = r₀
  · subst r
    by_cases hyΩ : y ∈ Ω
    · let t : ℕ → ℝ := fun k => r₀ + (r₁ - r₀) * (1 / ((k : ℝ) + 1))
      have ht : Tendsto t atTop (𝓝 r₀) := by
        dsimp [t]
        simpa using tendsto_const_nhds.add
          (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      have hcurve : Tendsto (fun k : ℕ => (t k, y)) atTop (𝓝 (r₀, y)) := by
        rw [nhds_prod_eq]
        exact ht.prodMk (tendsto_const_nhds (x := y))
      have hcurveWithin : Tendsto (fun k : ℕ => (t k, y)) atTop
          (𝓝[(scalarParabolicClosedCylinder r₀ r₁ Ω)] (r₀, y)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hcurve, ?_⟩
        filter_upwards with k
        have hk : 0 < (k : ℝ) + 1 := by positivity
        have hsmall : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one₀ hk).mpr (by linarith)
        have hprod : (r₁ - r₀) * (1 / ((k : ℝ) + 1)) ≤ r₁ - r₀ :=
          by simpa using mul_le_mul_of_nonneg_left hsmall (le_of_lt (sub_pos.mpr hr))
        exact ⟨⟨by dsimp [t]; nlinarith [one_div_pos.mpr hk],
          by dsimp [t]; nlinarith⟩, subset_closure hyΩ⟩
      apply le_of_tendsto ((hw (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩,
        subset_closure hyΩ⟩).tendsto.comp hcurveWithin)
      filter_upwards [eventually_ge_atTop 1] with k hkNat
      have hk : 0 < (k : ℝ) + 1 := by positivity
      have hkone : 1 < (k : ℝ) + 1 := by
        exact_mod_cast Nat.lt_succ_of_le hkNat
      have hsmall : 1 / ((k : ℝ) + 1) < 1 := (div_lt_one₀ hk).mpr hkone
      have hprod : (r₁ - r₀) * (1 / ((k : ℝ) + 1)) < r₁ - r₀ :=
        by simpa using mul_lt_mul_of_pos_left hsmall (sub_pos.mpr hr)
      exact le_zero_at_strictly_later_time hΩOpen hΩBounded
        (by dsimp [t]; nlinarith [one_div_pos.mpr hk])
        (by dsimp [t]; nlinarith) a b c haPsd hc w hw hwC12 hPDE hTerminal hLateral
        (subset_closure hyΩ)
    · have hyfrontier : y ∈ frontier Ω := by
        rw [hΩOpen.frontier_eq]
        exact ⟨hyclosure, hyΩ⟩
      exact hLateral (r₀, y) ⟨⟨le_rfl, le_of_lt hr⟩, hyfrontier⟩
  · by_cases hrterminal : r = r₁
    · exact hTerminal (r, y) ⟨hrterminal, hyclosure⟩
    · exact le_zero_at_strictly_later_time hΩOpen hΩBounded
        (lt_of_le_of_ne hr₀ (Ne.symm hyr₀)) (lt_of_le_of_ne hr₁ hrterminal)
        a b c haPsd hc w hw hwC12 hPDE hTerminal hLateral hyclosure

end HypoellipticAleksandrov.Parabolic
