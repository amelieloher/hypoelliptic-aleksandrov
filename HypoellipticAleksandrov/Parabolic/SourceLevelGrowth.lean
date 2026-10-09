module

public import HypoellipticAleksandrov.Parabolic.SourceDensityPositive

/-!
# Source-aware parabolic level growth

This module turns a source-aware density-to-point relation into the supplied
upper-bound level-growth inequality on a literal physical parabolic box.
-/

@[expose] public section

open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

private theorem parabolicOperator_const_sub {d : ℕ} (B : CoefficientField d)
    (c : ℝ) (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    parabolicOperator B (fun y ↦ c - u y) z = -parabolicOperator B u z := by
  calc
    parabolicOperator B (fun y ↦ c - u y) z =
        parabolicOperator B (fun y ↦ -u y + c) z := by
      congr 1
      funext y
      ring
    _ = parabolicOperator B (fun y ↦ -u y) z :=
      parabolicOperator_add_const B (fun y ↦ -u y) c z
    _ = -parabolicOperator B u z := parabolicOperator_neg B u z

private theorem parabolicBox_subset_parabolicClosedBox {d : ℕ}
    {vartheta r t₀ : ℝ} {v₀ : PDE.Vec d} :
    parabolicBox vartheta r t₀ v₀ ⊆ parabolicClosedBox vartheta r t₀ v₀ := by
  intro z hz
  rcases hz with ⟨⟨hzleft, hzright⟩, hzv⟩
  exact ⟨⟨hzleft.le, hzright.le⟩, fun i ↦ (hzv i).le⟩

private theorem terminalCenter_mem_parabolicClosedBox {d : ℕ} {R t₀ : ℝ}
    {v₀ : PDE.Vec d} (hR : 0 < R) :
    (t₀ + R ^ 2, v₀) ∈ parabolicClosedBox 1 R t₀ v₀ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith [sq_nonneg R]
  · apply le_of_eq
    ring
  · intro i
    simp only [sub_self, abs_zero]
    exact hR.le

private theorem center_mem_velocityClosedCube {d : ℕ} {R : ℝ}
    {v₀ : PDE.Vec d} (hR : 0 < R) :
    v₀ ∈ velocityClosedCube v₀ (R / 2) := by
  intro i
  simp only [sub_self, abs_zero]
  linarith

private theorem contDiffOn_const_sub_div {d : ℕ} {U : Set (TimeVelocity d)}
    {M D : ℝ} {u : TimeVelocity d → ℝ} (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (fun z ↦ (M - u z) / D) U :=
  (contDiffOn_const.sub hu).div_const D

private theorem volume_toReal_mono_of_subset {d : ℕ} {s t : Set (TimeVelocity d)}
    (ht : (volume : Measure (TimeVelocity d)) t ≠ ⊤) (hst : s ⊆ t) :
    ((volume : Measure (TimeVelocity d)) s).toReal ≤
      ((volume : Measure (TimeVelocity d)) t).toReal :=
  ENNReal.toReal_mono ht (measure_mono hst)

private theorem memLp_of_continuousOn_compact_carrier
    {d : ℕ} {F : TimeVelocity d → ℝ} {U Q K : Set (TimeVelocity d)}
    (hF : ContinuousOn F U) (hKU : K ⊆ U) (hKcompact : IsCompact K)
    (hQK : Q ⊆ K) :
    MemLp F (parabolicExponent d) (volume.restrict Q) := by
  have hFK : ContinuousOn F K := hF.mono hKU
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨A, hA⟩ := hKcompact.exists_bound_of_continuousOn hFK
  have hKmem : MemLp F (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound (hFK.aestronglyMeasurable hKmeas) A ?_
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hA z hz
  exact hKmem.mono_measure (Measure.restrict_mono_set volume hQK)

private theorem parabolicLpNormOn_abs_div
    {d : ℕ} {F : TimeVelocity d → ℝ} {Q : Set (TimeVelocity d)} {D : ℝ}
    (hD : 0 < D) (hFmem : MemLp F (parabolicExponent d) (volume.restrict Q)) :
    parabolicLpNormOn d (fun z ↦ |F z| / D) Q =
      D⁻¹ * parabolicLpNormOn d F Q := by
  have hFtop : parabolicELpNormOn d F Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFmem.eLpNorm_ne_top
  have habsmem : MemLp (fun z ↦ |F z|) (parabolicExponent d) (volume.restrict Q) := by
    simpa only [Real.norm_eq_abs] using hFmem.norm
  have habstop : parabolicELpNormOn d (fun z ↦ |F z|) Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using habsmem.eLpNorm_ne_top
  have hinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hD.le
  calc
    parabolicLpNormOn d (fun z ↦ |F z| / D) Q =
        parabolicLpNormOn d (D⁻¹ • fun z ↦ |F z|) Q := by
      congr 2
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    _ = D⁻¹ * parabolicLpNormOn d (fun z ↦ |F z|) Q := by
      unfold parabolicLpNormOn parabolicELpNormOn
      rw [eLpNorm_const_smul, ENNReal.toReal_mul]
      simp only [Real.enorm_of_nonneg hinv, ENNReal.toReal_ofReal hinv]
    _ = D⁻¹ * parabolicLpNormOn d F Q := by
      congr 1
      unfold parabolicLpNormOn parabolicELpNormOn
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_enorm_ae habsmem.aestronglyMeasurable hFmem.aestronglyMeasurable
      filter_upwards [] with z
      exact Real.enorm_abs (F z)

private theorem source_supersolution_const_sub_div
    {d : ℕ} {B : CoefficientField d} {M D : ℝ} {F u : TimeVelocity d → ℝ}
    {Q : Set (TimeVelocity d)} (hD : 0 < D)
    (heq : ∀ z ∈ Q, parabolicOperator B u z = F z) :
    IsParabolicSupersolutionOn B (fun z ↦ -(|F z| / D))
      (fun z ↦ (M - u z) / D) Q := by
  intro z hz
  have hoperator : parabolicOperator B (fun y ↦ (M - u y) / D) z =
      D⁻¹ * (-parabolicOperator B u z) := by
    calc
      parabolicOperator B (fun y ↦ (M - u y) / D) z =
          parabolicOperator B (D⁻¹ • fun y ↦ M - u y) z := by
        congr 1
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
        ring
      _ = D⁻¹ * parabolicOperator B (fun y ↦ M - u y) z :=
        parabolicOperator_const_smul B D⁻¹ (fun y ↦ M - u y) z
      _ = D⁻¹ * (-parabolicOperator B u z) := by
        rw [parabolicOperator_const_sub]
  rw [hoperator, heq z hz]
  have hquotient : F z / D ≤ |F z| / D :=
    (div_le_div_iff_of_pos_right hD).mpr (le_abs_self (F z))
  calc
    -(|F z| / D) ≤ -(F z / D) := neg_le_neg hquotient
    _ = D⁻¹ * (-F z) := by field_simp [hD.ne']

/-- A supplied `SourceDensityToPoint` relation yields raw-equation source-aware level growth
on a physical box. -/
theorem source_level_growth_of_low_set_density
    {d : Nat} {lam Lam beta g C : Real}
    (hdtp : SourceDensityToPoint d lam Lam beta g C)
    {R nu t0 M : Real} {v0 : PDE.Vec d}
    (hR : 0 < R) (hnu : 0 < nu) (hg : g < 1)
    (U : Set (TimeVelocity d)) (B : CoefficientField d)
    (F u : TimeVelocity d → Real) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 R t0 v0 ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn Real 2 u U)
    (hF : ContinuousOn F U)
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 R t0 v0))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 R t0 v0))
    (heq : ∀ z ∈ parabolicBox 1 R t0 v0,
      parabolicOperator B u z = F z)
    (hM : ∀ z ∈ parabolicClosedBox 1 R t0 v0, u z ≤ M)
    (htop : nu ≤ u (t0 + R ^ 2, v0))
    (hdensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 R t0 v0 ∩ {z | u z ≤ nu / 2})).toReal) :
    nu * ((2 - g) / (2 * (1 - g))) ≤
      M + (C / (1 - g)) * R ^ ((d : Real) / ((d : Real) + 1)) *
        parabolicLpNormOn d F (parabolicBox 1 R t0 v0) := by
  let Q := parabolicBox 1 R t0 v0
  let Qclosed := parabolicClosedBox 1 R t0 v0
  let D := M - nu / 2
  let w : TimeVelocity d → Real := fun z ↦ (M - u z) / D
  let Fabs : TimeVelocity d → Real := fun z ↦ |F z| / D
  have hterminal : (t0 + R ^ 2, v0) ∈ Qclosed :=
    terminalCenter_mem_parabolicClosedBox hR
  have hnuM : nu ≤ M := htop.trans (hM _ hterminal)
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hQsubset : Q ⊆ Qclosed := parabolicBox_subset_parabolicClosedBox
  have hFmem : MemLp F (parabolicExponent d) (volume.restrict Q) :=
    memLp_of_continuousOn_compact_carrier hF hclosed
      (isCompact_parabolicClosedBox 1 R t0 v0) hQsubset
  have hFtop : parabolicELpNormOn d F Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFmem.eLpNorm_ne_top
  have hFabsmem : MemLp Fabs (parabolicExponent d) (volume.restrict Q) := by
    have habsmem : MemLp (fun z ↦ |F z|) (parabolicExponent d)
        (volume.restrict Q) := by
      simpa only [Real.norm_eq_abs] using hFmem.norm
    rw [show Fabs = D⁻¹ • fun z ↦ |F z| by
      funext z
      dsimp only [Fabs]
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring]
    exact habsmem.const_smul D⁻¹
  have hFabstop : parabolicELpNormOn d Fabs Q ≠ ⊤ := by
    simpa only [parabolicELpNormOn] using hFabsmem.eLpNorm_ne_top
  have hwnonneg : IsNonnegativeOn w Q := by
    intro z hz
    dsimp [w]
    exact div_nonneg (sub_nonneg.mpr (hM z (hQsubset hz))) hD.le
  have hFabsnonneg : IsNonnegativeOn Fabs Q := by
    intro z _hz
    dsimp [Fabs]
    exact div_nonneg (abs_nonneg (F z)) hD.le
  have hwregular : ContDiffOn Real 2 w U := by
    dsimp only [w]
    exact contDiffOn_const_sub_div hu
  have hFabscontinuous : ContinuousOn Fabs U := by
    dsimp only [Fabs]
    exact hF.abs.div_const D
  have hwsuper : IsParabolicSupersolutionOn B (fun z ↦ -Fabs z) w Q := by
    dsimp only [Fabs, w]
    exact source_supersolution_const_sub_div hD (by simpa only [Q] using heq)
  have hlow : Q ∩ {z | u z ≤ nu / 2} ⊆ Q ∩ {z | 1 ≤ w z} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change 1 ≤ (M - u z) / D
    apply (le_div_iff₀ hD).mpr
    dsimp [D]
    have huz : u z ≤ nu / 2 := hz.2
    linarith
  have hsuperclosed : Q ∩ {z | 1 ≤ w z} ⊆ Qclosed := fun _ hz ↦ hQsubset hz.1
  have hvolfin : (volume : Measure (TimeVelocity d)) (Q ∩ {z | 1 ≤ w z}) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono hsuperclosed)
  have hwdensity : beta * ((volume : Measure (TimeVelocity d)) Q).toReal ≤
      ((volume : Measure (TimeVelocity d)) (Q ∩ {z | 1 ≤ w z})).toReal :=
    hdensity.trans (volume_toReal_mono_of_subset hvolfin hlow)
  have hcenter : v0 ∈ velocityClosedCube v0 (R / 2) :=
    center_mem_velocityClosedCube hR
  have hpoint : g ≤ w (t0 + R ^ 2, v0) +
      C * R ^ ((d : Real) / ((d : Real) + 1)) * parabolicLpNormOn d Fabs Q := by
    simpa only [one_mul] using hdtp.scaled hR one_pos U B Fabs w hU hclosed hB
      hwregular hFabscontinuous hwnonneg hFabsnonneg hlower hupper hwsuper hwdensity
      v0 hcenter
  have hnorm : parabolicLpNormOn d Fabs Q = D⁻¹ * parabolicLpNormOn d F Q := by
    dsimp only [Fabs]
    exact parabolicLpNormOn_abs_div hD hFmem
  rw [hnorm] at hpoint
  have hterminalBound : w (t0 + R ^ 2, v0) ≤ (M - nu) / D := by
    dsimp only [w]
    apply (div_le_div_iff_of_pos_right hD).mpr
    linarith
  have hmain : g ≤ (M - nu) / D + C * R ^ ((d : Real) / ((d : Real) + 1)) *
      (D⁻¹ * parabolicLpNormOn d F Q) := hpoint.trans (add_le_add_left hterminalBound _)
  have hmul : g * D ≤ M - nu + C * R ^ ((d : Real) / ((d : Real) + 1)) *
      parabolicLpNormOn d F Q := by
    calc
      g * D ≤ ((M - nu) / D + C * R ^ ((d : Real) / ((d : Real) + 1)) *
          (D⁻¹ * parabolicLpNormOn d F Q)) * D :=
        mul_le_mul_of_nonneg_right hmain hD.le
      _ = M - nu + C * R ^ ((d : Real) / ((d : Real) + 1)) *
          parabolicLpNormOn d F Q := by
        field_simp [hD.ne']
  have hden : 0 < 2 * (1 - g) := by
    nlinarith
  have hden' : 1 - g ≠ 0 := ne_of_gt (sub_pos.mpr hg)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  calc
    nu * (2 - g) ≤ 2 * M * (1 - g) +
        2 * C * R ^ ((d : Real) / ((d : Real) + 1)) * parabolicLpNormOn d F Q := by
      dsimp [D] at hmul
      nlinarith
    _ = (M + (C / (1 - g)) * R ^ ((d : Real) / ((d : Real) + 1)) *
        parabolicLpNormOn d F Q) * (2 * (1 - g)) := by
      field_simp [hden']

/-- A positive-density low set forces source-aware algebraic level growth on
a physical parabolic box, with constants uniform in all local data. -/
theorem exists_source_level_growth_of_low_set_density
    (d : Nat) (hd : 0 < d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) (beta : Real)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    ∃ g C : Real, 0 < g ∧ g < 1 ∧ 0 ≤ C ∧
      ∀ {R nu t0 M : Real} {v0 : PDE.Vec d},
        0 < R → 0 < nu →
        ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
          (F u : TimeVelocity d → Real),
          IsOpen U →
          parabolicClosedBox 1 R t0 v0 ⊆ U →
          IsContinuousCoefficientOn B U →
          ContDiffOn Real 2 u U →
          ContinuousOn F U →
          HasLowerEllipticityOn lam B (parabolicBox 1 R t0 v0) →
          HasUpperEllipticityOn Lam B (parabolicBox 1 R t0 v0) →
          (∀ z ∈ parabolicBox 1 R t0 v0,
            parabolicOperator B u z = F z) →
          (∀ z ∈ parabolicClosedBox 1 R t0 v0, u z ≤ M) →
          nu ≤ u (t0 + R ^ 2, v0) →
          beta * ((volume : Measure (TimeVelocity d))
            (parabolicBox 1 R t0 v0)).toReal ≤
            ((volume : Measure (TimeVelocity d))
              (parabolicBox 1 R t0 v0 ∩ {z | u z ≤ nu / 2})).toReal →
          nu * ((2 - g) / (2 * (1 - g))) ≤
            M + (C / (1 - g)) * R ^ ((d : Real) / ((d : Real) + 1)) *
              parabolicLpNormOn d F (parabolicBox 1 R t0 v0) := by
  obtain ⟨g, C, hg0, hg1, hC, hdtp⟩ :=
    exists_sourceDensityToPoint_positive d hd lam hlam Lam hlamLam beta hbeta0 hbeta1
  refine ⟨g, C, hg0, hg1, hC, ?_⟩
  intro R nu t0 M v0 hR hnu U B F u hU hclosed hB hu hF hlower hupper heq hM htop hdensity
  exact source_level_growth_of_low_set_density hdtp hR hnu hg1 U B F u hU hclosed hB hu hF
    hlower hupper heq hM htop hdensity

end

end HypoellipticAleksandrov.Parabolic
