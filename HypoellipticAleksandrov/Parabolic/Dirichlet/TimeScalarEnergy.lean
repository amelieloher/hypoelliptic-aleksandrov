module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy

/-!
# Scalar reverse-time energy representatives

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

private noncomputable def rawEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (u t)‖ ^ 2

private noncomputable def rawEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (g t) (u t)

private noncomputable def reverseTimeEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => ∫ r in Set.Ioc 0 t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T

private theorem integrable_rawEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) :
    Integrable (rawEnergy hΩ T u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hu : MemLp (fun t => valueCLM hΩ (u t)) 2 (reverseTimeVolume T) :=
    (MeasureTheory.Lp.memLp u).continuousLinearMap_comp (valueCLM hΩ)
  unfold rawEnergy
  exact hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

private theorem integrable_rawEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (rawEnergyRate hΩ T u g) (reverseTimeVolume T) := by
  unfold rawEnergyRate
  exact
    (integrable_reverseTimeDualPairing hΩ T u g).const_mul 2

private theorem continuousOn_reverseTimeEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    ContinuousOn (reverseTimeEnergyPrimitive hΩ T u g) (Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_rawEnergyRate hΩ T u g).integrableOn

private theorem reverseTimeEnergyPrimitive_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    reverseTimeEnergyPrimitive hΩ T u g t -
        reverseTimeEnergyPrimitive hΩ T u g s =
      ∫ r in Ioc s t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
  change (∫ r in Ioc 0 t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T) -
      ∫ r in Ioc 0 s, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_rawEnergyRate hΩ T u g).intervalIntegrable
      (integrable_rawEnergyRate hΩ T u g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]

private theorem exists_strict_test_collar
    (T : ℝ) (hT : 0 < T) (eta : ReverseTimeScalarTest T) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧
      tsupport (eta : ℝ → ℝ) ⊆ Ioo a b ∧ tsupport eta.deriv ⊆ Ioo a b := by
  by_cases hsupport : (tsupport (eta : ℝ → ℝ)).Nonempty
  · obtain ⟨lo, hlo, hloMin⟩ :=
      eta.hasCompactSupport.exists_isMinOn hsupport continuousOn_id
    obtain ⟨hi, hhi, hhiMax⟩ :=
      eta.hasCompactSupport.exists_isMaxOn hsupport continuousOn_id
    have hloIoo : lo ∈ Ioo (0 : ℝ) T := eta.tsupport_subset hlo
    have hhiIoo : hi ∈ Ioo (0 : ℝ) T := eta.tsupport_subset hhi
    obtain ⟨a, ha0, halo⟩ := exists_between hloIoo.1
    obtain ⟨b, hhib, hbT⟩ := exists_between hhiIoo.2
    have hlohi : lo ≤ hi := hloMin hhi
    refine ⟨a, b, ha0, ?_, hbT, ?_, ?_⟩
    · exact lt_of_lt_of_le halo (hlohi.trans_lt hhib).le
    · intro t ht
      have hlot : lo ≤ t := hloMin ht
      have hthi : t ≤ hi := hhiMax ht
      exact ⟨lt_of_lt_of_le halo hlot, lt_of_le_of_lt hthi hhib⟩
    · have hderivSupport : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) := by
        rw [ReverseTimeScalarTest.deriv, tsupport]
        exact closure_minimal support_deriv_subset (isClosed_tsupport _)
      exact hderivSupport.trans (by
        intro t ht
        have hlot : lo ≤ t := hloMin ht
        have hthi : t ≤ hi := hhiMax ht
        exact ⟨lt_of_lt_of_le halo hlot, lt_of_le_of_lt hthi hhib⟩)
  · have heta : (eta : ℝ → ℝ) = 0 := by
      funext t
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hsupport ⟨t, ht⟩
    have hderiv : eta.deriv = 0 := by
      apply funext
      intro t
      rw [eta.deriv_apply, heta]
      simp
    refine ⟨T / 3, 2 * T / 3, by linarith, by linarith, by linarith, ?_, ?_⟩
    · rw [heta]
      simp
    · rw [hderiv]
      simp

private theorem integral_reverseTime_eq_integral_Icc_of_tsupport_subset
    {T a b : ℝ} {F phi : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) (hphi : tsupport phi ⊆ Ioo a b) :
    (∫ t, F t * phi t ∂reverseTimeVolume T) = ∫ t in Icc a b, F t * phi t := by
  change (∫ t in Ioo (0 : ℝ) T, F t * phi t) = ∫ t in Icc a b, F t * phi t
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hK
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun hts => ht.2
    ⟨le_of_lt (hphi hts).1, le_of_lt (hphi hts).2⟩)]
  ring

private theorem integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment
    {a b : ℝ} {E Q : ℝ → ℝ} (hab : a ≤ b)
    (hE : Continuous E) (hQ : Continuous Q)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      E t - E s = ∫ r in Icc s t, Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, E t * deriv eta t) =
      -(∫ t in Icc a b, Q t * eta t) := by
  have hQIcc : IntegrableOn Q (Icc a b) volume := hQ.integrableOn_Icc
  have hEIcc : IntegrableOn E (Icc a b) volume := hE.integrableOn_Icc
  have hetaIcc : IntegrableOn eta (Icc a b) volume := heta.continuous.integrableOn_Icc
  have hderivIcc : IntegrableOn (deriv eta) (Icc a b) volume :=
    (heta.continuous_deriv (by simp)).integrableOn_Icc
  have hEformula : ∀ t ∈ Icc a b, E t = PDE.intervalPrimitive a Q t + E a := by
    intro t ht
    have h := hinc a ⟨le_rfl, hab⟩ t ht ht.1
    calc
      E t = (∫ r in Icc a t, Q r) + E a := by linarith
      _ = PDE.intervalPrimitive a Q t + E a := by
        rw [PDE.intervalPrimitive_eq_setIntegral_Icc ht.1]
  have hleft : (∫ t in Icc a b, E t * deriv eta t) =
      ∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change E t * deriv eta t = _
    rw [hEformula t ht]
  rw [hleft]
  calc
    (∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t) =
        ∫ t in Icc a b,
          PDE.intervalPrimitive a Q t * deriv eta t + E a * deriv eta t := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro t _
            ring
    _ = (∫ t in Icc a b, PDE.intervalPrimitive a Q t * deriv eta t) +
        ∫ t in Icc a b, E a * deriv eta t := by
          rw [integral_add]
          · exact ((PDE.continuousOn_intervalPrimitive hab hQIcc).mul
              (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
          · simpa only [Pi.mul_apply] using hderivIcc.const_mul (E a)
    _ = -(∫ t in Icc a b, Q t * eta t) := by
      rw [PDE.intervalPrimitive_scalar_weak_identity_Icc hQIcc heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc heta.contDiffOn hab]
        have ha : eta a = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1
        have hb : eta b = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2
        rw [ha, hb]
        ring
      rw [integral_const_mul, htail]
      ring

private theorem abs_sq_sub_le_of_bounds
    {a b N delta y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hdelta : 0 ≤ delta) (hy : 0 ≤ y)
    (hdiff : |a - b| ≤ N * delta)
    (hsum : a + b ≤ N * delta + 2 * N * y) :
    |a ^ 2 - b ^ 2| ≤ N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    (a + b) * |a - b| ≤ (N * delta + 2 * N * y) * (N * delta) := by
      exact mul_le_mul hsum hdiff (abs_nonneg _) (by positivity)
    _ = N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by ring

private theorem abs_sqNorm_valueCLM_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    |‖valueCLM hΩ x‖ ^ 2 - ‖valueCLM hΩ y‖ ^ 2| ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 +
        2 * ‖valueCLM hΩ‖ ^ 2 * ‖y‖ * ‖x - y‖ := by
  let L := valueCLM hΩ
  have hLx : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hLy : ‖L y‖ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
  have hLsub : ‖L (x - y)‖ ≤ ‖L‖ * ‖x - y‖ := L.le_opNorm (x - y)
  have hx : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by
        congr 1
        abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hLx' : ‖L x‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) :=
    hLx.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hdiff : |‖L x‖ - ‖L y‖| ≤ ‖L‖ * ‖x - y‖ := by
    calc
      |‖L x‖ - ‖L y‖| ≤ ‖L x - L y‖ := abs_norm_sub_norm_le _ _
      _ = ‖L (x - y)‖ := by rw [L.map_sub]
      _ ≤ ‖L‖ * ‖x - y‖ := hLsub
  have hfactor : ‖L x‖ + ‖L y‖ ≤ ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by
    calc
      ‖L x‖ + ‖L y‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) + ‖L‖ * ‖y‖ :=
        add_le_add hLx' hLy
      _ = ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by ring
  exact abs_sq_sub_le_of_bounds (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hdiff hfactor

private theorem integral_mul_norm_le_sqrt_mul_sqrt
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using hholder

private theorem memLp_on_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem tendsto_integral_abs_valueSq_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (μ : Measure ℝ) (u : ℝ → H10HilbertGraph hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ)
    (hu : MemLp u (2 : ℝ≥0∞) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 : ℝ≥0∞) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let C : ℝ := ‖valueCLM hΩ‖ ^ 2
  have hUsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hU.sqrt
  have hfirst : Tendsto (fun h : ℝ =>
      C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hU
  have hsecond : Tendsto (fun h : ℝ =>
      2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
        √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ =>
        2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ))
        (𝓝[>] 0) (𝓝 (2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ)) : Filter ℝ) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul hUsqrt
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [huh] with h huh
    have hdu : MemLp (fun t => uh h t - u t) (2 : ℝ≥0∞) μ := huh.sub hu
    have hLuh : MemLp (fun t => valueCLM hΩ (uh h t)) (2 : ℝ≥0∞) μ :=
      huh.continuousLinearMap_comp (valueCLM hΩ)
    have hLu : MemLp (fun t => valueCLM hΩ (u t)) (2 : ℝ≥0∞) μ :=
      hu.continuousLinearMap_comp (valueCLM hΩ)
    have hleft : Integrable (fun t =>
        |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|) μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_def] using
        ((hLuh.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).sub
          (hLu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).norm
    have hterm1 : Integrable (fun t =>
        C * ‖uh h t - u t‖ ^ 2) μ :=
      (hdu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    have hterm2 : Integrable (fun t =>
        2 * C * ‖u t‖ * ‖uh h t - u t‖) μ :=
      by
        apply ((hu.norm).integrable_mul hdu.norm).const_mul (2 * C) |>.congr
        filter_upwards with t
        change 2 * C *
          ((fun x => ‖u x‖) * fun x => ‖uh h x - u x‖) t = _
        simp only [Pi.mul_apply]
        ring
    have hpoint : ∀ t : ℝ,
        |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ≤
          C * ‖uh h t - u t‖ ^ 2 + 2 * C * ‖u t‖ * ‖uh h t - u t‖ := by
      intro t
      simpa only [C] using abs_sqNorm_valueCLM_sub_le hΩ (uh h t) (u t)
    have hmono := integral_mono hleft (hterm1.add hterm2) hpoint
    have hholder := integral_mul_norm_le_sqrt_mul_sqrt
      u (fun t => uh h t - u t) hu hdu
    have hterm2_eq : (∫ t,
        2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) =
        2 * C *
          (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
      rw [show (fun t : ℝ =>
          2 * C * ‖u t‖ * ‖uh h t - u t‖) =
          fun t => (2 * C) *
            (‖u t‖ * ‖uh h t - u t‖) by
            funext t
            ring, integral_const_mul]
    calc
      (∫ t, |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) ≤
          ∫ t, C * ‖uh h t - u t‖ ^ 2 +
            2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ := hmono
      _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          (∫ t, 2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
            rw [integral_add hterm1 hterm2, integral_const_mul]
      _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          2 * C *
            (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
            rw [hterm2_eq]
      _ ≤ C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
          2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
            √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) := by
            apply add_le_add_right
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hholder (by positivity : 0 ≤ 2 * C)
  · simpa only [add_zero] using hfirst.add hsecond

private theorem tendsto_forwardSteklov_valueSq_error_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      |‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
        ‖valueCLM hΩ (u t)‖ ^ 2|) (𝓝[>] 0) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hK : Icc a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ, reverseTimeVolume, reverseTimeOpenInterval,
      Measure.restrict_restrict_of_subset hK] using
      (MeasureTheory.Lp.memLp u).restrict (Icc a b)
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h u) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeForwardSteklov T h u)
      (continuous_reverseTimeForwardSteklov T h hh u) a b
  have hU := tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab hb
  change Tendsto (fun h : ℝ => ∫ t,
    |‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
      ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) (𝓝[>] 0) (𝓝 0)
  exact tendsto_integral_abs_valueSq_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (fun h t => reverseTimeForwardSteklov T h u t)
    hu huh hU

private theorem tendsto_backwardSteklov_valueSq_error_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t in Icc a b,
      |‖valueCLM hΩ (reverseTimeBackwardSteklov T h u t)‖ ^ 2 -
        ‖valueCLM hΩ (u t)‖ ^ 2|) (𝓝[>] 0) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hK : Icc a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ, reverseTimeVolume, reverseTimeOpenInterval,
      Measure.restrict_restrict_of_subset hK] using
      (MeasureTheory.Lp.memLp u).restrict (Icc a b)
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeBackwardSteklov T h u) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeBackwardSteklov T h u)
      (continuous_reverseTimeBackwardSteklov T h hh u) a b
  have hU := tendsto_backwardSteklov_sqNorm_integral_on_Icc T u ha hab hb
  change Tendsto (fun h : ℝ => ∫ t,
    |‖valueCLM hΩ (reverseTimeBackwardSteklov T h u t)‖ ^ 2 -
      ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) (𝓝[>] 0) (𝓝 0)
  exact tendsto_integral_abs_valueSq_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (fun h t => reverseTimeBackwardSteklov T h u t)
    hu huh hU

private theorem tendsto_integral_mul_of_tendsto_integral_abs
    {μ : Measure ℝ} {F : ℝ → ℝ → ℝ} {f phi : ℝ → ℝ}
    (hF : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (F h) μ)
    (hf : Integrable f μ) (hphi : AEStronglyMeasurable phi μ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ‖phi t‖ ≤ C)
    (hlim : Tendsto (fun h : ℝ => ∫ t, |F h t - f t| ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t, F h t * phi t ∂μ) (𝓝[>] 0)
      (𝓝 (∫ t, f t * phi t ∂μ)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnorm : ∀ t : ℝ, ‖‖phi t‖‖ ≤ C := by
    intro t
    simpa only [norm_norm] using hC t
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact (norm_nonneg _).trans this
  have herr : Tendsto (fun h : ℝ => ∫ t, (F h t - f t) * phi t ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · filter_upwards with h
      exact norm_nonneg _
    · filter_upwards [hF] with h hF
      have hdiff : Integrable (fun t => F h t - f t) μ := hF.sub hf
      have hprod : Integrable (fun t => |F h t - f t| * ‖phi t‖) μ :=
        hdiff.norm.mul_bdd hphi.norm (Eventually.of_forall fun t => hCnorm t)
      calc
        ‖∫ t, (F h t - f t) * phi t ∂μ‖ ≤
            ∫ t, ‖(F h t - f t) * phi t‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ t, |F h t - f t| * ‖phi t‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with t
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ ∫ t, C * |F h t - f t| ∂μ := by
          apply integral_mono
          · exact hprod
          · exact hdiff.norm.const_mul C
          · intro t
            calc
              |F h t - f t| * ‖phi t‖ ≤ |F h t - f t| * C :=
                mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)
              _ = C * |F h t - f t| := mul_comm _ _
        _ = C * (∫ t, |F h t - f t| ∂μ) :=
          integral_const_mul C (fun t => |F h t - f t|)
    · simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have hsum : Tendsto (fun h : ℝ =>
      (∫ t, (F h t - f t) * phi t ∂μ) + ∫ t, f t * phi t ∂μ)
      (𝓝[>] 0) (𝓝 (∫ t, f t * phi t ∂μ)) := by
    simpa only [zero_add] using herr.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [hF] with h hF
  have hdiff : Integrable (fun t => F h t - f t) μ := hF.sub hf
  have hprod : Integrable (fun t => (F h t - f t) * phi t) μ :=
    hdiff.mul_bdd hphi (Eventually.of_forall fun t => hC t)
  have hraw : Integrable (fun t => f t * phi t) μ :=
    hf.mul_bdd hphi (Eventually.of_forall fun t => hC t)
  rw [← integral_add hprod hraw]
  apply integral_congr_ae
  filter_upwards with t
  ring

private noncomputable def forwardSteklovEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2

private noncomputable def forwardSteklovEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (reverseTimeForwardSteklov T h g t)
    (reverseTimeForwardSteklov T h u t)

private theorem abs_two_mul_sub (x y : ℝ) :
    |2 * x - 2 * y| = 2 * |x - y| := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

private theorem abs_forwardSteklovEnergyRate_sub_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (t : ℝ) :
    |forwardSteklovEnergyRate hΩ T h u g t - rawEnergyRate hΩ T u g t| =
      2 * |(reverseTimeForwardSteklov T h g t)
        (reverseTimeForwardSteklov T h u t) - (g t) (u t)| := by
  change |2 * (reverseTimeForwardSteklov T h g t)
      (reverseTimeForwardSteklov T h u t) - 2 * (g t) (u t)| = _
  exact abs_two_mul_sub _ _

private theorem rawEnergy_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_test_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hraw : Integrable (rawEnergy hΩ T u) (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_rawEnergy hΩ T u).restrict
  have hpair : Integrable (fun t => (g t) (u t)) (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_reverseTimeDualPairing hΩ T u g).restrict
  have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t, forwardSteklovEnergy hΩ T h u t * eta.deriv t ∂reverseTimeVolume T) =
        -(∫ t, forwardSteklovEnergyRate hΩ T h u g t * eta t ∂reverseTimeVolume T) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
      (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
      with h hh hsmall
    have hE : Continuous (forwardSteklovEnergy hΩ T h u) := by
      exact ((valueCLM hΩ).continuous.comp
        (continuous_reverseTimeForwardSteklov T h hh u)).norm.pow 2
    have hQ : Continuous (forwardSteklovEnergyRate hΩ T h u g) := by
      exact continuous_const.mul
        ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
          (continuous_reverseTimeForwardSteklov T h hh u))
    have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
        forwardSteklovEnergy hΩ T h u t - forwardSteklovEnergy hΩ T h u s =
          ∫ r in Icc s t, forwardSteklovEnergyRate hΩ T h u g r := by
      intro s hs t ht hst
      change ‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
          ‖valueCLM hΩ (reverseTimeForwardSteklov T h u s)‖ ^ 2 = _
      calc
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u t)‖ ^ 2 -
            ‖valueCLM hΩ (reverseTimeForwardSteklov T h u s)‖ ^ 2 =
            2 * (∫ r in Icc s t,
              (reverseTimeForwardSteklov T h g r)
                (reverseTimeForwardSteklov T h u r)) :=
          reverseTimeForwardSteklov_energy_identity hΩ T hT u g hderiv hh
            (le_trans ha.le hs.1) hst
            (by linarith [ht.2, hsmall])
        _ = ∫ r in Icc s t, forwardSteklovEnergyRate hΩ T h u g r := by
          change 2 * (∫ r in Icc s t,
              (reverseTimeForwardSteklov T h g r)
                (reverseTimeForwardSteklov T h u r)) =
            ∫ r in Icc s t, 2 * (reverseTimeForwardSteklov T h g r)
              (reverseTimeForwardSteklov T h u r)
          rw [integral_const_mul]
    rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
      integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
    exact integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment hab.le hE hQ hinc
      (eta.contDiff.of_le (by simp)) heta
  have hEForward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (forwardSteklovEnergy hΩ T h u) (volume.restrict (Icc a b)) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    exact ((valueCLM hΩ).continuous.comp
      (continuous_reverseTimeForwardSteklov T h hh u)).norm.pow 2 |>.integrableOn_Icc
  have hQForward : ∀ᶠ h : ℝ in 𝓝[>] 0,
      Integrable (forwardSteklovEnergyRate hΩ T h u g) (volume.restrict (Icc a b)) := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    exact (continuous_const.mul
      ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
        (continuous_reverseTimeForwardSteklov T h hh u))).integrableOn_Icc
  have hEabs := tendsto_forwardSteklov_valueSq_error_on_Icc hΩ T u ha hab.le hb
  have hQabs := tendsto_forwardSteklov_dualPairing_integral_on_Icc hΩ T u g ha hab.le hb
  have hEtest := tendsto_integral_mul_of_tendsto_integral_abs hEForward hraw
    eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le hEabs
  have hQraw : Integrable (rawEnergyRate hΩ T u g) (volume.restrict (Icc a b)) :=
    hpair.const_mul 2
  have hQabs2 : Tendsto (fun h : ℝ => ∫ t in Icc a b,
      |forwardSteklovEnergyRate hΩ T h u g t - rawEnergyRate hΩ T u g t|)
      (𝓝[>] 0) (𝓝 0) := by
    convert tendsto_const_nhds.mul hQabs using 1
    · funext h
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      exact abs_forwardSteklovEnergyRate_sub_eq hΩ T h u g t
    · norm_num
  have hQtest := tendsto_integral_mul_of_tendsto_integral_abs hQForward hQraw
    eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le hQabs2
  have hforwardIcc : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, forwardSteklovEnergy hΩ T h u t * eta.deriv t) =
        -(∫ t in Icc a b, forwardSteklovEnergyRate hΩ T h u g t * eta t) := by
    filter_upwards [hforward] with h hh
    rw [← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
      ← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
    exact hh
  have hIccLimit := hEtest.add hQtest
  have hConst : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
      (𝓝 ((∫ t in Icc a b, rawEnergy hΩ T u t * eta.deriv t) +
        ∫ t in Icc a b, rawEnergyRate hΩ T u g t * eta t)) := by
    apply hIccLimit.congr'
    filter_upwards [hforwardIcc] with h hh
    linarith
  have hzeroIcc : (∫ t in Icc a b, rawEnergy hΩ T u t * eta.deriv t) +
      ∫ t in Icc a b, rawEnergyRate hΩ T u g t * eta t = 0 := by
    exact tendsto_nhds_unique hConst tendsto_const_nhds
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  linarith

private theorem integrable_reverseTimeEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (reverseTimeEnergyPrimitive hΩ T u g) (reverseTimeVolume T) := by
  change IntegrableOn (reverseTimeEnergyPrimitive hΩ T u g) (Ioo (0 : ℝ) T) volume
  exact (continuousOn_reverseTimeEnergyPrimitive hΩ T u g).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

private theorem integrable_mul_reverseTimeScalarTest_deriv
    {T : ℝ} {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T))
    (eta : ReverseTimeScalarTest T) :
    Integrable (fun t => f t * eta.deriv t) (reverseTimeVolume T) := by
  obtain ⟨C, hC⟩ := eta.exists_norm_deriv_le
  apply hf.mul_bdd eta.contDiff_deriv.continuous.aestronglyMeasurable
  filter_upwards with t
  exact hC t

private theorem reverseTimeEnergyPrimitive_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, reverseTimeEnergyPrimitive hΩ T u g t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
  have hrate := integrable_rawEnergyRate hΩ T u g
  have hrateIcc : IntegrableOn (rawEnergyRate hΩ T u g) (Icc (0 : ℝ) T) volume := by
    change Integrable (rawEnergyRate hΩ T u g) (volume.restrict (Icc (0 : ℝ) T))
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc] using hrate
  have hae : (fun t => reverseTimeEnergyPrimitive hΩ T u g t * eta.deriv t) =ᵐ[
      reverseTimeVolume T] fun t =>
        PDE.intervalPrimitive 0 (rawEnergyRate hΩ T u g) t * _root_.deriv eta t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change (∫ r in Ioc 0 t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T) *
        eta.deriv t = _
    rw [show (∫ r in Ioc 0 t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T) =
        ∫ r in Ioc 0 t, rawEnergyRate hΩ T u g r ∂volume by
      simp only [reverseTimeVolume, reverseTimeOpenInterval,
        Measure.restrict_restrict measurableSet_Ioc]
      rw [inter_eq_left.mpr]
      intro r hr
      exact ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩,
      (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
      PDE.intervalPrimitive]
  calc
    (∫ t, reverseTimeEnergyPrimitive hΩ T u g t * eta.deriv t
      ∂reverseTimeVolume T) =
        ∫ t, PDE.intervalPrimitive 0 (rawEnergyRate hΩ T u g) t * _root_.deriv eta t
          ∂reverseTimeVolume T := integral_congr_ae hae
    _ = -(∫ t, rawEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo hrateIcc
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

private theorem exists_continuous_reverseTimeScalarEnergyRepresentative_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T] rawEnergy hΩ T u ∧
      ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
  let defect : ℝ → ℝ := fun t => rawEnergy hΩ T u t - reverseTimeEnergyPrimitive hΩ T u g t
  have hdefInt : Integrable defect (reverseTimeVolume T) :=
    (integrable_rawEnergy hΩ T u).sub (integrable_reverseTimeEnergyPrimitive hΩ T u g)
  have hdefZero : ∀ eta : ReverseTimeScalarTest T,
      (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) = 0 := by
    intro eta
    have hrawInt := integrable_mul_reverseTimeScalarTest_deriv
      (integrable_rawEnergy hΩ T u) eta
    have hprimInt := integrable_mul_reverseTimeScalarTest_deriv
      (integrable_reverseTimeEnergyPrimitive hΩ T u g) eta
    rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
        (∫ t, rawEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) -
          ∫ t, reverseTimeEnergyPrimitive hΩ T u g t * eta.deriv t
            ∂reverseTimeVolume T by
      rw [← integral_sub hrawInt hprimInt]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [defect]
      ring,
      rawEnergy_test_deriv hΩ T hT u g hderiv eta,
      reverseTimeEnergyPrimitive_test_deriv hΩ T u g eta]
    ring
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt hdefZero
  let e : ℝ → ℝ := fun t => reverseTimeEnergyPrimitive hΩ T u g t + c
  have heCont : ContinuousOn e (Icc 0 T) :=
    (continuousOn_reverseTimeEnergyPrimitive hΩ T u g).add continuousOn_const
  have heAE : e =ᵐ[reverseTimeVolume T] rawEnergy hΩ T u := by
    filter_upwards [hc] with t ht
    dsimp only [defect] at ht
    dsimp only [e]
    linarith
  have heNonneg : ∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t := by
    have heIcc : e =ᵐ[volume.restrict (Icc (0 : ℝ) T)] rawEnergy hΩ T u := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heAE
    have hmaxAE : e =ᵐ[volume.restrict (Icc (0 : ℝ) T)] fun t => max (e t) 0 := by
      filter_upwards [heIcc] with t ht
      rw [ht]
      simp only [rawEnergy, max_eq_left (sq_nonneg _)]
    have hmaxCont : ContinuousOn (fun t => max (e t) 0) (Icc 0 T) := by
      exact heCont.sup continuousOn_const
    have heEqOn := Measure.eqOn_Icc_of_ae_eq volume hT.ne hmaxAE heCont hmaxCont
    intro t ht
    rw [heEqOn ht]
    exact le_max_right _ _
  refine ⟨e, heCont, heNonneg, heAE, ?_⟩
  intro s t hs ht hst
  calc
    e t - e s = reverseTimeEnergyPrimitive hΩ T u g t -
        reverseTimeEnergyPrimitive hΩ T u g s := by
          dsimp only [e]
          ring
    _ = ∫ r in Ioc s t, rawEnergyRate hΩ T u g r ∂reverseTimeVolume T :=
      reverseTimeEnergyPrimitive_sub hΩ T u g hs ht hst

/-- A continuous scalar reverse-time energy representative of a Gelfand weak
derivative on the closed reverse-time interval. -/
theorem exists_continuous_reverseTimeScalarEnergyRepresentative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ e : ℝ → ℝ,
      ContinuousOn e (Set.Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T]
        (fun t => ‖valueCLM hΩ (u t)‖ ^ 2) ∧
      ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
        e t - e s =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, heNonneg, heAE, heSub⟩ :=
    exists_continuous_reverseTimeScalarEnergyRepresentative_raw hΩ T hT u g hderiv
  refine ⟨e, heCont, heNonneg, ?_, ?_⟩
  · unfold rawEnergy at heAE
    exact heAE
  · intro s t hs ht hst
    rw [heSub s t hs ht hst]
    simp only [rawEnergyRate, integral_const_mul]


end HypoellipticAleksandrov.Parabolic.Dirichlet
