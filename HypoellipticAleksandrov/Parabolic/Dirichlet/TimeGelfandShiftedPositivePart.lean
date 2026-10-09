module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandShiftedPositivePartSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeShiftedPositivePartConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ShiftedPositivePartValueContinuity

/-!
# Shifted-positive-part reverse-time energy increments

This module proves the moving affine-threshold energy identity for the
canonical closed-time Hilbert representative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

private noncomputable def rawShiftedPositivePartEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) : ℝ → ℝ :=
  shiftedPositivePartEnergy hΩ M N u

private noncomputable def rawShiftedPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ) : ℝ → ℝ :=
  fun t => 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t

private noncomputable def reverseTimeShiftedPositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => ∫ r in Ioc 0 t,
    rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T

private theorem integrable_rawShiftedPositivePartEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) :
    Integrable (rawShiftedPositivePartEnergy hΩ M N u) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hu : MemLp (fun t => valueCLM hΩ (h10ShiftedPositivePart hΩ (u t)
      (reverseTimeAffineThreshold M N t))) 2 (reverseTimeVolume T) :=
    memLp_congr_ae (by
      filter_upwards [coeFn_reverseTimeShiftedPositivePart hΩ T M N u] with t ht
      exact congrArg (valueCLM hΩ) ht) |>.mp
      ((Lp.memLp (reverseTimeShiftedPositivePart hΩ T M N u)).continuousLinearMap_comp
        (valueCLM hΩ))
  unfold rawShiftedPositivePartEnergy shiftedPositivePartEnergy
  exact hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

private theorem integrable_rawShiftedPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g)
      (reverseTimeVolume T) := by
  have hp := integrable_reverseTimeDualPairing_shiftedPositivePart hΩ T M N u g
  have hm := integrable_reverseTimeShiftedPositivePart_spatialMass
    hΩ hΩbounded T M N u
  unfold rawShiftedPositivePartEnergyRate
  apply Integrable.const_mul
  unfold shiftedPositivePartEnergyRate
  apply (hp.sub (hm.const_mul (N : ℝ))).congr
  filter_upwards with t
  simp only [Pi.sub_apply]
  rw [spatialMassCLM_apply]

private theorem continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    ContinuousOn (reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g) (Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).integrableOn

private theorem reverseTimeShiftedPositivePartEnergyPrimitive_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g t -
        reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g s =
      ∫ r in Ioc s t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r
        ∂reverseTimeVolume T := by
  change (∫ r in Ioc 0 t, _ ∂reverseTimeVolume T) -
      (∫ r in Ioc 0 s, _ ∂reverseTimeVolume T) = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).intervalIntegrable
      (integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g).intervalIntegrable,
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
    have hloIoo := eta.tsupport_subset hlo
    have hhiIoo := eta.tsupport_subset hhi
    obtain ⟨a, ha0, halo⟩ := exists_between hloIoo.1
    obtain ⟨b, hhib, hbT⟩ := exists_between hhiIoo.2
    have hlohi : lo ≤ hi := hloMin hhi
    refine ⟨a, b, ha0, lt_of_lt_of_le halo (hlohi.trans_lt hhib).le, hbT, ?_, ?_⟩
    · intro t ht
      exact ⟨lt_of_lt_of_le halo (hloMin ht), lt_of_le_of_lt (hhiMax ht) hhib⟩
    · have hd : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) := by
        rw [ReverseTimeScalarTest.deriv, tsupport]
        exact closure_minimal support_deriv_subset (isClosed_tsupport _)
      exact hd.trans (by
        intro t ht
        exact ⟨lt_of_lt_of_le halo (hloMin ht), lt_of_le_of_lt (hhiMax ht) hhib⟩)
  · have heta : (eta : ℝ → ℝ) = 0 := by
      funext t
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hsupport ⟨t, ht⟩
    have hderiv : eta.deriv = 0 := by
      funext t
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

private theorem integral_energy_mul_deriv_eq_neg_integral_rate_of_increment
    {a b : ℝ} {E Q : ℝ → ℝ} (hab : a ≤ b)
    (hQ : Continuous Q)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      E t - E s = ∫ r in Icc s t, Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, E t * deriv eta t) = -(∫ t in Icc a b, Q t * eta t) := by
  have hQIcc : IntegrableOn Q (Icc a b) volume := hQ.integrableOn_Icc
  have hEformula : ∀ t ∈ Icc a b, E t = PDE.intervalPrimitive a Q t + E a := by
    intro t ht
    have h := hinc a ⟨le_rfl, hab⟩ t ht ht.1
    calc
      E t = (∫ r in Icc a t, Q r) + E a := by linarith
      _ = PDE.intervalPrimitive a Q t + E a := by
        rw [PDE.intervalPrimitive_eq_setIntegral_Icc ht.1]
  rw [show (∫ t in Icc a b, E t * deriv eta t) =
      ∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hEformula t ht]]
  calc
    (∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t) =
        (∫ t in Icc a b, PDE.intervalPrimitive a Q t * deriv eta t) +
          ∫ t in Icc a b, E a * deriv eta t := by
      rw [← integral_add]
      · apply setIntegral_congr_fun measurableSet_Icc
        intro t _
        ring
      · exact ((PDE.continuousOn_intervalPrimitive hab hQIcc).mul
          (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
      · exact (heta.continuous_deriv (by simp)).integrableOn_Icc.const_mul (E a)
    _ = -(∫ t in Icc a b, Q t * eta t) := by
      rw [PDE.intervalPrimitive_scalar_weak_identity_Icc hQIcc heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc heta.contDiffOn hab]
        have ha : eta a = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1)
        have hb : eta b = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2)
        rw [ha, hb]
        ring
      rw [integral_const_mul, htail]
      ring

private theorem eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < T)
    (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N
          (fun r => reverseTimeForwardSteklov T h u r) t * eta.deriv t) =
      -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun r => reverseTimeForwardSteklov T h u r)
          (fun r => reverseTimeForwardSteklov T h g r) t * eta t) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
    (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
    with h hh hsmall
  let x := fun r => reverseTimeForwardSteklov T h u r
  let y := fun r => reverseTimeForwardSteklov T h g r
  have hk : Continuous (reverseTimeAffineThreshold M N) :=
    continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp := (continuous_h10ShiftedPositivePart hΩ).comp
    ((continuous_reverseTimeForwardSteklov T h hh u).prodMk hk)
  have hQ : Continuous (fun r => 2 * shiftedPositivePartEnergyRate
      hΩ hΩbounded M N x y r) := by
    exact continuous_const.mul
      (((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hp).sub
        (continuous_const.mul
          (((spatialMassCLM hΩbounded).comp (valueCLM hΩ)).continuous.comp hp)))
  have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      shiftedPositivePartEnergy hΩ M N x t - shiftedPositivePartEnergy hΩ M N x s =
        ∫ r in Icc s t, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N x y r := by
    intro s hs t ht hst
    rw [reverseTimeForwardSteklov_shiftedPositivePart_energy_identity hΩ hΩbounded T hT
      M N u g hderiv hh (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall]),
      integral_const_mul]
  exact integral_energy_mul_deriv_eq_neg_integral_rate_of_increment hab.le hQ hinc
    (eta.contDiff.of_le (by simp)) heta

private theorem rawShiftedPositivePartEnergy_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
      ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_test_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hid := eventually_forwardSteklov_shiftedPositivePartEnergy_test_identity
    hΩ hΩbounded T hT M N u g hderiv eta ha hab hb heta
  have hE := tendsto_forwardSteklov_shiftedPositivePartEnergy_test
    hΩ M N T u eta ha hab hb
  have hQ := tendsto_forwardSteklov_shiftedPositivePartEnergyRate_test
    hΩ hΩbounded M N T u g eta ha hab hb
  have hzero : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
      (𝓝 ((∫ t in Icc a b, shiftedPositivePartEnergy hΩ M N u t * eta.deriv t) +
        2 * ∫ t in Icc a b,
          shiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t)) := by
    apply (hE.add (tendsto_const_nhds.mul hQ)).congr'
    filter_upwards [hid] with h hh
    have hfactor : (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate hΩ hΩbounded M N
        (fun r => reverseTimeForwardSteklov T h u r)
        (fun r => reverseTimeForwardSteklov T h g r) t * eta t) =
        2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate hΩ hΩbounded M N
          (fun r => reverseTimeForwardSteklov T h u r)
          (fun r => reverseTimeForwardSteklov T h g r) t * eta t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [hfactor] at hh
    exact (eq_neg_iff_add_eq_zero).mp hh
  have hz := tendsto_nhds_unique hzero tendsto_const_nhds
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  change _ = -(∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate
    hΩ hΩbounded M N u g t * eta t)
  rw [show (∫ t in Icc a b, 2 * shiftedPositivePartEnergyRate
      hΩ hΩbounded M N u g t * eta t) =
      2 * ∫ t in Icc a b, shiftedPositivePartEnergyRate
        hΩ hΩbounded M N u g t * eta t by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    ring]
  exact (eq_neg_iff_add_eq_zero).mpr hz

private theorem integrable_reverseTimeShiftedPositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g) (reverseTimeVolume T) := by
  change IntegrableOn _ (Ioo (0 : ℝ) T) volume
  exact (continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
    hΩ hΩbounded T M N u g).integrableOn_Icc.mono_set Ioo_subset_Icc_self

private theorem integrable_mul_reverseTimeScalarTest_deriv
    {T : ℝ} {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T))
    (eta : ReverseTimeScalarTest T) :
    Integrable (fun t => f t * eta.deriv t) (reverseTimeVolume T) := by
  obtain ⟨C, hC⟩ := eta.exists_norm_deriv_le
  apply hf.mul_bdd eta.contDiff_deriv.continuous.aestronglyMeasurable
  filter_upwards with t
  exact hC t

private theorem reverseTimeShiftedPositivePartEnergyPrimitive_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g t *
      eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g t * eta t
        ∂reverseTimeVolume T) := by
  have hr := integrable_rawShiftedPositivePartEnergyRate hΩ hΩbounded T M N u g
  have hrIcc : IntegrableOn (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g)
      (Icc (0 : ℝ) T) volume := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, IntegrableOn] using hr
  have hae : (fun t => reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g t * eta.deriv t) =ᵐ[reverseTimeVolume T]
      fun t => PDE.intervalPrimitive 0
        (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g) t * deriv eta t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change (∫ r in Ioc 0 t, _ ∂reverseTimeVolume T) * eta.deriv t = _
    rw [show (∫ r in Ioc 0 t, rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r
        ∂reverseTimeVolume T) = ∫ r in Ioc 0 t,
          rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂volume by
      simp only [reverseTimeVolume, reverseTimeOpenInterval,
        Measure.restrict_restrict measurableSet_Ioc]
      rw [inter_eq_left.mpr]
      intro r hr'
      exact ⟨hr'.1, lt_of_le_of_lt hr'.2 ht.2⟩,
      (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
      PDE.intervalPrimitive]
  calc
    _ = ∫ t, PDE.intervalPrimitive 0
        (rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g) t * deriv eta t
        ∂reverseTimeVolume T := integral_congr_ae hae
    _ = _ := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo hrIcc
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

private theorem exists_continuous_shiftedPositivePartEnergyRepresentative
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ e : ℝ → ℝ, ContinuousOn e (Icc 0 T) ∧
      e =ᵐ[reverseTimeVolume T] rawShiftedPositivePartEnergy hΩ M N u ∧
      ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
        e t - e s = ∫ r in Ioc s t,
          rawShiftedPositivePartEnergyRate hΩ hΩbounded M N u g r ∂reverseTimeVolume T := by
  let P := reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g
  let defect := fun t => rawShiftedPositivePartEnergy hΩ M N u t - P t
  have hdefInt : Integrable defect (reverseTimeVolume T) :=
    (integrable_rawShiftedPositivePartEnergy hΩ T M N u).sub
      (integrable_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g)
  have hdefZero : ∀ eta : ReverseTimeScalarTest T,
      (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) = 0 := by
    intro eta
    have hraw := integrable_mul_reverseTimeScalarTest_deriv
      (integrable_rawShiftedPositivePartEnergy hΩ T M N u) eta
    have hprim := integrable_mul_reverseTimeScalarTest_deriv
      (integrable_reverseTimeShiftedPositivePartEnergyPrimitive hΩ hΩbounded T M N u g) eta
    rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
        (∫ t, rawShiftedPositivePartEnergy hΩ M N u t * eta.deriv t
          ∂reverseTimeVolume T) -
        ∫ t, P t * eta.deriv t ∂reverseTimeVolume T by
      rw [← integral_sub hraw hprim]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [defect]
      ring,
      rawShiftedPositivePartEnergy_test_deriv hΩ hΩbounded T hT M N u g hderiv eta,
      reverseTimeShiftedPositivePartEnergyPrimitive_test_deriv hΩ hΩbounded T M N u g eta]
    ring
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt hdefZero
  let e := fun t => P t + c
  have heCont : ContinuousOn e (Icc 0 T) :=
    (continuousOn_reverseTimeShiftedPositivePartEnergyPrimitive
      hΩ hΩbounded T M N u g).add continuousOn_const
  have heAE : e =ᵐ[reverseTimeVolume T] rawShiftedPositivePartEnergy hΩ M N u := by
    filter_upwards [hc] with t ht
    dsimp only [defect, e] at ht ⊢
    linarith
  refine ⟨e, heCont, heAE, ?_⟩
  intro s t hs ht hst
  calc
    e t - e s = P t - P s := by dsimp only [e]; ring
    _ = _ := reverseTimeShiftedPositivePartEnergyPrimitive_sub
      hΩ hΩbounded T M N u g hs ht hst

/-- Moving-threshold shifted-positive-part energy increment for the canonical
closed-time Hilbert representative. -/
theorem reverseTimeHilbertRepresentative_shiftedPositivePart_norm_sq_increment
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (T : ℝ) (hT : 0 < T) (M N : ℝ≥0)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩)‖ ^ 2 -
      ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N s)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩)‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t,
        ((g r) (h10ShiftedPositivePart hΩ (u r)
            (reverseTimeAffineThreshold M N r)) -
          (N : ℝ) * spatialMassCLM hΩbounded
            (valueCLM hΩ (h10ShiftedPositivePart hΩ (u r)
              (reverseTimeAffineThreshold M N r))))
        ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, heAE, heInc⟩ :=
    exists_continuous_shiftedPositivePartEnergyRepresentative
      hΩ hΩbounded T hT M N u g hderiv
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let E : ℝ → ℝ := fun r => if hr : r ∈ Icc 0 T then
    ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, hr⟩)‖ ^ 2
    else 0
  have hECont : ContinuousOn E (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict E = fun r : (Icc 0 T) =>
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N (r : ℝ))
          (Ubar r)‖ ^ 2 := by
      funext r
      simp only [Set.domRestrict_apply, E, dif_pos r.2]
    rw [hEq]
    exact (continuous_norm.comp
      ((continuous_shiftedPositivePartValue_of_isBounded hΩbounded).comp
        (Ubar.continuous.prodMk
          ((continuous_const.add (continuous_real_toNNReal.mul continuous_const)).comp
            continuous_subtype_val)))).pow 2
  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hAE : E =ᵐ[volume.restrict (Icc 0 T)] e := by
    have hrep' : ∀ᵐ r ∂volume.restrict (Icc 0 T),
        ∀ hr : r ∈ Ioo 0 T, Ubar ⟨r, ⟨hr.1.le, hr.2.le⟩⟩ = valueCLM hΩ (u r) := by
      simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
        reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc, IntegrableOn] using hrep
    have he' : e =ᵐ[volume.restrict (Icc 0 T)]
        rawShiftedPositivePartEnergy hΩ M N u := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heAE
    have hi : ∀ᵐ r ∂volume.restrict (Icc 0 T), r ∈ Ioo 0 T := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hrep', he', hi] with r hU he hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
    change (if h : r ∈ Icc 0 T then
      ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N r) (Ubar ⟨r, h⟩)‖ ^ 2
      else 0) = e r
    rw [dif_pos hr', hU hr, ← valueCLM_h10ShiftedPositivePart]
    exact he.symm
  have hEqOn : EqOn E e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hAE hECont heCont
  calc
    _ = E t - E s := by
      change ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N t) (Ubar ⟨t, ht⟩)‖ ^ 2 -
        ‖shiftedPositivePartValue (reverseTimeAffineThreshold M N s) (Ubar ⟨s, hs⟩)‖ ^ 2 = _
      dsimp only [E]
      rw [dif_pos ht, dif_pos hs]
    _ = e t - e s := congrArg₂ (· - ·) (hEqOn ht) (hEqOn hs)
    _ = _ := by
      rw [heInc s t hs ht hst]
      simp only [rawShiftedPositivePartEnergyRate, shiftedPositivePartEnergyRate,
        integral_const_mul]

end HypoellipticAleksandrov.Parabolic.Dirichlet
