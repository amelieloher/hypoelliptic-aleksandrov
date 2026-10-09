module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeScalarEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertSteklov
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Continuous Hilbert representatives in reverse time

This module constructs the closed-time spatial-`L²` representative supplied
by a reverse-time Gelfand weak derivative.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A continuous closed-time spatial-`L²` curve agrees almost everywhere with
the spatial value image of the reverse-time Bochner curve. -/
def ReverseTimeHilbertRepresentativeAgrees
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T)
    (Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞))) : Prop :=
  ∀ᵐ tau ∂reverseTimeVolume T,
    ∀ htau : tau ∈ Set.Ioo 0 T,
      Ubar ⟨tau, ⟨le_of_lt htau.1, le_of_lt htau.2⟩⟩ =
        valueCLM hΩ (u tau)

private theorem collar_bounds {T : ℝ} (hT : 0 < T) :
    0 < T / 3 ∧ T / 3 < 2 * T / 3 ∧ 2 * T / 3 < T := by
  constructor
  · positivity
  constructor <;> linarith

private theorem has_local_hilbert_limits
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    (∃ U : C(↥(Set.Icc 0 (2 * T / 3)), PDE.ScalarLp Ω (2 : ℝ≥0∞)),
      Tendsto (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u (2 * T / 3))
        atTop (𝓝 U)) ∧
    (∃ U : C(↥(Set.Icc (T / 3) T), PDE.ScalarLp Ω (2 : ℝ≥0∞)),
      Tendsto (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u (T / 3))
        atTop (𝓝 U)) := by
  obtain ⟨ha0, hab, hbT⟩ := collar_bounds hT
  constructor
  · exact cauchySeq_tendsto_of_complete
      (cauchySeq_reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u g hderiv
        (by linarith) hbT)
  · exact cauchySeq_tendsto_of_complete
      (cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u g hderiv
        ha0 (by linarith))

private theorem tendstoInMeasure_of_tendsto_sqNorm_integral
    {E : Type*} [NormedAddCommGroup E] {μ : Measure ℝ}
    {F : ℕ → ℝ → E} {f : ℝ → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : AEStronglyMeasurable f μ)
    (hMem : ∀ n, MemLp (F n - f) (2 : ℝ≥0∞) μ)
    (h2 : Tendsto (fun n => ∫ t, ‖F n t - f t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ F atTop f := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  have hroot : Tendsto (fun n => (∫ t, ‖F n t - f t‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹))
      atTop (𝓝 0) := by
    convert
      (Real.continuousAt_rpow_const 0 ((2 : ℝ)⁻¹) (Or.inr (by norm_num))).tendsto.comp h2
      using 1 <;>
      norm_num [Function.comp_def, Real.zero_rpow]
  have hELp : Tendsto
      (fun n => ENNReal.ofReal ((∫ t, ‖F n t - f t‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hroot
  apply hELp.congr'
  filter_upwards with n
  rw [(hMem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  norm_num

private theorem memLp_two_on_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f)
    (a b : ℝ) :
    MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem memLp_two_on_full_Icc
    {E : Type*} [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    MemLp (f : ℝ → E) (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)) := by
  simpa only [reverseTimeVolume, reverseTimeOpenInterval,
    restrict_Ioo_eq_restrict_Icc] using Lp.memLp f

private theorem tendsto_value_sqNorm_integral_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (T : ℝ) (_hT : 0 < T) (u : ReverseTimeL2V hΩ T)
    (F : ℕ → ℝ → H10HilbertGraph hΩ)
    (hF : ∀ n, Continuous (F n))
    (hfull : Tendsto (fun n => ∫ t in Icc 0 T, ‖F n t - u t‖ ^ 2)
      atTop (𝓝 0))
    {c e : ℝ} (hc : 0 ≤ c) (_hce : c ≤ e) (he : e ≤ T) :
    Tendsto (fun n => ∫ t in Icc c e,
      ‖valueCLM hΩ (F n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
  have hsub : Icc c e ⊆ Icc 0 T := by
    intro t ht
    exact ⟨hc.trans ht.1, ht.2.trans he⟩
  have hu := memLp_two_on_full_Icc T u
  apply squeeze_zero'
  · filter_upwards with n
    exact integral_nonneg fun _ => sq_nonneg _
  · filter_upwards with n
    let D : ℝ → H10HilbertGraph hΩ := fun t => F n t - u t
    have hFD : MemLp D (2 : ℝ≥0∞) (volume.restrict (Icc 0 T)) :=
      (memLp_two_on_Icc_of_continuous (F n) (hF n) 0 T).sub hu
    have hDint : IntegrableOn (fun t => ‖D t‖ ^ 2) (Icc 0 T) volume := by
      change Integrable (fun t => ‖D t‖ ^ 2) (volume.restrict (Icc 0 T))
      exact (memLp_two_iff_integrable_sq_norm hFD.aestronglyMeasurable).mp hFD
    have hVD : MemLp (fun t => valueCLM hΩ (D t)) (2 : ℝ≥0∞)
        (volume.restrict (Icc 0 T)) := by
      simpa only [Function.comp_def] using (valueCLM hΩ).comp_memLp' hFD
    have hVDint : IntegrableOn (fun t => ‖valueCLM hΩ (D t)‖ ^ 2) (Icc 0 T) volume := by
      change Integrable (fun t => ‖valueCLM hΩ (D t)‖ ^ 2)
        (volume.restrict (Icc 0 T))
      exact (memLp_two_iff_integrable_sq_norm hVD.aestronglyMeasurable).mp hVD
    have hRDint : IntegrableOn (fun t => ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2)
        (Icc 0 T) volume := hDint.const_mul _
    calc
      (∫ t in Icc c e, ‖valueCLM hΩ (F n t) - valueCLM hΩ (u t)‖ ^ 2) =
          ∫ t in Icc c e, ‖valueCLM hΩ (D t)‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with t
            dsimp only [D]
            rw [← (valueCLM hΩ).map_sub]
      _ ≤ ∫ t in Icc c e, ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2 := by
            apply setIntegral_mono_on (hVDint.mono_set hsub) (hRDint.mono_set hsub)
              measurableSet_Icc
            intro t _
            have hbound := (valueCLM hΩ).le_opNorm (D t)
            calc
              ‖valueCLM hΩ (D t)‖ ^ 2 ≤ (‖valueCLM hΩ‖ * ‖D t‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) hbound 2
              _ = ‖valueCLM hΩ‖ ^ 2 * ‖D t‖ ^ 2 := by rw [mul_pow]
      _ ≤ ‖valueCLM hΩ‖ ^ 2 * (∫ t in Icc 0 T, ‖D t‖ ^ 2) := by
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left
              (setIntegral_mono_set hDint (Eventually.of_forall fun _ => sq_nonneg _)
                (Eventually.of_forall hsub))
              (sq_nonneg _)
      _ = ‖valueCLM hΩ‖ ^ 2 * (∫ t in Icc 0 T, ‖F n t - u t‖ ^ 2) := rfl
  · simpa only [mul_zero] using tendsto_const_nhds.mul hfull

private theorem tendsto_continuousMap_apply
    {X E ι : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {l : Filter ι} (F : ι → C(X, E)) (U : C(X, E)) (x : X)
    (hF : Tendsto F l (𝓝 U)) :
    Tendsto (fun n => F n x) l (𝓝 (U x)) := by
  exact ((continuous_eval_const x).tendsto U).comp hF

private theorem exists_continuousMap_glue_of_local_ae
    {E : Type*} [NormedAddCommGroup E]
    {a b T : ℝ} (ha0 : 0 < a) (hab : a < b) (hbT : b < T)
    (f : ℝ → E)
    (UL : C(↥(Icc 0 b), E)) (UR : C(↥(Icc a T), E))
    (hLeftAE : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      ∀ ht : t ∈ Icc 0 b, UL ⟨t, ht⟩ = f t)
    (hRightAE : ∀ᵐ t ∂volume.restrict (Icc a T),
      ∀ ht : t ∈ Icc a T, UR ⟨t, ht⟩ = f t) :
    ∃ Ubar : C(↥(Icc 0 T), E),
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ∀ ht : t ∈ Icc 0 T, Ubar ⟨t, ht⟩ = f t := by
  have h0b : 0 ≤ b := ha0.le.trans hab.le
  have haT : a ≤ T := hab.le.trans hbT.le
  have hLsub : Icc 0 b ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hbT.le⟩
  have hRsub : Icc a T ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ha0.le.trans ht.1, ht.2⟩
  let leftExt : ℝ → E := fun t =>
    UL ⟨min b (max 0 t), ⟨le_min h0b (le_max_left _ _), min_le_left _ _⟩⟩
  let rightExt : ℝ → E := fun t =>
    UR ⟨max a (min T t), ⟨le_max_left _ _, max_le haT (min_le_left _ _)⟩⟩
  have hLeftExtCont : Continuous leftExt := by
    dsimp only [leftExt]
    exact UL.continuous.comp
      (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id))
        fun t => ⟨le_min h0b (le_max_left _ _), min_le_left _ _⟩)
  have hRightExtCont : Continuous rightExt := by
    dsimp only [rightExt]
    exact UR.continuous.comp
      (Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id))
        fun t => ⟨le_max_left _ _, max_le haT (min_le_left _ _)⟩)
  have hLeftExtAE : ∀ᵐ t ∂volume.restrict (Icc 0 b), leftExt t = f t := by
    filter_upwards [hLeftAE, ae_restrict_mem measurableSet_Icc] with t hUL ht
    simpa only [leftExt, max_eq_right ht.1, min_eq_right ht.2] using hUL ht
  have hRightExtAE : ∀ᵐ t ∂volume.restrict (Icc a T), rightExt t = f t := by
    filter_upwards [hRightAE, ae_restrict_mem measurableSet_Icc] with t hUR ht
    simpa only [rightExt, min_eq_right ht.2, max_eq_right ht.1] using hUR ht
  have hLeftOverlap := ae_restrict_of_ae_restrict_of_subset
    (show Icc a b ⊆ Icc 0 b by
      intro t ht
      exact ⟨ha0.le.trans ht.1, ht.2⟩) hLeftExtAE
  have hRightOverlap := ae_restrict_of_ae_restrict_of_subset
    (show Icc a b ⊆ Icc a T by
      intro t ht
      exact ⟨ht.1, ht.2.trans hbT.le⟩) hRightExtAE
  have hOverlapAE : leftExt =ᵐ[volume.restrict (Icc a b)] rightExt := by
    filter_upwards [hLeftOverlap, hRightOverlap] with t hL hR
    rw [hL, hR]
  have hOverlapEqOn : EqOn leftExt rightExt (Icc a b) :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne hOverlapAE
      hLeftExtCont.continuousOn hRightExtCont.continuousOn
  let glue : ↥(Icc 0 T) → E := fun t =>
    if htb : (t : ℝ) ≤ b then
      UL ⟨t, ⟨t.2.1, htb⟩⟩
    else
      UR ⟨t, ⟨le_of_lt (hab.trans (lt_of_not_ge htb)), t.2.2⟩⟩
  let S : Set (↥(Icc 0 T)) := {t | (t : ℝ) ≤ b}
  let R : Set (↥(Icc 0 T)) := {t | a ≤ (t : ℝ)}
  have hSclosed : IsClosed S := by
    dsimp only [S]
    exact isClosed_le continuous_subtype_val continuous_const
  have hRclosed : IsClosed R := by
    dsimp only [R]
    exact isClosed_le continuous_const continuous_subtype_val
  have hSR : S ∪ R = univ := by
    ext t
    simp only [mem_union, mem_univ, iff_true]
    by_cases htb : (t : ℝ) ≤ b
    · exact Or.inl htb
    · exact Or.inr (le_of_lt (hab.trans (lt_of_not_ge htb)))
  have hGlueEqLeft : EqOn glue (fun t : ↥(Icc 0 T) => leftExt t) S := by
    intro t ht
    change (if htb : (t : ℝ) ≤ b then UL ⟨t, ⟨t.2.1, htb⟩⟩ else
      UR ⟨t, ⟨le_of_lt (hab.trans (lt_of_not_ge htb)), t.2.2⟩⟩) = leftExt t
    change (t : ℝ) ≤ b at ht
    rw [dif_pos ht]
    change UL ⟨t, ⟨t.2.1, ht⟩⟩ = UL ⟨min b (max 0 t), _⟩
    apply congrArg UL
    apply Subtype.ext
    dsimp
    rw [max_eq_right t.2.1, min_eq_right ht]
  have hGlueEqRight : EqOn glue (fun t : ↥(Icc 0 T) => rightExt t) R := by
    intro t ht
    change a ≤ (t : ℝ) at ht
    change (if h : (t : ℝ) ≤ b then UL ⟨t, ⟨t.2.1, h⟩⟩ else
      UR ⟨t, ⟨le_of_lt (hab.trans (lt_of_not_ge h)), t.2.2⟩⟩) = rightExt t
    by_cases htb : (t : ℝ) ≤ b
    · have habmem : (t : ℝ) ∈ Icc a b := ⟨ht, htb⟩
      have heq := hOverlapEqOn habmem
      change leftExt t = rightExt t at heq
      rw [dif_pos htb]
      change UL ⟨t, ⟨t.2.1, htb⟩⟩ = UR ⟨max a (min T t), _⟩
      change UL ⟨min b (max 0 t), _⟩ = UR ⟨max a (min T t), _⟩ at heq
      simpa only [max_eq_right t.2.1, min_eq_right htb, Subsingleton.elim] using heq
    ·
      rw [dif_neg htb]
      change UR ⟨t, ⟨ht, t.2.2⟩⟩ = UR ⟨max a (min T t), _⟩
      apply congrArg UR
      apply Subtype.ext
      dsimp
      rw [min_eq_right t.2.2, max_eq_right ht]
  have hGlueS : ContinuousOn glue S :=
    ContinuousOn.congr (f := fun t : ↥(Icc 0 T) => leftExt t) (g := glue)
      (hLeftExtCont.comp continuous_subtype_val).continuousOn hGlueEqLeft
  have hGlueR : ContinuousOn glue R :=
    ContinuousOn.congr (f := fun t : ↥(Icc 0 T) => rightExt t) (g := glue)
      (hRightExtCont.comp continuous_subtype_val).continuousOn hGlueEqRight
  have hGlueOn : ContinuousOn glue (S ∪ R) :=
    ContinuousOn.union_of_isClosed hGlueS hGlueR hSclosed hRclosed
  have hGlue : Continuous glue := by
    rw [hSR] at hGlueOn
    simpa only [continuousOn_univ] using hGlueOn
  let Ubar : C(↥(Icc 0 T), E) := ⟨glue, hGlue⟩
  have hGlueLeftAE : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      ∀ ht : t ∈ Icc 0 b, Ubar ⟨t, hLsub ht⟩ = f t := by
    filter_upwards [hLeftExtAE, ae_restrict_mem measurableSet_Icc] with t hLeft ht
    intro ht'
    change glue ⟨t, hLsub ht'⟩ = _
    simpa only [glue, dif_pos ht'.2, leftExt,
      max_eq_right ht'.1, min_eq_right ht'.2, Subsingleton.elim] using hLeft
  have hGlueRightAE : ∀ᵐ t ∂volume.restrict (Icc a T),
      ∀ ht : t ∈ Icc a T, Ubar ⟨t, hRsub ht⟩ = f t := by
    filter_upwards [hRightExtAE, ae_restrict_mem measurableSet_Icc] with t hRight ht
    intro ht'
    let x : ↥(Icc 0 T) := ⟨t, hRsub ht'⟩
    have hxR : x ∈ R := by
      change a ≤ t
      exact ht'.1
    have hEq := hGlueEqRight hxR
    change Ubar x = _
    calc
      Ubar x = rightExt t := by
        change glue x = rightExt t
        change glue x = rightExt (x : ℝ) at hEq
        exact hEq
      _ = f t := hRight
  have hcover : Icc 0 b ∪ Icc a T = Icc 0 T := by
    apply Set.Subset.antisymm
    · intro t ht
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans hbT.le⟩
      · exact ⟨ha0.le.trans ht.1, ht.2⟩
    · intro t ht
      by_cases htb : t ≤ b
      · exact Or.inl ⟨ht.1, htb⟩
      · exact Or.inr ⟨le_of_lt (hab.trans (lt_of_not_ge htb)), ht.2⟩
  have hUnionAE : ∀ᵐ t ∂volume.restrict (Icc 0 b ∪ Icc a T),
      ∀ ht : t ∈ Icc 0 T, Ubar ⟨t, ht⟩ = f t :=
    (ae_restrict_union_iff (μ := volume) (Icc 0 b) (Icc a T)
    fun t => ∀ ht : t ∈ Icc 0 T, Ubar ⟨t, ht⟩ = f t).mpr
    ⟨by
      filter_upwards [hGlueLeftAE, ae_restrict_mem measurableSet_Icc] with t h htb
      intro ht
      simpa only [Subsingleton.elim] using h htb,
    by
      filter_upwards [hGlueRightAE, ae_restrict_mem measurableSet_Icc] with t h hta
      intro ht
      simpa only [Subsingleton.elim] using h hta⟩
  refine ⟨Ubar, ?_⟩
  simpa only [hcover] using hUnionAE

private theorem exists_reverseTimeHilbertRepresentative_agrees
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃ Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)),
      ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar := by
  let a : ℝ := T / 3
  let b : ℝ := 2 * T / 3
  obtain ⟨ha0, hab, hbT⟩ := collar_bounds hT
  have h0b : 0 ≤ b := by
    dsimp only [b]
    positivity
  have haT : a ≤ T := by
    dsimp only [a]
    linarith
  obtain ⟨UL, hUL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u g hderiv
      (by simpa only [b] using (show 0 < 2 * T / 3 by linarith))
      (by simpa only [b] using hbT))
  obtain ⟨UR, hUR⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u g hderiv
      (by simpa only [a] using ha0)
      (by simpa only [a] using (show T / 3 < T by linarith)))
  have hUL' : Tendsto (reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b)
      atTop (𝓝 UL) := by
    simpa only [b] using hUL
  have hUR' : Tendsto (reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a)
      atTop (𝓝 UR) := by
    simpa only [a] using hUR
  let SL : ℕ → C(↥(Icc 0 b), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
    reverseTimeForwardSteklovHilbertOnIcc hΩ T hT u b
  let SR : ℕ → C(↥(Icc a T), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
    reverseTimeBackwardSteklovHilbertOnIcc hΩ T hT u a
  have hSL : Tendsto SL atTop (𝓝 UL) := hUL'
  have hSR : Tendsto SR atTop (𝓝 UR) := hUR'
  let FL : ℕ → ℝ → H10HilbertGraph hΩ := fun n t =>
    reverseTimeForwardSteklov T (reverseTimeSteklovStep T n) u t
  let FR : ℕ → ℝ → H10HilbertGraph hΩ := fun n t =>
    reverseTimeBackwardSteklov T (reverseTimeSteklovStep T n) u t
  have hFLcont : ∀ n, Continuous (FL n) := by
    intro n
    simpa only [FL] using continuous_reverseTimeForwardSteklov T
      (reverseTimeSteklovStep T n) (by
        unfold reverseTimeSteklovStep
        positivity) u
  have hFRcont : ∀ n, Continuous (FR n) := by
    intro n
    simpa only [FR] using continuous_reverseTimeBackwardSteklov T
      (reverseTimeSteklovStep T n) (by
        unfold reverseTimeSteklovStep
        positivity) u
  have hFLraw : Tendsto (fun n => ∫ t in Icc 0 T, ‖FL n t - u t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [FL, Function.comp_def] using
      (tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
        (tendsto_reverseTimeSteklovStep T hT)
  have hFRraw : Tendsto (fun n => ∫ t in Icc 0 T, ‖FR n t - u t‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [FR, Function.comp_def] using
      (tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T T hT u).comp
        (tendsto_reverseTimeSteklovStep T hT)
  have hVL : Tendsto (fun n => ∫ t in Icc 0 b,
      ‖valueCLM hΩ (FL n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
    exact tendsto_value_sqNorm_integral_on_Icc hΩ T hT u FL hFLcont hFLraw
      le_rfl h0b hbT.le
  have hVR : Tendsto (fun n => ∫ t in Icc a T,
      ‖valueCLM hΩ (FR n t) - valueCLM hΩ (u t)‖ ^ 2) atTop (𝓝 0) := by
    exact tendsto_value_sqNorm_integral_on_Icc hΩ T hT u FR hFRcont hFRraw
      ha0.le haT le_rfl
  have huFull := memLp_two_on_full_Icc T u
  have hLsub : Icc 0 b ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hbT.le⟩
  have hRsub : Icc a T ⊆ Icc 0 T := by
    intro t ht
    exact ⟨ha0.le.trans ht.1, ht.2⟩
  have huL : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞)
      (volume.restrict (Icc 0 b)) := by
    simpa only [Measure.restrict_restrict_of_subset hLsub] using
      huFull.restrict (Icc 0 b)
  have huR : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞)
      (volume.restrict (Icc a T)) := by
    simpa only [Measure.restrict_restrict_of_subset hRsub] using
      huFull.restrict (Icc a T)
  have hVDL : ∀ n, MemLp
      ((fun t => valueCLM hΩ (FL n t)) - fun t => valueCLM hΩ (u t))
      (2 : ℝ≥0∞) (volume.restrict (Icc 0 b)) := by
    intro n
    have hdiff := (memLp_two_on_Icc_of_continuous (FL n) (hFLcont n) 0 b).sub huL
    simpa only [Pi.sub_def, ContinuousLinearMap.map_sub] using
      hdiff.continuousLinearMap_comp (valueCLM hΩ)
  have hVDR : ∀ n, MemLp
      ((fun t => valueCLM hΩ (FR n t)) - fun t => valueCLM hΩ (u t))
      (2 : ℝ≥0∞) (volume.restrict (Icc a T)) := by
    intro n
    have hdiff := (memLp_two_on_Icc_of_continuous (FR n) (hFRcont n) a T).sub huR
    simpa only [Pi.sub_def, ContinuousLinearMap.map_sub] using
      hdiff.continuousLinearMap_comp (valueCLM hΩ)
  have hIML : TendstoInMeasure (volume.restrict (Icc 0 b))
      (fun n t => valueCLM hΩ (FL n t)) atTop (fun t => valueCLM hΩ (u t)) := by
    apply tendstoInMeasure_of_tendsto_sqNorm_integral
      (fun n => ((valueCLM hΩ).continuous.comp (hFLcont n)).aestronglyMeasurable)
      (huL.continuousLinearMap_comp (valueCLM hΩ)).aestronglyMeasurable hVDL
    exact hVL
  have hIMR : TendstoInMeasure (volume.restrict (Icc a T))
      (fun n t => valueCLM hΩ (FR n t)) atTop (fun t => valueCLM hΩ (u t)) := by
    apply tendstoInMeasure_of_tendsto_sqNorm_integral
      (fun n => ((valueCLM hΩ).continuous.comp (hFRcont n)).aestronglyMeasurable)
      (huR.continuousLinearMap_comp (valueCLM hΩ)).aestronglyMeasurable hVDR
    exact hVR
  obtain ⟨nsL, hnsL, hsubL⟩ := hIML.exists_seq_tendsto_ae
  obtain ⟨nsR, hnsR, hsubR⟩ := hIMR.exists_seq_tendsto_ae
  have hULAE : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      ∀ ht : t ∈ Icc 0 b, UL ⟨t, ht⟩ = valueCLM hΩ (u t) := by
    filter_upwards [hsubL, ae_restrict_mem measurableSet_Icc] with t ht htb
    intro htb'
    have hPoint : Tendsto (fun n =>
        SL (nsL n) ⟨t, htb'⟩) atTop (𝓝 (UL ⟨t, htb'⟩)) := by
      exact (tendsto_continuousMap_apply SL UL ⟨t, htb'⟩ hSL).comp hnsL.tendsto_atTop
    apply tendsto_nhds_unique
      (by
        convert hPoint using 1
        funext n
        rfl)
      ht
  have hURAE : ∀ᵐ t ∂volume.restrict (Icc a T),
      ∀ ht : t ∈ Icc a T, UR ⟨t, ht⟩ = valueCLM hΩ (u t) := by
    filter_upwards [hsubR, ae_restrict_mem measurableSet_Icc] with t ht hta
    intro hta'
    have hPoint : Tendsto (fun n =>
        SR (nsR n) ⟨t, hta'⟩) atTop (𝓝 (UR ⟨t, hta'⟩)) := by
      exact (tendsto_continuousMap_apply SR UR ⟨t, hta'⟩ hSR).comp hnsR.tendsto_atTop
    apply tendsto_nhds_unique
      (by
        convert hPoint using 1
        funext n
        rfl)
      ht
  obtain ⟨Ubar, hClosedAE⟩ := exists_continuousMap_glue_of_local_ae ha0 hab hbT
    (fun t => valueCLM hΩ (u t)) UL UR hULAE hURAE
  refine ⟨Ubar, ?_⟩
  change ∀ᵐ tau ∂volume.restrict (Ioo 0 T),
    ∀ htau : tau ∈ Ioo 0 T,
      Ubar ⟨tau, ⟨le_of_lt htau.1, le_of_lt htau.2⟩⟩ = valueCLM hΩ (u tau)
  rw [restrict_Ioo_eq_restrict_Icc]
  filter_upwards [hClosedAE] with tau hTau
  intro htau
  simpa only [Subsingleton.elim] using
    hTau ⟨le_of_lt htau.1, le_of_lt htau.2⟩

private theorem reverseTimeHilbertRepresentative_energy_increment
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar) :
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
      s ≤ t →
        ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨e, heCont, _heNonneg, heAE, heInc⟩ :=
    exists_continuous_reverseTimeScalarEnergyRepresentative hΩ T hT u g hderiv
  let Uext : ℝ → PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun t =>
    if ht : t ∈ Icc 0 T then Ubar ⟨t, ht⟩ else 0
  have hUextCont : ContinuousOn Uext (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict Uext = Ubar := by
      funext t
      simp only [Set.domRestrict_apply, Uext, dif_pos t.2]
    rw [hEq]
    exact Ubar.continuous
  have hIoo : ∀ᵐ t ∂volume.restrict (Icc 0 T), t ∈ Ioo 0 T := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hUbarIcc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Ubar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) := by
    simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
      reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hUbar
  have heAEIcc : e =ᵐ[volume.restrict (Icc 0 T)]
      fun t => ‖valueCLM hΩ (u t)‖ ^ 2 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc] using heAE
  have hNormSqAE : (fun t => ‖Uext t‖ ^ 2) =ᵐ[volume.restrict (Icc 0 T)] e := by
    filter_upwards [hIoo, hUbarIcc, heAEIcc] with t ht hUbar he
    have htIcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    calc
      ‖Uext t‖ ^ 2 = ‖Ubar ⟨t, htIcc⟩‖ ^ 2 := by
        simp only [Uext, dif_pos htIcc]
      _ = ‖valueCLM hΩ (u t)‖ ^ 2 := by rw [hUbar ht]
      _ = e t := he.symm
  have hNormSqCont : ContinuousOn (fun t => ‖Uext t‖ ^ 2) (Icc 0 T) :=
    (hUextCont.norm.pow 2)
  have hNormSqEqOn : EqOn (fun t => ‖Uext t‖ ^ 2) e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hNormSqAE hNormSqCont heCont
  intro s t hs ht hst
  calc
    ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
        ‖Uext t‖ ^ 2 - ‖Uext s‖ ^ 2 := by
          simp only [Uext, dif_pos hs, dif_pos ht]
    _ = e t - e s := congrArg₂ (fun x y : ℝ => x - y)
      (hNormSqEqOn ht) (hNormSqEqOn hs)
    _ = 2 * (∫ r in Ioc s t, (g r) (u r) ∂reverseTimeVolume T) :=
      heInc s t hs ht hst

private theorem reverseTimeHilbertRepresentative_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T)
    (Ubar Vbar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar)
    (hVbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Vbar) :
    Ubar = Vbar := by
  let Uext : ℝ → PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun t =>
    if ht : t ∈ Icc 0 T then Ubar ⟨t, ht⟩ else 0
  let Vext : ℝ → PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun t =>
    if ht : t ∈ Icc 0 T then Vbar ⟨t, ht⟩ else 0
  have hUextCont : ContinuousOn Uext (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict Uext = Ubar := by
      funext t
      simp only [Set.domRestrict_apply, Uext, dif_pos t.2]
    rw [hEq]
    exact Ubar.continuous
  have hVextCont : ContinuousOn Vext (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict Vext = Vbar := by
      funext t
      simp only [Set.domRestrict_apply, Vext, dif_pos t.2]
    rw [hEq]
    exact Vbar.continuous
  have hIoo : ∀ᵐ t ∂volume.restrict (Icc 0 T), t ∈ Ioo 0 T := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hUbarIcc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Ubar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) := by
    simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
      reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hUbar
  have hVbarIcc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Vbar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) := by
    simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
      reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hVbar
  have hUVAE : Uext =ᵐ[volume.restrict (Icc 0 T)] Vext := by
    filter_upwards [hIoo, hUbarIcc, hVbarIcc] with t ht hUbar hVbar
    have htIcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    calc
      Uext t = Ubar ⟨t, htIcc⟩ := by simp only [Uext, dif_pos htIcc]
      _ = valueCLM hΩ (u t) := hUbar ht
      _ = Vbar ⟨t, htIcc⟩ := (hVbar ht).symm
      _ = Vext t := by simp only [Vext, dif_pos htIcc]
  have hEqOn : EqOn Uext Vext (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hUVAE hUextCont hVextCont
  apply ContinuousMap.ext
  intro t
  simpa only [Uext, Vext, dif_pos t.2] using hEqOn t.2

/-- The continuous spatial-`L²` representative of a reverse-time Gelfand
weak derivative, with its one-curve energy increment. -/
theorem existsUnique_reverseTimeHilbertRepresentative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ∃! Ubar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)),
      ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar ∧
      ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
        s ≤ t →
          ‖Ubar ⟨t, ht⟩‖ ^ 2 - ‖Ubar ⟨s, hs⟩‖ ^ 2 =
            2 * (∫ r in Set.Ioc s t,
              (g r) (u r) ∂reverseTimeVolume T) := by
  obtain ⟨Ubar, hUbar⟩ :=
    exists_reverseTimeHilbertRepresentative_agrees hΩ T hT u g hderiv
  refine ⟨Ubar, ⟨hUbar, ?_⟩, ?_⟩
  · exact reverseTimeHilbertRepresentative_energy_increment hΩ T hT u g hderiv Ubar hUbar
  · intro Vbar hVbar
    exact reverseTimeHilbertRepresentative_eq hΩ T hT u Vbar Ubar hVbar.1 hUbar

end HypoellipticAleksandrov.Parabolic.Dirichlet
