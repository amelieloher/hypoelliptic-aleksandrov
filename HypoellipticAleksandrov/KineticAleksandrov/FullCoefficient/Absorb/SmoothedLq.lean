module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.GreenLimitC
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.Assembly

/-!
# The smoothed `L^q` bound: limits `δ → 0`, `τ₁ ↓ 0`, `τ₂ ↑ T`

The result follows from Fatou's lemma in
`δ_n → 0` on the slabs `{τ ∈ (T/(k+3), T - T/(k+3))}` and monotone convergence in `k`, from the
absorption estimate for the mollified densities. The result is `SmoothedLqBound`, the
input of the density argument.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory Filter Topology
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam Lam T q : ℝ}

theorem absorbConst_nonneg {d : ℕ} {lam q : ℝ} (hl : 0 < lam)
    (hθ : 2 * (d : ℝ) * (q - 1) < 1) : 0 ≤ absorbConst d lam q := by
  unfold absorbConst
  have hc : 0 ≤ flowSupConstant d lam := supConst_nonneg (flowKernelFamily (d := d) hl)
    (h := 1) one_pos
  have h1 : 0 < 1 - 2 * (d : ℝ) * (q - 1) := by linarith
  have := Real.rpow_nonneg hc (q - 1)
  positivity

theorem green_lintegral_le (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    (hq : 1 < q) (hqΛ : q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x, ENNReal.ofReal
        (smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2 ^ q)
      ∂((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))) ≤
      ENNReal.ofReal (absorbConst d lam q * T ^ (1 - 2 * (d : ℝ) * (q - 1))) := by
  set P := (elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))
    with hP
  set ρ : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ := fun x =>
    smoothDensity (flowKernelFamily (d := d) hlam) ε (sliceMeasure K σ₀ p x.1) x.2 with hρ
  set Fn : ℕ → ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (greenDensity hlam (mollN n) ε Γ x.1.1 x.2 ^ q) with hFn
  have hfin : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  have hρm : Measurable ρ := by
    have h1 := measurable_ofReal_smoothDensity (Φ := flowKernelFamily (d := d) hlam) hε
      (sliceKernel K σ₀ p (ENNReal.ofReal T))
    have h3 := h1.ennreal_toReal
    have e : ρ = fun x => (ENNReal.ofReal (smoothDensity (flowKernelFamily (d := d) hlam) ε
          (sliceKernel K σ₀ p (ENNReal.ofReal T) x.1) x.2)).toReal :=
      funext fun x => (ENNReal.toReal_ofReal (smoothDensity_nonneg _ _ hε _)).symm
    rw [e]; exact h3
  have hFm : Measurable fun x => ENNReal.ofReal (ρ x ^ q) :=
    ENNReal.measurable_ofReal.comp (hρm.pow_const q)
  have hFnm : ∀ n, Measurable (Fn n) := fun n => by
    have hc : Continuous fun p : ℝ × EvolutionAmbientState d =>
        greenDensity hlam (mollN n) ε Γ p.1 p.2 :=
      (contDiff_greenDensity hlam Γ (isMollifier_mollN n) hε).continuous
    have hg := measurable_greenMap (S := ENNReal.ofReal T) (d := d)
    have := hc.measurable.comp hg
    exact ENNReal.measurable_ofReal.comp (this.pow_const q)
  have hq0 : 0 ≤ q := by linarith
  have hae := ae_tendsto_greenDensity hlam K σ₀ hT p Γ hΓ hε
  have hae' : ∀ᵐ x ∂P, Tendsto (fun n => Fn n x) atTop (𝓝 (ENNReal.ofReal (ρ x ^ q))) := by
    filter_upwards [hae] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hx.rpow_const (Or.inr hq0))
  -- slabs
  set a : ℕ → ℝ := fun k => T / ((k : ℝ) + 3) with ha
  set b : ℕ → ℝ := fun k => T - T / ((k : ℝ) + 3) with hb
  have ha0 : ∀ k, 0 < a k := fun k => by positivity
  have hab : ∀ k, a k < b k := fun k => by
    simp only [ha, hb]
    have hk : (3 : ℝ) ≤ (k : ℝ) + 3 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have : T / ((k : ℝ) + 3) ≤ T / 3 := div_le_div_of_nonneg_left hT.le (by norm_num) hk
    linarith
  set A : ℕ → Set (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d) := fun k =>
    (fun x => x.1.1) ⁻¹' Set.Ioo (a k) (b k) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (measurable_subtype_coe.comp measurable_fst) measurableSet_Ioo
  have hslab : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (ρ x ^ q) ∂P ≤
      ENNReal.ofReal (absorbConst d lam q * T ^ (1 - 2 * (d : ℝ) * (q - 1))) := by
    intro k
    have hev : ∀ᶠ n in atTop, mollRadius n < a k ∧ b k + mollRadius n < T := by
      have h1 : ∀ᶠ n in atTop, mollRadius n < a k :=
        tendsto_mollRadius.eventually (gt_mem_nhds (ha0 k))
      have h2 : ∀ᶠ n in atTop, mollRadius n < T - b k := by
        refine tendsto_mollRadius.eventually (gt_mem_nhds ?_)
        simp only [hb]; have : 0 < T / ((k : ℝ) + 3) := by positivity
        linarith
      filter_upwards [h1, h2] with n h1 h2
      exact ⟨h1, by linarith⟩
    have hle : ∀ᶠ n in atTop, ∫⁻ x in A k, Fn n x ∂P ≤
        ENNReal.ofReal (absorbConst d lam q * T ^ (1 - 2 * (d : ℝ) * (q - 1))) := by
      filter_upwards [hev] with n hn
      exact green_slab_lintegral_le hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ hq hqΛ hε
        (hab k) hn.1 hn.2
    have hae'' : ∀ᵐ x ∂(P.restrict (A k)), Tendsto (fun n => Fn n x) atTop
        (𝓝 (ENNReal.ofReal (ρ x ^ q))) := ae_restrict_of_ae hae'
    calc ∫⁻ x in A k, ENNReal.ofReal (ρ x ^ q) ∂P
        = ∫⁻ x in A k, liminf (fun n => Fn n x) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae''] with x hx
          exact hx.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x in A k, Fn n x ∂P) atTop :=
          lintegral_liminf_le (fun n => hFnm n)
      _ ≤ _ := liminf_le_of_frequently_le' hle.frequently
  -- monotone convergence
  have hmono : Monotone fun k => (A k).indicator fun x => ENNReal.ofReal (ρ x ^ q) := by
    intro k l hkl
    refine Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le)
    intro x hx
    have hkl' : (k : ℝ) + 3 ≤ l + 3 := by
      have := (Nat.cast_le (α := ℝ)).2 hkl; linarith
    have hdiv : T / ((l : ℝ) + 3) ≤ T / ((k : ℝ) + 3) :=
      div_le_div_of_nonneg_left hT.le (by positivity) hkl'
    have hka : a l ≤ a k := hdiv
    have hkb : b k ≤ b l := by simp only [hb]; linarith
    exact ⟨lt_of_le_of_lt hka hx.1, lt_of_lt_of_le hx.2 hkb⟩
  have hsup : ∀ x, ENNReal.ofReal (ρ x ^ q) =
      ⨆ k, (A k).indicator (fun x => ENNReal.ofReal (ρ x ^ q)) x := by
    intro x
    refine le_antisymm ?_ (iSup_le fun k => Set.indicator_le_self _ _ x)
    have hx0 : 0 < x.1.1 := x.1.2.1
    have hxT : x.1.1 < T := (ENNReal.ofReal_lt_ofReal_iff hT).1 x.1.2.2
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * T / min x.1.1 (T - x.1.1))
    have hm : 0 < min x.1.1 (T - x.1.1) := lt_min hx0 (by linarith)
    have hk' : T / ((k : ℝ) + 3) < min x.1.1 (T - x.1.1) := by
      rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hm).1 hk
      nlinarith
    have hxk : x ∈ A k := by
      refine ⟨?_, ?_⟩
      · exact lt_of_lt_of_le hk' (min_le_left _ _)
      · have := lt_of_lt_of_le hk' (min_le_right _ _)
        simp only [hb]; linarith
    refine le_iSup_of_le k ?_
    rw [Set.indicator_of_mem hxk]
  calc ∫⁻ x, ENNReal.ofReal (ρ x ^ q) ∂P
      = ∫⁻ x, ⨆ k, (A k).indicator (fun x => ENNReal.ofReal (ρ x ^ q)) x ∂P :=
        lintegral_congr hsup
    _ = ⨆ k, ∫⁻ x, (A k).indicator (fun x => ENNReal.ofReal (ρ x ^ q)) x ∂P :=
        lintegral_iSup (fun k => hFm.indicator (hAm k)) hmono
    _ ≤ _ := iSup_le fun k => by
        rw [lintegral_indicator (hAm k)]
        exact hslab k

/-- **The smoothed `L^q` bound**. -/
theorem smoothedLqBound_holds (hd : 1 ≤ d) (lam q : ℝ) (hlam : 0 < lam) (hq : 1 < q) :
    SmoothedLqBound d lam q hlam := by
  by_cases hθ : 2 * (d : ℝ) * (q - 1) < 1
  · refine ⟨absorbConst d lam q, absorbConst_nonneg hlam hθ, ?_⟩
    intro Lam hLam hqΛ B hB hBs hell S K hreal σ₀ p T hT ε hε
    obtain ⟨Γ, hΓ, -⟩ := existsUnique_greenMeasure K σ₀ (ENNReal.ofReal T)
      (ENNReal.ofReal_pos.2 hT) (Measure.dirac p)
    exact green_lintegral_le hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ hq hqΛ hε
  · refine ⟨0, le_refl _, ?_⟩
    intro Lam hLam hqΛ
    exact absurd (qstar_facts hd hlam hLam hq hqΛ).2.1 hθ

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
