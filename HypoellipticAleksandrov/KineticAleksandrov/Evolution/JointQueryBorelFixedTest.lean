module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelProbe

/-! # Joint Borel evaluations of fixed admissible terminal probes

Upper countable-valued terminal times approximate every valid query, including the
endpoint. The proved terminal barrier and composition control the approximation.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology


/-- The integral of a fixed probe at admissible terminal times, and zero at the other times. -/
def validTerminalProbeIntegral (n : ℕ) (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (μ : EvolutionQuery Ω γ → Measure (EvolutionAmbientState n))
    (F : BoundedBorel (EvolutionAmbientState n)) (q : EvolutionQuery Ω γ) : ℝ := by
  classical
  exact if IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F then ∫ x, F x ∂(μ q) else 0

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "μT" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- At every query where a fixed smooth compact datum is admissible, its upper-time
measurable probe approximations converge to the terminal measure integral. -/
theorem tendsto_upper_terminal_probe
    (q : EvolutionQuery Ω γ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F) :
    Tendsto (fun j => extendedTerminalProbe n Ω γ B b hEx
      (terminalTimeMesh j q.1.2.1) F (evolutionQueryPoint q)) atTop
      (𝓝 (∫ x, F x ∂(μT q))) := by
  let τ := q.1.2.1
  let σ := q.1.1
  let p : EvolutionState Ω γ σ := ⟨q.1.2.2, q.2.2⟩
  obtain ⟨δ, hδ, hwindow⟩ := hF.exists_terminal_window
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1
  obtain ⟨M, hM0, herr⟩ := terminalOperators_terminal_time_error n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx τ F hF
  have hnear : ∀ᶠ j in atTop, dist (terminalTimeMesh j τ) τ < δ :=
    (tendsto_terminalTimeMesh τ).eventually (Metric.ball_mem_nhds τ hδ)
  have hevent : ∀ᶠ j in atTop,
      |extendedTerminalProbe n Ω γ B b hEx (terminalTimeMesh j τ) F (evolutionQueryPoint q) -
        P₀ σ τ q.2.1 (terminalStateDatum F) p| ≤ (terminalTimeMesh j τ - τ) * M := by
    filter_upwards [hnear] with j hj
    have hτj := le_terminalTimeMesh j τ
    have hFj := hwindow (terminalTimeMesh j τ) hj
    have hs : ∀ t ∈ Icc τ (terminalTimeMesh j τ),
        tsupport F ⊆ evolutionStateSet Ω γ t := by
      intro t ht
      have hd : dist t τ ≤ dist (terminalTimeMesh j τ) τ := by
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1),
          abs_of_nonneg (sub_nonneg.mpr hτj)]
        exact sub_le_sub_right ht.2 τ
      exact (hwindow t (hd.trans_lt hj)).2.2
    have hh := herr (terminalTimeMesh j τ) hτj hFj
      (terminalDatum_zero_lateral_of_support (isOpen_of_isAdmissibleEvolutionDomain hΩ) hs)
      σ q.2.1 p
    change |extendedTerminalProbe n Ω γ B b hEx (terminalTimeMesh j τ) F
      ⟨σ, p.1.1, p.1.2⟩ - P₀ σ τ q.2.1 (terminalStateDatum F) p| ≤ _
    rw [extendedTerminalProbe_eq_operator n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx σ (terminalTimeMesh j τ)
      (q.2.1.trans hτj) p F hFj]
    exact hh
  have hlim : Tendsto (fun j => extendedTerminalProbe n Ω γ B b hEx
      (terminalTimeMesh j τ) F (evolutionQueryPoint q)) atTop
      (𝓝 (P₀ σ τ q.2.1 (terminalStateDatum F) p)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall fun j => abs_nonneg _) hevent
    simpa only [sub_self, zero_mul] using ((tendsto_terminalTimeMesh τ).sub_const τ).mul_const M
  have heq : P₀ σ τ q.2.1 (terminalStateDatum F) p = ∫ x, F x ∂(μT q) := by
    rw [terminalOperators_apply_smooth]
    exact ((terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).2.2 F hF).symm
  rw [heq] at hlim
  exact hlim

/-- Fixed compact smooth test integrals are jointly measurable on the subtype of queries
where the test datum is supported in the terminal fiber. -/
theorem measurable_terminal_probe_on_admissible_queries
    (F : BoundedBorel (EvolutionAmbientState n)) :
    Measurable (fun q : {q : EvolutionQuery Ω γ //
      IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F} => ∫ x, F x ∂(μT q.1)) := by
  apply measurable_of_tendsto_metrizable
    (fun j => (measurable_upper_terminal_probe n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx j F).comp measurable_subtype_coe)
  apply tendsto_pi_nhds.mpr
  intro q
  exact tendsto_upper_terminal_probe n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q.1 F q.2

/-- A fixed smooth compact test integral, taken as zero when the test is not admissible,
is jointly measurable on the entire valid query space. -/
theorem measurable_valid_terminal_probe
    (F : BoundedBorel (EvolutionAmbientState n))
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    Measurable (validTerminalProbeIntegral n Ω γ μT F) := by
  classical
  unfold validTerminalProbeIntegral
  let D : Set (EvolutionQuery Ω γ) :=
    {q | IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F}
  have hs : MeasurableSet D := by
    have hopen := IsCompact.isOpen_terminal_support_times
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hFc
    have hm : Measurable (fun q : EvolutionQuery Ω γ => q.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
    simpa only [D, IsSmoothCompactTerminalDatum, hFs, hFc, true_and,
      Set.preimage, Set.mem_ofPred_eq] using
      hopen.measurableSet.preimage hm
  apply measurable_of_restrict_of_restrict_compl hs
  · convert measurable_terminal_probe_on_admissible_queries n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx F using 1
    funext q
    exact ite_eq_left q.2
  · have hf : Dᶜ.domRestrict (fun q : EvolutionQuery Ω γ =>
        if IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F then ∫ x, F x ∂(μT q) else 0) =
        (fun _ : ↥(Dᶜ) => (0 : ℝ)) := by
      funext q
      exact ite_eq_right q.2
    rw [hf]
    exact measurable_const

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov
