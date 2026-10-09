module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-!
# Transported cutoffs and the growth tail comparison (outside context)

Companion paper, Proposition 2.1 (marginal smoothness).  For a smooth compactly
supported scalar datum `F` the cutoff data `F_N(y, z) = F(y) χ(z / (N + 1))` are smooth compactly
supported kinetic data supported in the open terminal fiber, and the data difference
`F_M - F_N` (`M ≥ N`) is bounded by `‖F‖ (1 + |y|² + |z|²) / (N + 1)²`.  The growth comparison
(Proposition 2.1) turns an inequality of terminal data of this form into
`u₁ - u₂ ≤ c Φ_τ` on the whole past closed cylinder.

* `zCutoff`, `zCutoffN`: the transported-coordinate cutoffs.
* `cutoffDatum`, `lowerDatum`: `F(y) χ_N(z)` and `F(y)` as bounded Borel kinetic data.
* `cutoffDatum_isSmoothCompact`: the cutoff data are admissible smooth compact terminal data.
* `abs_cutoffDatum_sub_le`: the quadratic tail bound for the data difference.
* `classical_sub_le_growthBarrier`: the growth tail comparison for classical solutions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory
open scoped Topology MatrixOrder

section Cutoff

variable {n : ℕ}

/-- A smooth bump in the transported coordinate: equal to one on the unit ball, supported in the
ball of radius two, with values in `[0, 1]`. -/
theorem exists_zCutoff (n : ℕ) :
    ∃ χ : PDE.Vec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ ∀ z, ‖z‖ ≤ 1 → χ z = 1 := by
  obtain ⟨f, hs, hc, -, h01, h1⟩ := exists_smooth_bump_of_isCompact_subset_isOpen
    (K := Metric.closedBall (0 : PDE.Vec n) 1) (V := Metric.ball (0 : PDE.Vec n) 2)
    (isCompact_closedBall 0 1) Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by norm_num))
  exact ⟨f, hs, hc, h01, fun z hz => h1 z (by simpa using hz)⟩

/-- The chosen bump. -/
def zCutoff (n : ℕ) : PDE.Vec n → ℝ := (exists_zCutoff n).choose

theorem contDiff_zCutoff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (zCutoff n) :=
  (exists_zCutoff n).choose_spec.1

theorem hasCompactSupport_zCutoff (n : ℕ) : HasCompactSupport (zCutoff n) :=
  (exists_zCutoff n).choose_spec.2.1

theorem zCutoff_mem_Icc (n : ℕ) (z : PDE.Vec n) : 0 ≤ zCutoff n z ∧ zCutoff n z ≤ 1 :=
  (exists_zCutoff n).choose_spec.2.2.1 z

theorem zCutoff_eq_one (n : ℕ) {z : PDE.Vec n} (hz : ‖z‖ ≤ 1) : zCutoff n z = 1 :=
  (exists_zCutoff n).choose_spec.2.2.2 z hz

/-- The cutoff at scale `N + 1`. -/
def zCutoffN (n N : ℕ) (z : PDE.Vec n) : ℝ := zCutoff n (((N : ℝ) + 1)⁻¹ • z)

theorem contDiff_zCutoffN (n N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (zCutoffN n N) :=
  (contDiff_zCutoff n).comp (contDiff_const_smul _)

theorem hasCompactSupport_zCutoffN (n N : ℕ) : HasCompactSupport (zCutoffN n N) := by
  have hne : ((N : ℝ) + 1)⁻¹ ≠ 0 := by positivity
  exact (hasCompactSupport_zCutoff n).comp_homeomorph (Homeomorph.smulOfNeZero _ hne)

theorem zCutoffN_mem_Icc (n N : ℕ) (z : PDE.Vec n) : 0 ≤ zCutoffN n N z ∧ zCutoffN n N z ≤ 1 :=
  zCutoff_mem_Icc n _

theorem zCutoffN_eq_one {n N : ℕ} {z : PDE.Vec n} (hz : ‖z‖ ≤ (N : ℝ) + 1) :
    zCutoffN n N z = 1 := by
  apply zCutoff_eq_one
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

/-- The cutoff datum `F(y) χ_N(z)` as a bounded Borel kinetic datum. -/
def cutoffDatum (F : BoundedBorel (PDE.Vec n)) (N : ℕ) : BoundedBorel (EvolutionAmbientState n) :=
  ⟨fun x => F x.1 * zCutoffN n N x.2,
    ⟨(F.measurable.comp measurable_fst).mul
      ((contDiff_zCutoffN n N).continuous.measurable.comp measurable_snd),
    by
      obtain ⟨C, hC0, hC⟩ := F.exists_bound
      refine ⟨C, hC0, fun x => ?_⟩
      rw [abs_mul]
      calc |F x.1| * |zCutoffN n N x.2| ≤ C * 1 := by
            refine mul_le_mul (hC x.1) ?_ (abs_nonneg _) hC0
            rw [abs_of_nonneg (zCutoffN_mem_Icc n N x.2).1]
            exact (zCutoffN_mem_Icc n N x.2).2
        _ = C := mul_one C⟩⟩

/-- The `z`-independent datum `F(y)` as a bounded Borel kinetic datum. -/
def lowerDatum (F : BoundedBorel (PDE.Vec n)) : BoundedBorel (EvolutionAmbientState n) :=
  F.pullback Prod.fst measurable_fst

@[simp] theorem cutoffDatum_apply (F : BoundedBorel (PDE.Vec n)) (N : ℕ)
    (x : EvolutionAmbientState n) : cutoffDatum F N x = F x.1 * zCutoffN n N x.2 := rfl

@[simp] theorem lowerDatum_apply (F : BoundedBorel (PDE.Vec n)) (x : EvolutionAmbientState n) :
    lowerDatum F x = F x.1 := rfl

/-- The cutoff data are smooth compactly supported terminal data in the open fiber. -/
theorem cutoffDatum_isSmoothCompact {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {τ : ℝ}
    {F : BoundedBorel (PDE.Vec n)}
    (hF : ParabolicProbe.IsSmoothCompactScalarTerminalDatum Ω γ τ F) (N : ℕ) :
    IsSmoothCompactTerminalDatum Ω γ τ (cutoffDatum F N) := by
  have hsub : tsupport (cutoffDatum F N : EvolutionAmbientState n → ℝ) ⊆
      tsupport (F : PDE.Vec n → ℝ) ×ˢ tsupport (zCutoffN n N) := by
    have h : Function.support (cutoffDatum F N : EvolutionAmbientState n → ℝ) ⊆
        Function.support (F : PDE.Vec n → ℝ) ×ˢ Function.support (zCutoffN n N) := by
      intro x hx
      refine ⟨?_, ?_⟩
      · intro h0
        exact hx (by simp [h0])
      · intro h0
        exact hx (by simp [h0])
    refine (closure_mono h).trans ?_
    rw [closure_prod_eq]
    exact Subset.rfl
  refine ⟨?_, ?_, ?_⟩
  · exact (hF.1.comp contDiff_fst).mul ((contDiff_zCutoffN n N).comp contDiff_snd)
  · exact ((hF.2.1.prod (hasCompactSupport_zCutoffN n N))).of_isClosed_subset
      (isClosed_tsupport _) hsub
  · intro x hx
    exact ⟨hF.2.2 (hsub hx).1, mem_univ _⟩

/-- A cutoff datum is bounded by the bound of `F`. -/
theorem abs_cutoffDatum_le {F : BoundedBorel (PDE.Vec n)} {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    (hC0 : 0 ≤ C) (N : ℕ) (x : EvolutionAmbientState n) : |cutoffDatum F N x| ≤ C := by
  rw [cutoffDatum_apply, abs_mul]
  calc |F x.1| * |zCutoffN n N x.2| ≤ C * 1 := by
        refine mul_le_mul (hC x.1) ?_ (abs_nonneg _) hC0
        rw [abs_of_nonneg (zCutoffN_mem_Icc n N x.2).1]
        exact (zCutoffN_mem_Icc n N x.2).2
    _ = C := mul_one C

/-- A large transported coordinate has large Euclidean norm square. -/
theorem sq_lt_vecNormSq_of_lt_norm {z : PDE.Vec n} {r : ℝ} (hr : 0 ≤ r) (hz : r < ‖z‖) :
    r ^ 2 < PDE.vecNormSq z := by
  by_contra hcon
  push Not at hcon
  have : ‖z‖ ≤ r := by
    rw [pi_norm_le_iff_of_nonneg hr]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq (by linarith [PDE.sq_apply_le_vecNormSq z i]) hr
  linarith

/-- The quadratic tail bound for the difference of two cutoff data. -/
theorem abs_cutoffDatum_sub_le {F : BoundedBorel (PDE.Vec n)} {C : ℝ} (hC : ∀ x, |F x| ≤ C)
    (hC0 : 0 ≤ C) {N M : ℕ} (hNM : N ≤ M) (x : EvolutionAmbientState n) :
    |cutoffDatum F M x - cutoffDatum F N x| ≤
      C / ((N : ℝ) + 1) ^ 2 * (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hRHS : 0 ≤ C / ((N : ℝ) + 1) ^ 2 * (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
    have := PDE.vecNormSq_nonneg x.1
    have := PDE.vecNormSq_nonneg x.2
    positivity
  have hdiff : cutoffDatum F M x - cutoffDatum F N x =
      F x.1 * (zCutoffN n M x.2 - zCutoffN n N x.2) := by
    simp only [cutoffDatum_apply]
    ring
  rw [hdiff, abs_mul]
  by_cases hz : ‖x.2‖ ≤ (N : ℝ) + 1
  · have hz' : ‖x.2‖ ≤ (M : ℝ) + 1 := hz.trans (by
      have : (N : ℝ) ≤ M := by exact_mod_cast hNM
      linarith)
    rw [zCutoffN_eq_one hz, zCutoffN_eq_one hz']
    simpa using hRHS
  · push Not at hz
    have hsq := sq_lt_vecNormSq_of_lt_norm hN.le hz
    have h1 : |zCutoffN n M x.2 - zCutoffN n N x.2| ≤ 1 := by
      have := zCutoffN_mem_Icc n M x.2
      have := zCutoffN_mem_Icc n N x.2
      rw [abs_le]
      constructor <;> linarith
    have h2 : 1 ≤ PDE.vecNormSq x.2 / ((N : ℝ) + 1) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h3 : PDE.vecNormSq x.2 / ((N : ℝ) + 1) ^ 2 ≤
        (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) / ((N : ℝ) + 1) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := PDE.vecNormSq_nonneg x.1
      linarith
    calc |F x.1| * |zCutoffN n M x.2 - zCutoffN n N x.2| ≤ C * 1 :=
          mul_le_mul (hC x.1) h1 (abs_nonneg _) hC0
      _ ≤ C * ((1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) / ((N : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) hC0
      _ = _ := by ring

end Cutoff

section Comparison

variable {n : ℕ}

/-- **Growth tail comparison** (Proposition 2.1, `ε = 0`).  There is a constant `C`
depending only on `Λ`, `b 0` and `L_b` such that, for classical terminal solutions `u₁, u₂` whose
terminal data satisfy `F₁ - F₂ ≤ c (1 + |y|² + |z|²)` over the closed fiber, one has
`u₁ - u₂ ≤ c Φ_τ` on the whole past closed cylinder, `Φ_τ = e^{C(τ-σ)}(1 + |y|² + |z|²)`. -/
theorem classical_sub_le_growthBarrier {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (F₁ F₂ : BoundedBorel (EvolutionAmbientState n))
      (u₁ u₂ : KineticPoint n → ℝ) (c : ℝ), 0 ≤ c →
      IsClassicalTerminalSolution Ω γ B b τ F₁ u₁ →
      IsClassicalTerminalSolution Ω γ B b τ F₂ u₂ →
      (∀ x : EvolutionAmbientState n, x.1 ∈ closure (movingDomain Ω γ τ) →
        F₁ x - F₂ x ≤ c * (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2)) →
      ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, u₁ p - u₂ p ≤ c * growthBarrier C τ p := by
  obtain ⟨C, hC0, hCΦ⟩ := exists_growthConstant (fun σ y z => (hB σ y z).2) hb
  refine ⟨C, hC0, fun τ F₁ F₂ u₁ u₂ c hc h₁ h₂ hF p₀ hp₀ => ?_⟩
  have h₁' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F₁ u₁).2 h₁
  have h₂' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F₂ u₂).2 h₂
  have hslab : ∀ a, movingClosedSlab Ω γ a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω γ a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  obtain ⟨C₁, -, hC₁⟩ := h₁'.1
  obtain ⟨C₂, -, hC₂⟩ := h₂'.1
  have hp₀slab : p₀ ∈ movingClosedSlab Ω γ p₀.time τ := ⟨le_rfl, hp₀.1, hp₀.2⟩
  have hres := growth_comparison (a := p₀.time) (T := τ)
    (u := fun q => u₁ q - u₂ q - c * growthBarrier C τ q) hΩ hγ hlam hB hb le_rfl zero_le_one
    ?_ ?_ ?_ ?_ ?_ ?_ p₀ hp₀slab
  · linarith
  · refine ⟨C₁ + C₂, fun p hp => ?_⟩
    have h1 := hC₁ p (hslab _ hp)
    have h2 := hC₂ p (hslab _ hp)
    have h3 := le_abs_self (u₁ p)
    have h4 := neg_abs_le (u₂ p)
    have h5 : 0 ≤ c * growthBarrier C τ p := mul_nonneg hc (growthBarrier_pos C τ p).le
    show u₁ p - u₂ p - c * growthBarrier C τ p ≤ C₁ + C₂
    linarith
  · exact ((h₁'.2.1.mono (hslab _)).sub (h₂'.2.1.mono (hslab _))).sub
      (continuousOn_const.mul (continuous_growthBarrier C τ).continuousOn)
  · intro p hp
    exact ((h₁'.isSliceRegularAt hΩ hγ (hact _ hp)).sub
      (h₂'.isSliceRegularAt hΩ hγ (hact _ hp))).sub
      ((isSliceRegularAt_growthBarrier C τ p).const_mul c)
  · intro p hp
    have hr₁ := h₁'.isSliceRegularAt hΩ hγ (hact _ hp)
    have hr₂ := h₂'.isSliceRegularAt hΩ hγ (hact _ hp)
    have hrΦ := (isSliceRegularAt_growthBarrier C τ p).const_mul c
    rw [viscousTransportedOperator_sub (hr₁.sub hr₂) hrΦ, viscousTransportedOperator_sub hr₁ hr₂,
      viscousTransportedOperator_const_mul c (isSliceRegularAt_growthBarrier C τ p),
      h₁'.2.2.2.1 p (hact _ hp), h₂'.2.2.2.1 p (hact _ hp)]
    have hΦ := hCΦ 0 le_rfl zero_le_one τ p
    have hΦpos := growthBarrier_pos C τ p
    nlinarith
  · intro p hp hpT
    have hterm : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hpT ▸ hp.2.2⟩
    have hF' := hF (p.position, p.velocity) hterm.2
    have e1 := h₁'.2.2.2.2.1 p hterm
    have e2 := h₂'.2.2.2.2.1 p hterm
    have hΦτ : growthBarrier C τ p = 1 + PDE.vecNormSq p.position + PDE.vecNormSq p.velocity := by
      unfold growthBarrier radialSq
      rw [hpT]
      simp only [sub_self, mul_zero, Real.exp_zero, one_mul]
      ring
    show u₁ p - u₂ p - c * growthBarrier C τ p ≤ 0
    rw [hΦτ]
    linarith
  · intro p hp hfr
    have hlat : p ∈ evolutionLateralFrontier Ω γ τ := ⟨hp.2.1, hfr⟩
    show u₁ p - u₂ p - c * growthBarrier C τ p ≤ 0
    rw [h₁'.2.2.2.2.2 p hlat, h₂'.2.2.2.2.2 p hlat]
    have h5 : 0 ≤ c * growthBarrier C τ p := mul_nonneg hc (growthBarrier_pos C τ p).le
    linarith

end Comparison

end HypoellipticAleksandrov.KineticAleksandrov
