module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyWholeSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Locally uniform whole-space limits of actual ball solutions -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter
open scoped Topology MatrixOrder

/-- A Euclidean radial cutoff lies strictly inside every larger diffused ball. -/
theorem mem_movingBall_of_radialSq_le {n : ℕ} {S r : ℝ} (hS : 0 ≤ S) (hr : S < r)
    {p : KineticPoint n} (hp : radialSq p ≤ S ^ 2) :
    p.position ∈ movingDomain (PDE.euclideanBall 0 r) (fun _ => 0) p.time := by
  have hsq : PDE.vecNormSq p.position ≤ S ^ 2 := by
    dsimp only [radialSq] at hp
    linarith [PDE.vecNormSq_nonneg p.velocity]
  have hn : PDE.vecEuclideanNorm p.position ≤ S := Real.sqrt_le_iff.mpr ⟨hS, hsq⟩
  apply (mem_movingBall_iff_norm_lt (hS.trans_lt hr)).mpr
  simpa only [sub_zero] using hn.trans_lt hr

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- Actual expanding-ball solutions are uniformly Cauchy on every fixed bounded whole-space
cylinder, by the proved pure-growth comparison estimate. -/
theorem uniformCauchySeqOn_wholeSpace_ball_solutions :
    UniformCauchySeqOn v atTop
      (movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2}) := by
  let K := movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
  obtain ⟨M0, hM0⟩ := (isCompact_movingClosedSlab_inter (Ω := univ)
    (γ := fun _ : ℝ => (0 : PDE.Vec n)) continuous_const α τ S0).bddAbove_image
    (continuous_growthBarrier cg τ).continuousOn
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦ : ∀ p ∈ K, growthBarrier cg τ p ≤ M :=
    fun p hp => (hM0 ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro e he
  obtain ⟨δ, A, S, hδ, -, -, hA, -, -, hS, herr⟩ :=
    exists_small_dirichlet_comparison_parameters (κ := 1) (d := 1) (δ0 := 1) (r0 := 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num) (by norm_num) hC hM he S0
  have hw : 0 ≤ barrierW 1 (δ + 3 / 2 * A) / barrierW 1 1 :=
    div_nonneg (barrierW_pos (by norm_num) (by linarith)).le
      (barrierW_pos (by norm_num) (by norm_num)).le
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hrlim.eventually (eventually_gt_atTop |S|))
  refine ⟨N, ?_⟩
  intro j hj k hk p hp
  let ix (i : Fin 2) := if i = 0 then j else k
  have hix (i : Fin 2) : N ≤ ix i := by dsimp [ix]; split_ifs <;> assumption
  have hpS : p ∈ movingClosedSlab univ (fun _ => 0) α τ ∩
      {q | radialSq q ≤ |S| ^ 2} := ⟨hp.1, by
        rw [sq_abs]
        exact (show radialSq p ≤ S0 ^ 2 from hp.2).trans hS⟩
  have hc := abs_sub_le_growth_ball_solutions hlam hB hb hε hε1 (abs_nonneg S) hC
    F hFC (fun i => r (ix i)) (fun i => hN _ (hix i)) (fun i => v (ix i))
    (fun i => hv _) p hpS
  have hden : 0 ≤ 1 + S ^ 2 := by positivity
  have hnum : growthBarrier cg τ p / (1 + S ^ 2) ≤ M / (1 + S ^ 2) :=
    div_le_div_of_nonneg_right (hΦ p hp) hden
  have hfinal := hc.trans_lt (by
    rw [sq_abs]
    exact (mul_le_mul_of_nonneg_left
      (hnum.trans (le_add_of_nonneg_right hw)) (by positivity)).trans_lt herr)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [ix, ite_true, h10, ite_false, Real.dist_eq] using hfinal

/-- Actual expanding-ball solutions converge uniformly to one bounded continuous limit
on every fixed whole-space cylinder. -/
theorem tendstoUniformlyOn_wholeSpace_ball_solutions :
    TendstoUniformlyOn v (fun p => limUnder atTop (fun j => v j p)) atTop
      (movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2}) ∧
    ContinuousOn (fun p => limUnder atTop (fun j => v j p))
      (movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2}) ∧
    ∀ p ∈ movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2},
      |limUnder atTop (fun j => v j p)| ≤ C := by
  let K := movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hCau := uniformCauchySeqOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε hε1 hC F hFC r hrlim v hv
  have hU := hCau.tendstoUniformlyOn_of_tendsto
    (f := fun p => limUnder atTop (fun j => v j p))
    (fun p hp => (hCau.cauchySeq hp).tendsto_limUnder)
  have hnear : ∀ᶠ j : ℕ in atTop, |S0| < r j :=
    hrlim.eventually (eventually_gt_atTop |S0|)
  have hclosed (j : ℕ) (hj : |S0| < r j) :
      K ⊆ evolutionPastClosedCylinder (PDE.euclideanBall 0 (r j)) (fun _ => 0) τ :=
    fun p hp => ⟨hp.1.2.1, subset_closure (mem_movingBall_of_radialSq_le
      (abs_nonneg S0) hj (by simpa only [sq_abs] using (show radialSq p ≤ S0 ^ 2 from hp.2)))⟩
  refine ⟨hU, hU.continuousOn ?_, fun p hp => ?_⟩
  · exact (hnear.mono fun j hj => (hv j).2.1.mono (hclosed j hj)).frequently
  · apply le_of_tendsto (hU.tendsto_at hp |>.abs)
    exact hnear.mono fun j hj => classical_abs_le_const
      (PDE.isOpen_euclideanBall 0 (r j)) continuous_const hlam hB hb hε hε1
      (hv j) hFC p (hclosed j hj hp)

end Data

end HypoellipticAleksandrov.KineticAleksandrov
