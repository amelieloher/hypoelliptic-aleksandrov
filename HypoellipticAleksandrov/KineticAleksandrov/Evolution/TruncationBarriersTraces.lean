module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriers
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationBarriers
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz

/-!
# Uniform boundary traces for the actual viscous solutions

Companion paper, (A.1), zero-viscosity part.  For a family `u_ε`, `ε ∈ (0, 1]`, of viscous classical
terminal solutions with smooth compactly supported terminal datum `F`, the terminal trace
`u_ε → F(p₀)` at a terminal point `p₀` and the lateral trace `u_ε → 0` at a lateral point `p₀` hold
uniformly in `ε`: the neighbourhood `O` of `p₀` for a given tolerance `η` does not depend on `ε`.

The proof chooses a finite slab around `p₀`, the Lipschitz constant of `γ` on it, the
collar scale `d_*` from the distance of the compact support of `F` to the terminal boundary, and
the operator bound `M` of `FiniteSlabBarriersTerminal`, and then applies the two barriers
on balls or on the whole space.
The admissible interval domains of dimension `1` are balls (`BarrierIntervalGeometry`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- The collar scale: the compact support of a terminal datum of the moving ball lies at positive
distance from the terminal boundary, so some `d_* < r/4` has `2 d_* ≤` that distance. -/
theorem exists_collar_scale {n : ℕ} {c : PDE.Vec n} {r : ℝ} (hr : 0 < r) {γ : ℝ → PDE.Vec n}
    {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r) γ τ F) :
    ∃ d : ℝ, 0 < d ∧ d < r / 4 ∧ ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - (γ τ + c)) := by
  have hcpt : IsCompact (tsupport (F : EvolutionAmbientState n → ℝ)) := hF.2.1.isCompact
  have hcont : Continuous (fun q : EvolutionAmbientState n =>
      r - PDE.vecEuclideanNorm (q.1 - (γ τ + c))) :=
    continuous_const.sub (PDE.continuous_vecEuclideanNorm.comp
      (continuous_fst.sub continuous_const))
  obtain ⟨m, hm, hmle⟩ := hcpt.exists_forall_le' (a := 0) hcont.continuousOn (fun q hq => by
    have h1 : q.1 ∈ movingDomain (PDE.euclideanBall c r) γ τ := (hF.2.2 hq).1
    have h2 := mem_movingDomain_euclideanBall_iff.mp h1
    have h3 : PDE.vecEuclideanNorm (q.1 - (γ τ + c)) < r := by
      unfold PDE.vecEuclideanNorm
      exact (Real.sqrt_lt' hr).mpr h2
    linarith)
  refine ⟨min (m / 2) (r / 8), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), fun q hq => ?_⟩
  have := hmle q hq
  have h2 : min (m / 2) (r / 8) ≤ m / 2 := min_le_left _ _
  linarith

/-- Terminal trace from a uniform terminal window: if `|u_i - F| ≤ (τ - σ) M` for all `i` on the
past cylinder near the terminal time, then the terminal trace at a terminal point is uniform. -/
theorem terminal_trace_of_window {n : ℕ} {ι : Type*} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} {τ : ℝ} (F : BoundedBorel (EvolutionAmbientState n))
    (hF : Continuous (F : EvolutionAmbientState n → ℝ)) (u : ι → KineticPoint n → ℝ)
    {M δ₀ : ℝ} (hM0 : 0 ≤ M) (hδ₀ : 0 < δ₀)
    (hwin : ∀ i, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, τ - δ₀ < p.time →
      |u i p - F (p.position, p.velocity)| ≤ (τ - p.time) * M)
    {p₀ : KineticPoint n} (hp₀ : p₀.time = τ) {η : ℝ} (hη : 0 < η) :
    ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
      ∀ i, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
        |u i p - F (p₀.position, p₀.velocity)| ≤ η := by
  have hK : 0 < η / (2 * (M + 1)) := by positivity
  set δ := min δ₀ (η / (2 * (M + 1))) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hK
  have hFe : Continuous (fun p : KineticPoint n => F (p.position, p.velocity)) :=
    hF.comp (continuous_position.prodMk continuous_velocity)
  refine ⟨{p | τ - δ < p.time} ∩
    {p | |F (p.position, p.velocity) - F (p₀.position, p₀.velocity)| < η / 2}, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_time).inter
      (isOpen_lt ((hFe.sub continuous_const).abs) continuous_const)
  · refine ⟨?_, ?_⟩
    · show τ - δ < p₀.time
      rw [hp₀]
      linarith
    · show |F (p₀.position, p₀.velocity) - F (p₀.position, p₀.velocity)| < η / 2
      simp only [sub_self, abs_zero]
      linarith
  · rintro i p ⟨⟨hpt, hpF⟩, hcyl⟩
    have hpt' : τ - δ < p.time := hpt
    have hpF' : |F (p.position, p.velocity) - F (p₀.position, p₀.velocity)| < η / 2 := hpF
    have hδ₀le : δ ≤ δ₀ := min_le_left _ _
    have hδKle : δ ≤ η / (2 * (M + 1)) := min_le_right _ _
    have h1 := hwin i p hcyl (by linarith)
    have h2 : (τ - p.time) * M ≤ δ * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have h3 : δ * M ≤ η / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hδKle hM0
    have h4 : η / (2 * (M + 1)) * M ≤ η / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 := abs_sub_le (u i p) (F (p.position, p.velocity)) (F (p₀.position, p₀.velocity))
    linarith

/-- **Uniform traces** (companion paper, (A.1), zero-viscosity part).  Uniform terminal and lateral
traces for the family of actual viscous solutions: for every terminal point `p₀` and tolerance `η`
there is a neighbourhood `O` of `p₀`, independent of `ε ∈ (0, 1]`, on which `|u_ε - F(p₀)| ≤ η`
(past cylinder), and likewise `|u_ε| ≤ η` near every lateral frontier point.  The standing premises
(`Ω` admissible, `γ` continuous piecewise `C¹`, the Loewner bounds of `B`, the Lipschitz drift)
are explicit. -/
theorem uniform_viscous_boundary_traces {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (u : {ε : ℝ // 0 < ε ∧ ε ≤ 1} → KineticPoint n → ℝ)
    (hu : ∀ ε, IsClassicalViscousTerminalSolution Ω γ B b ε.1 τ F (u ε)) :
    (∀ p₀ ∈ evolutionTerminalClosure Ω γ τ, ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
        ∀ ε, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
          |u ε p - F (p₀.position, p₀.velocity)| ≤ η) ∧
    (∀ p₀ ∈ evolutionLateralFrontier Ω γ τ, ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
        ∀ ε, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
          |u ε p| ≤ η) := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_terminalDatum_operator_bound hlam hB hb τ F hF
  obtain ⟨C, -, hC⟩ := F.exists_bound
  have hFc : Continuous (F : EvolutionAmbientState n → ℝ) := hF.1.continuous
  rcases eq_univ_or_exists_euclideanBall_of_isAdmissibleEvolutionDomain hΩ with
    rfl | ⟨c, r, hr, rfl⟩
  · refine ⟨fun p₀ hp₀ η hη => ?_, fun p₀ hp₀ η hη => ?_⟩
    · refine terminal_trace_of_window F hFc u hM0 one_pos (fun i p hp ht => ?_) hp₀.1 hη
      exact wholeSpace_terminalDatum_bound hlam hB hb rfl (τ - 1) τ (by linarith) F hF i.1
        i.2.1.le i.2.2 M hM0 (fun q _ => hM i.1 i.2.1.le i.2.2 q) (u i) (hu i) p
        ⟨by linarith, hp.1, hp.2⟩
    · exfalso
      have h := hp₀.2
      rw [movingDomain_univ, frontier_univ] at h
      exact notMem_empty _ h
  · obtain ⟨d, hd, hdr, hsupp⟩ := exists_collar_scale hr hF
    refine ⟨fun p₀ hp₀ η hη => ?_, fun p₀ hp₀ η hη => ?_⟩
    · obtain ⟨L, hL, hγL⟩ := exists_evolution_curve_lipschitzOn hγ (τ - 1) τ (by linarith)
      have hL1 : 0 < d / (1 + L) := div_pos hd (by linarith)
      refine terminal_trace_of_window F hFc u hM0 (lt_min one_pos hL1)
        (fun i p hp ht => ?_) hp₀.1 hη
      have hslab : p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (τ - 1) τ :=
        ⟨by linarith [min_le_left (1 : ℝ) (d / (1 + L))], hp.1, hp.2⟩
      exact (two_barriers_on_finite_slab hr hγ (τ - 1) τ (by linarith) L hL hγL hlam hB hb
        i.2.1.le i.2.2 hF d hd hdr hsupp C M hC (fun q _ => hM i.1 i.2.1.le i.2.2 q)
        (hu i)).2 p hslab (by linarith [min_le_right (1 : ℝ) (d / (1 + L))])
    · have hpτ : p₀.time ≤ τ := hp₀.1
      obtain ⟨L, hL, hγL⟩ := exists_evolution_curve_lipschitzOn hγ (p₀.time - 1) τ
        (by linarith)
      have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
      have hW : 0 < barrierW (collarKappa L lam) d := barrierW_pos hκ hd
      have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
      have hDc : Continuous (fun p : KineticPoint n =>
          r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) :=
        continuous_const.sub (PDE.continuous_vecEuclideanNorm.comp
          (continuous_position.sub ((hγ.1.comp continuous_time).add continuous_const)))
      have hwc : Continuous (barrierW (collarKappa L lam)) := by
        unfold barrierW
        fun_prop
      have hD0 : r - PDE.vecEuclideanNorm (p₀.position - (γ p₀.time + c)) = 0 := by
        have hS := vecNormSq_eq_of_mem_frontier_movingDomain hp₀.2
        have : PDE.vecEuclideanNorm (p₀.position - (γ p₀.time + c)) = r := by
          unfold PDE.vecEuclideanNorm
          rw [hS, Real.sqrt_sq hr.le]
        linarith
      have hw0 : barrierW (collarKappa L lam) 0 = 0 := by simp [barrierW]
      refine ⟨{p | p₀.time - 1 < p.time} ∩
        {p | C * barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) <
            η * barrierW (collarKappa L lam) d}, ?_,
        ⟨(by show p₀.time - 1 < p₀.time; linarith), ?_⟩, ?_⟩
      · exact (isOpen_lt continuous_const continuous_time).inter
          (isOpen_lt (continuous_const.mul (hwc.comp hDc)) continuous_const)
      · show C * barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p₀.position - (γ p₀.time + c))) <
            η * barrierW (collarKappa L lam) d
        rw [hD0, hw0, mul_zero]
        exact mul_pos hη hW
      · rintro i p ⟨⟨hpt, hpD⟩, hcyl⟩
        have hpt' : p₀.time - 1 < p.time := hpt
        have hpD' : C * barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) <
              η * barrierW (collarKappa L lam) d := hpD
        have hslab : p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (p₀.time - 1) τ :=
          ⟨hpt'.le, hcyl.1, hcyl.2⟩
        have h1 := (two_barriers_on_finite_slab hr hγ (p₀.time - 1) τ (by linarith) L hL hγL
          hlam hB hb i.2.1.le i.2.2 hF d hd hdr hsupp C M hC
          (fun q _ => hM i.1 i.2.1.le i.2.2 q) (hu i)).1 p hslab
        have h2 : C * min 1 (barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) d) ≤
            C * (barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) d) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
        have h3 : C * (barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) d) < η := by
          rw [← mul_div_assoc, div_lt_iff₀ hW]
          exact hpD'
        linarith

end HypoellipticAleksandrov.KineticAleksandrov
