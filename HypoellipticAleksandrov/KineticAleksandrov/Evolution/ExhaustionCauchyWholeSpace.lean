module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBall

/-!
# Pure-growth comparison for whole-space exhaustion

The actual ball solutions have radii larger than the common radial cutoff.
Thus the common cylinder has no physical lateral face and only the growth error remains.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set
open scoped Topology MatrixOrder

/-- Actual classical solutions on sufficiently large balls satisfy the pure-growth
Cauchy estimate on a common whole-space inner cylinder. -/
theorem abs_sub_le_growth_ball_solutions {n : ℕ} {lam Lam Lb : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hb : HasEuclideanLipschitzDrift Lb b) {ε τ α S C : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (r : Fin 2 → ℝ) (hr : ∀ i, S < r i) (v : Fin 2 → KineticPoint n → ℝ)
    (hv : ∀ i, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r i))
      (fun _ => 0) B b ε τ F (v i)) :
    ∀ p ∈ movingClosedSlab Set.univ (fun _ => 0) α τ ∩ {q | radialSq q ≤ S ^ 2},
      |v 0 p - v 1 p| ≤ 2 * C *
        (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) τ p /
          (1 + S ^ 2)) := by
  let K := movingClosedSlab Set.univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {q | radialSq q ≤ S ^ 2}
  let A := movingActiveSlab Set.univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {q | radialSq q < S ^ 2}
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
  let Φ := growthBarrier (n := n) cg τ
  let k := 2 * C / (1 + S ^ 2)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hcg : 0 ≤ cg := by
    dsimp [cg, growthConstant]
    have := PDE.vecEuclideanNorm_nonneg (b 0)
    positivity
  have hmem (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) :
      p.position ∈ movingDomain (PDE.euclideanBall 0 (r i)) (fun _ => 0) p.time := by
    have hsq : PDE.vecNormSq p.position ≤ S ^ 2 := by
      have ht : radialSq p ≤ S ^ 2 := hp.2
      dsimp only [radialSq] at ht
      linarith [PDE.vecNormSq_nonneg p.velocity]
    have hn : PDE.vecEuclideanNorm p.position ≤ S := Real.sqrt_le_iff.mpr ⟨hS, hsq⟩
    apply (mem_movingBall_iff_norm_lt (hS.trans_lt (hr i))).mpr
    simpa only [sub_zero] using hn.trans_lt (hr i)
  have hclosed (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) :
      p ∈ evolutionPastClosedCylinder (PDE.euclideanBall 0 (r i)) (fun _ => 0) τ :=
    ⟨hp.1.2.1, subset_closure (hmem i p hp)⟩
  have hvc (i : Fin 2) : ContinuousOn (v i) K := (hv i).2.1.mono (hclosed i)
  have hAK : A ⊆ K := fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.1.le, subset_closure hp.1.2.2⟩,
      (show radialSq p < S ^ 2 from hp.2).le⟩
  have hopen (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) :
      p ∈ evolutionPastOpenCylinder (PDE.euclideanBall 0 (r i)) (fun _ => 0) τ :=
    ⟨hp.1.2.1, hmem i p (hAK hp)⟩
  have hreg (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) : IsSliceRegularAt (v i) p :=
    (hv i).isSliceRegularAt (PDE.isOpen_euclideanBall 0 (r i)) continuous_const
      (hopen i p hp)
  have hop (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) :
      viscousTransportedOperator B b ε (v i) p = 0 := (hv i).2.2.2.1 p (hopen i p hp)
  have hbound (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) : |v i p| ≤ C :=
    classical_abs_le_const (PDE.isOpen_euclideanBall 0 (r i)) continuous_const
      hlam hB hb hε hε1 (hv i) hFC p (hclosed i p hp)
  have hterm (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) (ht : p.time = τ) :
      v i p = F (p.position, p.velocity) :=
    (hv i).2.2.2.2.1 p ⟨ht, by simpa only [ht] using (hclosed i p hp).2⟩
  have hΦreg (p : KineticPoint n) := isSliceRegularAt_growthBarrier cg τ p
  have hΦop (p : KineticPoint n) : viscousTransportedOperator B b ε Φ p ≤ -Φ p :=
    viscousTransportedOperator_growthBarrier_le hε1 (fun t y z => (hB t y z).2) hb τ p
  have hΦpos (p : KineticPoint n) : 0 < Φ p := growthBarrier_pos cg τ p
  have hwhole (t : ℝ) : movingDomain Set.univ (fun _ : ℝ => (0 : PDE.Vec n)) t = univ := by
    ext y
    rw [mem_movingDomain_iff]
    simp only [mem_univ]
  have side (s : ℝ) (hs : s = 1 ∨ s = -1) : ∀ p ∈ K,
      s * (v 0 p - v 1 p) ≤ k * Φ p := by
    have hmax := bounded_comparison (b := b) isOpen_univ continuous_const hlam hB hε
      (Ω := univ) (γ := fun _ => 0) (a := α) (T := τ) (R := S)
      (u := fun p => s * (v 0 p - v 1 p) - k * Φ p)
      ((((hvc 0).sub (hvc 1)).const_smul s).sub
        ((continuous_const.mul (continuous_growthBarrier cg τ)).continuousOn))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      have := hmax p hp
      linarith
    · intro p hp
      exact (((hreg 0 p hp).sub (hreg 1 p hp)).const_mul s).sub ((hΦreg p).const_mul k)
    · intro p hp
      rw [viscousTransportedOperator_sub
          (((hreg 0 p hp).sub (hreg 1 p hp)).const_mul s) ((hΦreg p).const_mul k),
        viscousTransportedOperator_const_mul s ((hreg 0 p hp).sub (hreg 1 p hp)),
        viscousTransportedOperator_sub (hreg 0 p hp) (hreg 1 p hp), hop 0 p hp, hop 1 p hp,
        viscousTransportedOperator_const_mul k (hΦreg p)]
      have hn := mul_nonpos_of_nonneg_of_nonpos hk
        ((hΦop p).trans (by linarith [hΦpos p]))
      linarith
    · intro p hp ht
      rw [hterm 0 p hp ht, hterm 1 p hp ht, sub_self, mul_zero]
      simpa only [zero_sub] using neg_nonpos.mpr (mul_nonneg hk (hΦpos p).le)
    · intro p _ hfr
      rw [hwhole, frontier_univ] at hfr
      exact hfr.elim
    · intro p hp he
      have h0 := abs_le.mp (hbound 0 p hp)
      have h1 := abs_le.mp (hbound 1 p hp)
      have hdom := one_add_radialSq_le_growthBarrier hcg hp.1.2.1
      rw [he] at hdom
      have hb' : 2 * C ≤ k * Φ p := by
        dsimp only [k]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hdom (by positivity)
      rcases hs with rfl | rfl <;> linarith
  intro p hp
  have h0 := side 1 (Or.inl rfl) p hp
  have h1 := side (-1) (Or.inr rfl) p hp
  have he : k * Φ p = 2 * C * (Φ p / (1 + S ^ 2)) := by dsimp [k]; ring
  rw [he] at h0 h1
  exact abs_le.mpr ⟨by linarith, by simpa only [one_mul] using h0⟩

end HypoellipticAleksandrov.KineticAleksandrov
