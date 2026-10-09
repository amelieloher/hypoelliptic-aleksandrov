module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationIterationOverlap
import Mathlib.Tactic

/-! # Source overlap induction on the finite Gaussian block chain -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Successive source Gaussian blocks propagate their comparison through the halved tube. -/
theorem propagation_overlap_induction {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell TP : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (n : ℕ) (hnTP : (n : ℝ) * h ≤ TP)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A : ℝ} (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinitial : ∀ P ∈ corridor tminus (-T0) TP (kx / 2) (kv / 2) x v,
      P.time ≤ tminus → ell ≤ u P) :
    ∀ k : ℕ, k < n → ∀ P ∈ closure (backwardCylinder
      ⟨tminus + (k : ℝ) * h + h, x ((k : ℝ) * h + h), v ((k : ℝ) * h + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ((barrierGamma (barrierL d lam Lam H T1)) ^ k *
          Real.exp (-(barrierL d lam Lam H T1) ^ 2 / 512) * ell)
        tminus ((k : ℝ) * h) x v P ≤ u P := by
  let L := barrierL d lam Lam H T1
  let gamma := barrierGamma L
  let a := fun k : ℕ => gamma ^ k * Real.exp (-L ^ 2 / 512) * ell
  have hL : 0 < L := barrierL_pos (H := H) hd hlam hLam (hT0.le.trans hT1)
  have hgamma := (barrierGamma_bounds hL).1
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (mul_nonneg (pow_nonneg hgamma.le k) (Real.exp_pos _).le) hell
  have hstep : ∀ k, a (k + 1) = gamma * a k := by
    intro k
    dsimp only [a]
    rw [pow_succ]
    ring
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  intro k
  induction k with
  | zero =>
    intro hkn
    simp only [Nat.cast_zero, zero_mul]
    have hb : h ≤ TP := by
      have he := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hh.le
      norm_num at he
      exact he.trans hnTP
    apply propagation_one_block hd hlam hLam hH hT0 hT1 hkx hkv hh hhstar (ha 0)
      A hA O tminus 0 TP (by norm_num) (by simpa only [zero_add] using hb)
      hx hv hkin hLip htube u hnonneg hu
    intro P hP ht
    have hcont := propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
      tminus 0 TP (by norm_num) (by
        have he := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hh.le
        norm_num at he ⊢
        exact he.trans hnTP) hv.continuous hkin hLip hP
    have hupper := gaussianBarrier_initial_upper hlam hh Lam H L (a 0) tminus 0
      hLam (ha 0) hbudget x v P ht
    have heq : a 0 * Real.exp (L ^ 2 / 512) = ell := by
      dsimp only [a]
      rw [pow_zero, one_mul, mul_comm _ ell, mul_assoc, ← Real.exp_add]
      simp only [neg_div, neg_add_cancel, Real.exp_zero, mul_one]
    exact (hupper.trans_eq heq).trans (hinitial P hcont (by linarith only [ht]))
  | succ k ih =>
    intro hkn
    have hk : k < n := Nat.lt_trans (Nat.lt_succ_self k) hkn
    have hb : ((k + 1 : ℕ) : ℝ) * h + h ≤ TP := by
      have he := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hh.le
      push_cast at he ⊢
      linarith only [he, hnTP]
    apply propagation_one_block hd hlam hLam hH hT0 hT1 hkx hkv hh hhstar (ha (k + 1))
      A hA O tminus (((k + 1 : ℕ) : ℝ) * h) TP (by positivity) hb
      hx hv hkin hLip htube u hnonneg hu
    intro P hP ht
    by_cases hp : 0 < gaussianBarrier lam Lam H h L (a (k + 1))
        tminus (((k + 1 : ℕ) : ℝ) * h) x v P
    · rw [hstep] at hp
      obtain ⟨hprev, hcompare⟩ := gaussianBarrier_overlap_compare hd hlam hLam hH hT0 hT1
        hh hhstar (ha k) tminus (((k + 1 : ℕ) : ℝ) * h)
        hv.continuous hkin hLip P ht hp
      have heq : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by push_cast; ring
      rw [heq, ← add_assoc] at hprev
      have hprevtime : ((k + 1 : ℕ) : ℝ) * h - h = (k : ℝ) * h := by
        rw [heq]
        ring
      rw [hprevtime] at hcompare
      rw [hstep]
      exact hcompare.trans (ih hk P hprev)
    · have hcont := propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
        tminus (((k + 1 : ℕ) : ℝ) * h) TP (by positivity) hb hv.continuous hkin hLip hP
      exact (le_of_not_gt hp).trans (hnonneg P (htube hcont))

end HypoellipticAleksandrov.KineticAleksandrov.Holder
