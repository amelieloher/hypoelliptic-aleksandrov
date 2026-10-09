module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import HypoellipticAleksandrov.Parabolic.HarnackChainGeometry
public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackScaling

/-!
# Fixed-chain source perturbation of parabolic Harnack

This module iterates the source-aware physical one-box Harnack estimate over
the fixed normalized chain, retaining one compact carrier and one source norm.
-/

@[expose] public section

open Set
open BigOperators

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

private theorem harnack_pow_iterate_add_error
    {n : Nat} {h e : Real} {Q : Nat -> Real}
    (hh : 0 <= h)
    (hstep : ∀ k < n, h * Q k <= Q (k + 1) + e) :
    ∀ k ≤ n,
      h ^ k * Q 0 <= Q k + e * (∑ j ∈ Finset.range k, h ^ j) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      have hih := ih (Nat.le_of_lt hklt)
      have hs := hstep k hklt
      calc
        h ^ (k + 1) * Q 0 = h * (h ^ k * Q 0) := by
          rw [pow_succ]
          ring
        _ <= h * (Q k + e * (∑ j ∈ Finset.range k, h ^ j)) :=
          mul_le_mul_of_nonneg_left hih hh
        _ = h * Q k + e * (h * (∑ j ∈ Finset.range k, h ^ j)) := by ring
        _ <= (Q (k + 1) + e) + e * (h * (∑ j ∈ Finset.range k, h ^ j)) :=
          calc
            h * Q k + e * (h * (∑ j ∈ Finset.range k, h ^ j)) =
                e * (h * (∑ j ∈ Finset.range k, h ^ j)) + h * Q k := by ring
            _ <= e * (h * (∑ j ∈ Finset.range k, h ^ j)) + (Q (k + 1) + e) :=
              add_le_add_right hs _
            _ = (Q (k + 1) + e) + e * (h * (∑ j ∈ Finset.range k, h ^ j)) := by
              ring
        _ = Q (k + 1) + e * ((h * (∑ j ∈ Finset.range k, h ^ j)) + 1) := by
          ring
        _ = Q (k + 1) + e * (∑ j ∈ Finset.range (k + 1), h ^ j) := by
          rw [geom_sum_succ]

private theorem harnack_geometric_sum_le_length
    {n : Nat} {h : Real} (hh0 : 0 <= h) (hh1 : h <= 1) :
    (∑ j ∈ Finset.range n, h ^ j) <= (n : Real) := by
  calc
    (∑ j ∈ Finset.range n, h ^ j) <= (Finset.range n).card • (1 : Real) :=
      Finset.sum_le_card_nsmul (Finset.range n) (fun j => h ^ j) 1
        (fun j hj => pow_le_one₀ hh0 hh1)
    _ = (n : Real) := by simp [Finset.card_range]

/-- A finite normalized Harnack chain with a single compact source carrier. -/
theorem exists_parabolic_harnack_fixed_chain_of_source
    (d : Nat) (hd : 1 <= d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam <= Lam) :
    ∃ h C : Real, 0 < h ∧ h <= 1 ∧ 0 < C ∧
      ∀ (K U : Set (TimeVelocity d)) (B : CoefficientField d)
        (q F : TimeVelocity d -> Real),
        IsCompact K -> K ⊆ U -> IsOpen U ->
        (∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          ∀ k ≤ harnackChainLength d,
            harnackChainClosedLinkBox z k ⊆ K) ->
        IsContinuousCoefficientOn B U -> ContDiffOn Real 2 q U ->
        ContinuousOn F U -> IsNonnegativeOn q K ->
        HasLowerEllipticityOn lam B K -> HasUpperEllipticityOn Lam B K ->
        (∀ x ∈ K, parabolicOperator B q x = F x) ->
        ∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          h * q harnackSource <= q (4, z) + C * parabolicLpNormOn d F K := by
  obtain ⟨hBox, CBox, hhBox0, hhBox1, hCBox, hBoxTheorem⟩ :=
    exists_source_local_parabolic_harnack d hd lam hlam Lam hlamLam
  let N : Nat := harnackChainLength d
  let p : Real := (d : Real) / ((d : Real) + 1)
  let h : Real := hBox ^ N
  let C : Real := (N : Real) * CBox * harnackChainRadius d ^ p
  have hNpos : 0 < N := by
    dsimp [N]
    exact harnackChainLength_pos hd
  have hNposReal : 0 < (N : Real) := by exact_mod_cast hNpos
  have hrpos : 0 < harnackChainRadius d := harnackChainRadius_pos hd
  have hp : 0 <= p := by
    dsimp [p]
    positivity
  have hrpowpos : 0 < harnackChainRadius d ^ p :=
    Real.rpow_pos_of_pos hrpos p
  have hh0 : 0 < h := pow_pos hhBox0 _
  have hh1 : h <= 1 := pow_le_one₀ hhBox0.le hhBox1
  have hC0 : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨h, C, hh0, hh1, hC0, ?_⟩
  intro K U B q F hK hKU hU hlinks hB hq hF hnonneg hlower hupper heq z hz
  let A : Real := parabolicLpNormOn d F K
  let e : Real := CBox * harnackChainRadius d ^ p * A
  let Q : Nat -> Real := fun k =>
    q (harnackChainTime d k, harnackChainVelocity z k)
  have hstep : ∀ k < N, hBox * Q k <= Q (k + 1) + e := by
    intro k hk
    have hk' : k < harnackChainLength d := by simpa only [N] using hk
    have hlink := hBoxTheorem K U B q F
      (harnackChainTime d k) (harnackChainVelocity z k) (harnackChainRadius d)
      (harnackChainRadius_pos hd) hK hKU hU
      (hlinks z hz k (Nat.le_of_lt hk')) hB hq hF hnonneg hlower hupper heq
      (harnackChainVelocity z (k + 1))
      (harnackChain_next_mem_terminalHalfCube hd hz hk')
    rw [← harnackChainTime_succ] at hlink
    simpa only [Q, e, A, p] using hlink
  have hrecurrence := harnack_pow_iterate_add_error hhBox0.le hstep N le_rfl
  have hsum : (∑ j ∈ Finset.range N, hBox ^ j) <= (N : Real) :=
    harnack_geometric_sum_le_length hhBox0.le hhBox1
  have hA0 : 0 <= A := ENNReal.toReal_nonneg
  have he0 : 0 <= e :=
    mul_nonneg (mul_nonneg hCBox.le (Real.rpow_nonneg hrpos.le p)) hA0
  have hsumMul : e * (∑ j ∈ Finset.range N, hBox ^ j) <= e * (N : Real) :=
    mul_le_mul_of_nonneg_left hsum he0
  have hterminal : hBox ^ N * Q 0 <= Q N + e * (N : Real) := by
    apply hrecurrence.trans
    calc
      Q N + e * (∑ j ∈ Finset.range N, hBox ^ j) =
          e * (∑ j ∈ Finset.range N, hBox ^ j) + Q N := by ring
      _ <= e * (N : Real) + Q N := add_le_add_left hsumMul _
      _ = Q N + e * (N : Real) := by ring
  have hsource : Q 0 = q harnackSource := by
    simp only [Q, harnackChainTime_zero, harnackChainVelocity_zero, harnackSource]
  have htarget : Q N = q (4, z) := by
    dsimp [Q]
    rw [show N = harnackChainLength d by rfl,
      harnackChainTime_terminal hd, harnackChainVelocity_terminal hd z]
  change hBox ^ N * q harnackSource <=
    q (4, z) + ((N : Real) * CBox * harnackChainRadius d ^ p) *
      parabolicLpNormOn d F K
  rw [← hsource, ← htarget]
  calc
    hBox ^ N * Q 0 <= Q N + e * (N : Real) := hterminal
    _ = Q N + ((N : Real) * CBox * harnackChainRadius d ^ p) *
        parabolicLpNormOn d F K := by
      dsimp [e, A]
      ring

end

end HypoellipticAleksandrov.Parabolic
