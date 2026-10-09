module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosure
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDerivativeNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedGeometry
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Finite closed dyadic parabolic Morrey tails

This module telescopes the closed one-step dyadic projection estimate along a
finite addressed prefix.  It proves no infinite-chain or representative result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

private theorem parabolicDyadicTruncate_le_succ_eq_truncate_parent
    {d m n : Nat} (hmn : m <= n) (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index =
      parabolicDyadicTruncate hmn (parabolicDyadicParent index) := by
  funext j
  simp only [parabolicDyadicTruncate, parabolicDyadicParent]
  apply congrArg index
  exact Fin.ext (by rfl)

private theorem parabolicDyadicSourceBox_radius_rpow_truncate_mul
    {d m n : Nat} (hmn : m <= n) (index : ParabolicDyadicIndex d n)
    (alpha : Real) :
    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius ^ alpha *
        ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (parabolicDyadicSourceBox index).radius ^ alpha := by
  change ((2 : Real) ^ m)⁻¹ ^ alpha * ((2 : Real) ^ (-alpha)) ^ (n - m) =
    ((2 : Real) ^ n)⁻¹ ^ alpha
  have hbase (k : Nat) : ((2 : Real) ^ k)⁻¹ ^ alpha =
      (2 : Real) ^ (-(k : Real) * alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : Real) <= 2),
      ← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  have hfactor : ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (2 : Real) ^ (-alpha * ((n - m : Nat) : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  rw [hbase m, hbase n, hfactor, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
  congr 1
  rw [Nat.cast_sub hmn]
  ring

private theorem parabolicMorreyDerivativeLpNorm_nonneg (d : Nat)
    (u : TimeVelocity d -> Real) : 0 <= parabolicMorreyDerivativeLpNorm d u := by
  unfold parabolicMorreyDerivativeLpNorm parabolicLpNorm parabolicELpNorm
  refine add_nonneg ENNReal.toReal_nonneg ?_
  refine Finset.sum_nonneg fun i _ => ?_
  refine Finset.sum_nonneg fun j _ => ?_
  exact ENNReal.toReal_nonneg

private theorem parabolicMorreyDyadicTruncateProjectionClosedFiniteTail
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (m n : Nat) (hmn : m <= n) (index : ParabolicDyadicIndex d n)
        (u : TimeVelocity d -> Real),
        ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∀ z : TimeVelocity d,
          z ∈ parabolicClosedBox 1
              (parabolicDyadicSourceBox index).radius
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center ->
          |parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center
              (parabolicDyadicSourceBox index).radius u z -
            parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).baseTime
              (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).center
              (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius u z| <=
            C * (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius ^
                  parabolicMorreyExponent d *
              (∑ k ∈ Finset.range (n - m),
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) *
              parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C, hCpos, hstep⟩ :=
    exists_parabolicMorreyDyadicChildProjectionClosedConst d hd
  refine ⟨C, hCpos, ?_⟩
  intro m n hmn index u hu huc z hz
  have huJet : ParabolicSmoothJetMemLp d u :=
    parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
  induction n, hmn using Nat.le_induction with
  | base =>
      simp [parabolicDyadicTruncate_self]
  | succ n hmn ih =>
      let parent := parabolicDyadicParent index
      let child : ParabolicDyadicChild d := index (Fin.last n)
      have hindex : index = parabolicDyadicChildIndex parent child := by
        simpa only [parent, child] using
          (parabolicDyadicChildIndex_parent_last index).symm
      have hzParent : z ∈ parabolicClosedBox 1
          (parabolicDyadicSourceBox parent).radius
          (parabolicDyadicSourceBox parent).baseTime
          (parabolicDyadicSourceBox parent).center := by
        have hzChild : z ∈ parabolicClosedBox 1
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center := by
          simpa only [hindex] using hz
        exact parabolicDyadicClosedForwardBox_child_subset parent child hzChild
      have hih := ih parent hzParent
      have htrunc : parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index =
          parabolicDyadicTruncate hmn parent := by
        simpa only [parent] using
          parabolicDyadicTruncate_le_succ_eq_truncate_parent hmn index
      have hstep' := hstep n parent child u hu z (by simpa only [hindex] using hz)
      have hnorm : parabolicMorreyDerivativeLpNormOn d u
          (parabolicBox 1 (parabolicDyadicSourceBox parent).radius
            (parabolicDyadicSourceBox parent).baseTime
            (parabolicDyadicSourceBox parent).center) <=
          parabolicMorreyDerivativeLpNorm d u :=
        parabolicMorreyDerivativeLpNormOn_le u _ huJet
      have hstepNorm : |parabolicMorreyBoxAffineProjection
          (parabolicDyadicSourceBox index).baseTime
          (parabolicDyadicSourceBox index).center
          (parabolicDyadicSourceBox index).radius u z -
          parabolicMorreyBoxAffineProjection
          (parabolicDyadicSourceBox parent).baseTime
          (parabolicDyadicSourceBox parent).center
          (parabolicDyadicSourceBox parent).radius u z| <=
          C * (parabolicDyadicSourceBox parent).radius ^ parabolicMorreyExponent d *
            parabolicMorreyDerivativeLpNorm d u := by
        simpa only [hindex, parabolicMorreyDerivativeLpNormOn] using
          (hstep'.trans (mul_le_mul_of_nonneg_left hnorm
            (mul_nonneg hCpos.le (Real.rpow_nonneg
              (parabolicDyadicSourceBox_radius_pos parent).le _))))
      have hparentRadius := parabolicDyadicSourceBox_radius_rpow_truncate_mul
        hmn parent (parabolicMorreyExponent d)
      have hraw : 0 <= parabolicMorreyDerivativeLpNorm d u :=
        parabolicMorreyDerivativeLpNorm_nonneg d u
      rw [htrunc]
      rw [hindex]
      rw [Nat.succ_sub hmn, Finset.sum_range_succ]
      calc
        |parabolicMorreyBoxAffineProjection
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center
            (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius u z -
          parabolicMorreyBoxAffineProjection
            (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).baseTime
            (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).center
            (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius u z| <=
            |parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
                (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center
                (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius u z -
              parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox parent).baseTime
                (parabolicDyadicSourceBox parent).center
                (parabolicDyadicSourceBox parent).radius u z| +
              |parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox parent).baseTime
                (parabolicDyadicSourceBox parent).center
                (parabolicDyadicSourceBox parent).radius u z -
              parabolicMorreyBoxAffineProjection
                (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).baseTime
                (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).center
                (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius u z| := by
              rw [show parabolicMorreyBoxAffineProjection
                    (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
                    (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center
                    (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius u z -
                  parabolicMorreyBoxAffineProjection
                    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).baseTime
                    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).center
                    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius u z =
                  (parabolicMorreyBoxAffineProjection
                    (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).baseTime
                    (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).center
                    (parabolicDyadicSourceBox (parabolicDyadicChildIndex parent child)).radius u z -
                    parabolicMorreyBoxAffineProjection
                      (parabolicDyadicSourceBox parent).baseTime
                      (parabolicDyadicSourceBox parent).center
                      (parabolicDyadicSourceBox parent).radius u z) +
                    (parabolicMorreyBoxAffineProjection
                      (parabolicDyadicSourceBox parent).baseTime
                      (parabolicDyadicSourceBox parent).center
                      (parabolicDyadicSourceBox parent).radius u z -
                      parabolicMorreyBoxAffineProjection
                        (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).baseTime
                        (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).center
                        (parabolicDyadicSourceBox
                          (parabolicDyadicTruncate hmn parent)).radius u z) by ring]
              exact abs_add_le _ _
        _ <= C * (parabolicDyadicSourceBox parent).radius ^ parabolicMorreyExponent d *
              parabolicMorreyDerivativeLpNorm d u +
            C * (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius ^
              parabolicMorreyExponent d *
              (∑ k ∈ Finset.range (n - m),
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) *
              parabolicMorreyDerivativeLpNorm d u := by
              exact add_le_add (by simpa only [hindex] using hstepNorm) hih
        _ = C * (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn parent)).radius ^
              parabolicMorreyExponent d *
              ((∑ k ∈ Finset.range (n - m),
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) +
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ (n - m)) *
              parabolicMorreyDerivativeLpNorm d u := by
              rw [← hparentRadius]
              ring

/-- A finite closed dyadic address tail is bounded by the geometric Morrey tail. -/
theorem exists_parabolicMorreyDyadicAddressPrefixProjectionClosedTailConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (a b : ParabolicDyadicAddress d) (u : TimeVelocity d -> Real),
        parabolicDyadicAddressPrefix a b ->
        ContDiff Real 2 u ->
        HasCompactSupport u ->
        ∀ z : TimeVelocity d,
          z ∈ parabolicClosedBox 1
              (parabolicDyadicSourceBox b.2).radius
              (parabolicDyadicSourceBox b.2).baseTime
              (parabolicDyadicSourceBox b.2).center ->
          |parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox b.2).baseTime
              (parabolicDyadicSourceBox b.2).center
              (parabolicDyadicSourceBox b.2).radius u z -
            parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox a.2).baseTime
              (parabolicDyadicSourceBox a.2).center
              (parabolicDyadicSourceBox a.2).radius u z| <=
            C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
              (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ *
              parabolicMorreyDerivativeLpNorm d u := by
  obtain ⟨C, hCpos, hfinite⟩ :=
    parabolicMorreyDyadicTruncateProjectionClosedFiniteTail d hd
  refine ⟨C, hCpos, ?_⟩
  intro a b u hab hu huc z hz
  rcases hab with ⟨hmn, htruncate⟩
  have hfinite' := hfinite a.1 b.1 hmn b.2 u hu huc z hz
  rw [htruncate] at hfinite'
  have halpha : 0 < parabolicMorreyExponent d := by
    unfold parabolicMorreyExponent
    have hd' : 0 < (d : Real) := by exact_mod_cast hd
    positivity
  have hqpos : 0 < (2 : Real) ^ (-parabolicMorreyExponent d) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hqlt : (2 : Real) ^ (-parabolicMorreyExponent d) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr halpha)
  have hqnonneg : 0 <= (2 : Real) ^ (-parabolicMorreyExponent d) := hqpos.le
  have hqsub : 0 < 1 - (2 : Real) ^ (-parabolicMorreyExponent d) :=
    sub_pos.mpr hqlt
  have hclear (N : Nat) :
      (∑ k ∈ Finset.range N, ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) *
        (1 - (2 : Real) ^ (-parabolicMorreyExponent d)) =
      1 - ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ N := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        calc
          ((∑ k ∈ Finset.range N,
              ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) +
              ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ N) *
              (1 - (2 : Real) ^ (-parabolicMorreyExponent d)) =
              (∑ k ∈ Finset.range N,
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) *
                (1 - (2 : Real) ^ (-parabolicMorreyExponent d)) +
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ N *
                  (1 - (2 : Real) ^ (-parabolicMorreyExponent d)) := by ring
          _ = (1 - ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ N) +
                ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ N *
                  (1 - (2 : Real) ^ (-parabolicMorreyExponent d)) := by rw [ih]
          _ = 1 - ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ (N + 1) := by
                rw [pow_succ]
                ring
  have hgeom : (∑ k ∈ Finset.range (b.1 - a.1),
      ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) <=
      (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hqsub).mpr
    rw [hclear]
    linarith [pow_nonneg hqnonneg (b.1 - a.1)]
  have hraw := parabolicMorreyDerivativeLpNorm_nonneg d u
  have hleft : 0 <= C * (parabolicDyadicSourceBox a.2).radius ^
      parabolicMorreyExponent d * parabolicMorreyDerivativeLpNorm d u := by
    exact mul_nonneg
      (mul_nonneg hCpos.le (Real.rpow_nonneg
        (parabolicDyadicSourceBox_radius_pos a.2).le _)) hraw
  calc
    _ <= C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
        (∑ k ∈ Finset.range (b.1 - a.1),
          ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) *
        parabolicMorreyDerivativeLpNorm d u := hfinite'
    _ = (C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
        parabolicMorreyDerivativeLpNorm d u) *
        (∑ k ∈ Finset.range (b.1 - a.1),
          ((2 : Real) ^ (-parabolicMorreyExponent d)) ^ k) := by ring
    _ <= (C * (parabolicDyadicSourceBox a.2).radius ^ parabolicMorreyExponent d *
        parabolicMorreyDerivativeLpNorm d u) *
        (1 - (2 : Real) ^ (-parabolicMorreyExponent d))⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom hleft
    _ = _ := by ring

end HypoellipticAleksandrov.Parabolic
