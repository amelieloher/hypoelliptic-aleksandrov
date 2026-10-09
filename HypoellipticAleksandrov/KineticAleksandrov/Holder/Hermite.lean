module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Cubic Hermite paths and their Euclidean acceleration estimate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source's literal cubic Hermite position polynomial. -/
def hermitePosition {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) (s : ℝ) : PDE.Vec d :=
  let z := s / T
  (2 * z ^ 3 - 3 * z ^ 2 + 1) • x0 + ((z ^ 3 - 2 * z ^ 2 + z) * T) • v0 +
    (-2 * z ^ 3 + 3 * z ^ 2) • x1 + ((z ^ 3 - z ^ 2) * T) • v1

/-- Velocity in displacement-difference coordinates. -/
def hermiteVelocity {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) (s : ℝ) : PDE.Vec d :=
  let z := s / T
  v0 + ((6 * z - 6 * z ^ 2) / T) • (x1 - x0 - T • v0) +
    (3 * z ^ 2 - 2 * z) • (v1 - v0)

/-- Acceleration in displacement-difference coordinates. -/
def hermiteAcceleration {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) (s : ℝ) :
    PDE.Vec d :=
  let z := s / T
  ((6 - 12 * z) / T ^ 2) • (x1 - x0 - T • v0) +
    ((6 * z - 2) / T) • (v1 - v0)

/-- Equivalent displacement representation of the literal polynomial. -/
theorem hermitePosition_eq {d : ℕ} {T : ℝ} (hT : T ≠ 0)
    (x0 v0 x1 v1 : PDE.Vec d) (s : ℝ) :
    hermitePosition T x0 v0 x1 v1 s =
      x0 + s • v0 + (3 * (s / T) ^ 2 - 2 * (s / T) ^ 3) •
        (x1 - x0 - T • v0) + (T * ((s / T) ^ 3 - (s / T) ^ 2)) • (v1 - v0) := by
  ext i
  simp only [hermitePosition, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hT]
  ring

/-- Position takes the prescribed initial endpoint. -/
theorem hermitePosition_zero {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) :
    hermitePosition T x0 v0 x1 v1 0 = x0 := by
  simp [hermitePosition]

/-- Position takes the prescribed terminal endpoint. -/
theorem hermitePosition_end {d : ℕ} {T : ℝ} (hT : T ≠ 0)
    (x0 v0 x1 v1 : PDE.Vec d) : hermitePosition T x0 v0 x1 v1 T = x1 := by
  norm_num [hermitePosition, hT]

/-- Velocity takes the prescribed initial endpoint. -/
theorem hermiteVelocity_zero {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) :
    hermiteVelocity T x0 v0 x1 v1 0 = v0 := by
  simp [hermiteVelocity]

/-- Velocity takes the prescribed terminal endpoint. -/
theorem hermiteVelocity_end {d : ℕ} {T : ℝ} (hT : T ≠ 0)
    (x0 v0 x1 v1 : PDE.Vec d) : hermiteVelocity T x0 v0 x1 v1 T = v1 := by
  norm_num [hermiteVelocity, hT]

/-- The Hermite position polynomial is smooth. -/
theorem contDiff_hermitePosition {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (hermitePosition T x0 v0 x1 v1) := by
  unfold hermitePosition
  fun_prop

/-- The Hermite velocity polynomial is smooth. -/
theorem contDiff_hermiteVelocity {d : ℕ} (T : ℝ) (x0 v0 x1 v1 : PDE.Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (hermiteVelocity T x0 v0 x1 v1) := by
  unfold hermiteVelocity
  fun_prop

/-- The Hermite velocity is the derivative of position. -/
theorem hasDerivAt_hermitePosition {d : ℕ} {T : ℝ} (hT : T ≠ 0)
    (x0 v0 x1 v1 : PDE.Vec d) (s : ℝ) :
    HasDerivAt (hermitePosition T x0 v0 x1 v1)
      (hermiteVelocity T x0 v0 x1 v1 s) s := by
  have hz := (hasDerivAt_id s).div_const T
  have hpoly := ((hasDerivAt_const s x0).add ((hasDerivAt_id s).smul_const v0)).add
    ((((hz.pow 2).const_mul 3).sub ((hz.pow 3).const_mul 2)).smul_const
      (x1 - x0 - T • v0))
  have hp := hpoly.add ((((hz.pow 3).sub (hz.pow 2)).const_mul T).smul_const (v1 - v0))
  convert hp using 1
  · funext t
    exact hermitePosition_eq hT x0 v0 x1 v1 t
  · ext i
    simp only [hermiteVelocity, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hT]
    ring

/-- The displayed acceleration is the derivative of Hermite velocity. -/
theorem hasDerivAt_hermiteVelocity {d : ℕ} {T : ℝ} (hT : T ≠ 0)
    (x0 v0 x1 v1 : PDE.Vec d) (s : ℝ) :
    HasDerivAt (hermiteVelocity T x0 v0 x1 v1)
      (hermiteAcceleration T x0 v0 x1 v1 s) s := by
  have hz := (hasDerivAt_id s).div_const T
  have hp := ((hasDerivAt_const s v0).add
    ((((hz.const_mul 6).sub ((hz.pow 2).const_mul 6)).div_const T).smul_const
      (x1 - x0 - T • v0))).add
    ((((hz.pow 2).const_mul 3).sub (hz.const_mul 2)).smul_const (v1 - v0))
  convert hp using 1
  · funext t
    rfl
  · ext i
    simp only [hermiteAcceleration, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hT]
    ring

/-- Source acceleration bound, with Euclidean norms and no dimension-dependent loss. -/
theorem hermiteAcceleration_bound {d : ℕ} {T : ℝ} (hT : 0 < T)
    (x0 v0 x1 v1 : PDE.Vec d) {s : ℝ} (hs : s ∈ Icc 0 T) :
    PDE.vecEuclideanNorm (hermiteAcceleration T x0 v0 x1 v1 s) ≤
      6 * PDE.vecEuclideanNorm (x1 - x0 - T • v0) / T ^ 2 +
      4 * PDE.vecEuclideanNorm (v1 - v0) / T := by
  have hz0 : 0 ≤ s / T := div_nonneg hs.1 hT.le
  have hz1 : s / T ≤ 1 := (div_le_one hT).mpr hs.2
  have h6 : |6 - 12 * (s / T)| ≤ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h4 : |6 * (s / T) - 2| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  unfold hermiteAcceleration
  refine (PDE.vecEuclideanNorm_add_le _ _).trans ?_
  rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul, abs_div, abs_div,
    abs_of_pos (sq_pos_of_pos hT), abs_of_pos hT]
  have hx := PDE.vecEuclideanNorm_nonneg (x1 - x0 - T • v0)
  have hv := PDE.vecEuclideanNorm_nonneg (v1 - v0)
  calc
    _ ≤ (6 / T ^ 2) * PDE.vecEuclideanNorm (x1 - x0 - T • v0) +
        (4 / T) * PDE.vecEuclideanNorm (v1 - v0) :=
      add_le_add (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h6 (sq_nonneg T)) hx)
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h4 hT.le) hv)
    _ = _ := by ring

/-- A continuous derivative bounded in Euclidean norm bounds increments with the same constant. -/
theorem euclidean_lipschitz_of_derivative {d : ℕ} {v acc : ℝ → PDE.Vec d}
    {a b H : ℝ} (ha : Continuous acc)
    (hder : ∀ s, HasDerivAt v (acc s) s)
    (hbound : ∀ s ∈ Icc a b, PDE.vecEuclideanNorm (acc s) ≤ H) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t| := by
  have hkey : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      PDE.vecEuclideanNorm (v t - v s) ≤ H * |t - s| := by
    intro s hs t ht hst
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hder u) (ha.intervalIntegrable s t)]
    apply vecEuclideanNorm_intervalIntegral_le (ha.intervalIntegrable s t)
    intro u hu
    rw [uIoc_of_le hst] at hu
    exact hbound u ⟨hs.1.trans hu.1.le, hu.2.trans ht.2⟩
  intro s hs t ht
  rcases le_total t s with hts | hst
  · exact hkey t ht s hs hts
  · rw [PDE.vecEuclideanNorm_sub_comm, abs_sub_comm]
    exact hkey s hs t ht hst

/-- The cubic Hermite path is an admissible skeleton with the source acceleration constant. -/
theorem hermite_isSkeleton {d : ℕ} {T : ℝ} (hT : 0 < T)
    (x0 v0 x1 v1 : PDE.Vec d) :
    IsSkeleton (hermitePosition T x0 v0 x1 v1)
      (hermiteVelocity T x0 v0 x1 v1)
      (6 * PDE.vecEuclideanNorm (x1 - x0 - T • v0) / T ^ 2 +
        4 * PDE.vecEuclideanNorm (v1 - v0) / T) 0 T := by
  have hv := (contDiff_hermiteVelocity T x0 v0 x1 v1).continuous
  refine ⟨hv.continuousOn, fun s _ =>
    (hasDerivAt_hermitePosition hT.ne' x0 v0 x1 v1 s).hasDerivWithinAt, ?_⟩
  apply euclidean_lipschitz_of_derivative
    (show Continuous (hermiteAcceleration T x0 v0 x1 v1) by
      unfold hermiteAcceleration
      fun_prop)
    (hasDerivAt_hermiteVelocity hT.ne' x0 v0 x1 v1)
  exact fun s hs => hermiteAcceleration_bound hT x0 v0 x1 v1 hs

end HypoellipticAleksandrov.KineticAleksandrov.Holder
