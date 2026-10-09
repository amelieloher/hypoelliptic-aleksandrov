module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Propagation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationScaling
import Mathlib.Tactic

/-! # Propagation with a constant chosen before the dimensional time scale -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The propagation constant depends only on the source dimensionless parameters. -/
theorem propagation_dimensionless
    (d : ℕ) (hd : 1 ≤ d) (lam Lam a0 b0 cx cv : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (ha0 : 0 < a0) (ha01 : a0 ≤ 1)
    (hb0 : 0 < b0) (hcx : 0 < cx) (hcv : 0 < cv) :
  ∃ cprop : ℝ, 0 < cprop ∧ cprop ≤ 1 ∧
    ∀ T1 : ℝ, 0 < T1 →
    ∀ (p C_A : ℝ), 1 ≤ p →
    ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
    ∀ O : Set (KineticPoint d), IsOpen O →
    ∀ (tminus : ℝ) (P : KineticPoint d), P ∈ O →
      a0*T1 ≤ P.time-tminus → P.time-tminus ≤ T1 →
    ∀ x v : ℝ → PDE.Vec d,
      IsSkeleton x v (b0/Real.sqrt T1) (-a0*T1) (P.time-tminus) →
      x (P.time-tminus) = P.position → v (P.time-tminus) = P.velocity →
      corridor tminus (-a0*T1) (P.time-tminus)
        (cx*T1^(3/2 : ℝ)) (cv*Real.sqrt T1) x v ⊆ O →
    ∀ ell : ℝ, 0 ≤ ell →
    ∀ u : KineticPoint d → ℝ,
      (∀ Q ∈ O, 0 ≤ u Q) → IsAdmissibleSupersolution A O p C_A u →
      (∀ Q ∈ corridor tminus (-a0*T1) (P.time-tminus)
          (cx*T1^(3/2 : ℝ)) (cv*Real.sqrt T1) x v,
        Q.time ≤ tminus → ell ≤ u Q) → cprop*ell ≤ u P := by
  let L := barrierL d lam Lam b0 1
  let hs := stepSize d lam Lam b0 a0 1 cx cv
  have hL : 0 < L := barrierL_pos hd hlam hLam (by norm_num)
  have hg := barrierGamma_bounds hL
  refine ⟨(barrierGamma L) ^ Nat.ceil (1 / hs), pow_pos hg.1 _,
    pow_le_one₀ hg.1.le hg.2.le, ?_⟩
  intro T1 hT1 p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v hsk hxP hvP htube
    ell hell u hnonneg hu hinitial
  have hsqrt : 0 < Real.sqrt T1 := Real.sqrt_pos.mpr hT1
  have hkx : 0 < cx * T1 ^ (3 / 2 : ℝ) :=
    mul_pos hcx (Real.rpow_pos_of_pos hT1 _)
  have hkv : 0 < cv * Real.sqrt T1 := mul_pos hcv hsqrt
  have hH : 0 < b0 / Real.sqrt T1 := div_pos hb0 hsqrt
  have hT0 : 0 < a0 * T1 := mul_pos ha0 hT1
  have hT01 : a0 * T1 ≤ T1 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha01 hT1.le
  have hbarrier := (propagation_barrier_scaling d lam Lam b0 hT1).1
  have hstep := propagation_step_scaling d lam Lam a0 b0 cx cv hb0.le hcx.le hT1
  have hratio : T1 / (T1 * hs) = 1 / hs := by
    field_simp
  have hconstant :
      (barrierGamma (barrierL d lam Lam (b0 / Real.sqrt T1) T1)) ^
        Nat.ceil (T1 / stepSize d lam Lam (b0 / Real.sqrt T1) (a0 * T1) T1
          (cx * T1 ^ (3 / 2 : ℝ)) (cv * Real.sqrt T1)) =
      (barrierGamma L) ^ Nat.ceil (1 / hs) := by
    rw [hbarrier, hstep, hratio]
  have hresult := propagation_explicit d hd lam Lam (b0 / Real.sqrt T1) (a0 * T1) T1
    (cx * T1 ^ (3 / 2 : ℝ)) (cv * Real.sqrt T1) hlam hLam hH hkx hkv hT0 hT01
    p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v
    (by simpa only [neg_mul] using hsk) hxP hvP
    (by simpa only [neg_mul] using htube) ell hell u hnonneg hu
    (by simpa only [neg_mul] using hinitial)
  rw [hconstant] at hresult
  exact hresult

end HypoellipticAleksandrov.KineticAleksandrov.Holder
