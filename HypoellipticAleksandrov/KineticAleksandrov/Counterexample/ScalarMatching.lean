module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarEquations
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarGluing
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Connection
import Mathlib.Tactic

/-!
# Local scalar matching

The positive-side analytic expression follows conditionally from the complete planned
Kummer connection theorem. The conditional theorem is a consumer, not a connection proof.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter
open scoped Topology ContDiff

/-- The entire local expression at diffusivity a, with the source linear normalization. -/
def scalarLocal (gamma : ScalarGamma) (Lam a s : ℝ) : ℝ :=
  gammaA gamma.1 * Kummer.M (-gamma.1) Kummer.b23 (scalarCubic a s) +
    gammaB gamma.1 * s / Real.rpow (9 * Lam) (1 / 3) *
      Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic a s)

/-- The literal local expression at diffusivity one is the negative piece. -/
theorem scalarLocal_one (gamma : ScalarGamma) (Lam : ℝ) :
    scalarLocal gamma Lam 1 = Fminus gamma Lam := by
  funext s
  simp only [scalarLocal, scalarCubic, mul_one, Fminus]

/-- Smoothness of the entire local expression. -/
theorem contDiff_scalarLocal (gamma : ScalarGamma) (Lam a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarLocal gamma Lam a) := by
  have hm (u : ℝ) (b : Kummer.Pos) : ContDiff ℝ (⊤ : ℕ∞) (Kummer.M u b) :=
    (Kummer.analyticOnNhd_M u b).contDiff
  exact (contDiff_const.mul ((hm _ _).comp (contDiff_scalarCubic a))).add
    (((contDiff_const.mul contDiff_id).div_const _).mul
      ((hm _ _).comp (contDiff_scalarCubic a)))

/-- The local expression has the source value at zero for every diffusivity. -/
@[simp] theorem scalarLocal_zero (gamma : ScalarGamma) (Lam a : ℝ) :
    scalarLocal gamma Lam a 0 = gammaA gamma.1 := by
  simp only [scalarLocal, scalarCubic, zero_pow (by decide : 3 ≠ 0), zero_div,
    Kummer.M_zero, mul_one, mul_zero, add_zero]

/-- Its first derivative at zero is independent of the branch diffusivity. -/
theorem scalarLocal_hasDerivAt_zero (gamma : ScalarGamma) (Lam a : ℝ) :
    HasDerivAt (scalarLocal gamma Lam a)
      (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) 0 := by
  have hc : scalarCubic a 0 = 0 := by simp [scalarCubic]
  have hd (u : ℝ) (b : Kummer.Pos) : HasDerivAt
      (fun s => Kummer.M u b (scalarCubic a s)) 0 0 := by
    simpa only [Function.comp_def, hc, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero] using
      (Kummer.hasDerivAt_M u b (scalarCubic a 0)).comp 0 (hasDerivAt_scalarCubic a 0)
  have h := ((hd (-gamma.1) Kummer.b23).const_mul (gammaA gamma.1)).add
    ((((hasDerivAt_id (0 : ℝ)).const_mul (gammaB gamma.1)).div_const
      (Real.rpow (9 * Lam) (1 / 3))).mul (hd (1 / 3 - gamma.1) Kummer.b43))
  unfold scalarLocal
  simpa only [Pi.add_def, Pi.mul_def, id_eq, scalarCubic,
    zero_pow (by decide : 3 ≠ 0), zero_div, Kummer.M_zero, mul_zero, zero_mul,
    add_zero, zero_add, mul_one] using h

/-- The local expression solves the scalar equation at all real s. -/
theorem scalarLocal_ode (gamma : ScalarGamma) (Lam a s : ℝ) (ha : a ≠ 0) :
    a * deriv (deriv (scalarLocal gamma Lam a)) s -
      s ^ 2 / 3 * deriv (scalarLocal gamma Lam a) s +
        gamma.1 * s * scalarLocal gamma Lam a s = 0 := by
  let f : ℝ → ℝ := fun t => Kummer.M (-gamma.1) Kummer.b23 (scalarCubic a t)
  let g : ℝ → ℝ := fun t => t *
    Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic a t)
  have hm (u : ℝ) (b : Kummer.Pos) : ContDiff ℝ 2 (Kummer.M u b) :=
    (Kummer.analyticOnNhd_M u b).contDiff
  have hc : ContDiff ℝ 2 (scalarCubic a) := (contDiff_scalarCubic a).of_le (by norm_num)
  have hf : ContDiff ℝ 2 f := (hm _ _).comp hc
  have hg : ContDiff ℝ 2 g := contDiff_id.mul ((hm _ _).comp hc)
  have hfo := scalarCubic_ode (Kummer.M (-gamma.1) Kummer.b23) gamma.1 a s ha
    (hm _ _).contDiffAt
    (by simpa only [Kummer.b23, neg_mul, sub_neg_eq_add] using
      Kummer.M_ode (-gamma.1) Kummer.b23 (scalarCubic a s))
  have hgo := scalarCubic_second_ode (Kummer.M (1 / 3 - gamma.1) Kummer.b43)
    gamma.1 a s ha (hm _ _)
    (by simpa only [Kummer.b43] using
      Kummer.M_ode (1 / 3 - gamma.1) Kummer.b43 (scalarCubic a s))
  have he : scalarLocal gamma Lam a = fun t => gammaA gamma.1 * f t +
      (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) * g t := by
    funext t
    dsimp only [scalarLocal, f, g]
    ring
  rw [he]
  exact scalar_ode_linear_combination f g gamma.1 a (gammaA gamma.1)
    (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) s hf hg hfo hgo

/-- Both local second derivatives vanish at zero by their actual differential equation. -/
theorem scalarLocal_deriv2_zero (gamma : ScalarGamma) (Lam a : ℝ) (ha : a ≠ 0) :
    deriv (deriv (scalarLocal gamma Lam a)) 0 = 0 := by
  have ho := scalarLocal_ode gamma Lam a 0 ha
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, mul_zero, sub_zero,
    add_zero] at ho
  exact (mul_eq_zero.mp ho).resolve_left ha

/-- Exact positive-side connection consumer, pending the Kummer lane's connection proof. -/
theorem Fplus_eq_scalarLocal_of_connection
    (hconnection : ∀ a : Kummer.NegThird, ∀ z : ℝ, 0 < z →
      Kummer.UNr a z = Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) *
        Kummer.M a.1 Kummer.b23 z +
      Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
        Kummer.M (a.1 + 1 / 3) Kummer.b43 z)
    (gamma : ScalarGamma) (Lam s : ℝ) (hLam : 0 < Lam) (hs : 0 < s) :
    Fplus gamma Lam s = scalarLocal gamma Lam Lam s := by
  have hd : 0 < 9 * Lam := mul_pos (by norm_num) hLam
  have hp : (s ^ 3 / (9 * Lam)) ^ (1 / 3 : ℝ) = s / (9 * Lam) ^ (1 / 3 : ℝ) := by
    rw [Real.div_rpow (pow_nonneg hs.le _) hd.le,
      ← Real.rpow_natCast s 3, ← Real.rpow_mul hs.le]
    norm_num
  rw [Fplus, hconnection gamma.negative _ (div_pos (pow_pos hs _) hd)]
  dsimp only [ScalarGamma.negative, scalarLocal, scalarCubic, gammaA, gammaB]
  simp only [Real.rpow_eq_pow, hp]
  rw [show -gamma.1 + 1 / 3 = 1 / 3 - gamma.1 by ring]
  ring

section Connection

variable (hconnection : ∀ a : Kummer.NegThird, ∀ z : ℝ, 0 < z →
  Kummer.UNr a z = Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) *
    Kummer.M a.1 Kummer.b23 z +
  Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
    Kummer.M (a.1 + 1 / 3) Kummer.b43 z)

include hconnection

/-- The source piecewise profile is the join of its two entire local expressions. -/
theorem F_eq_scalarJoin_of_connection (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    F gamma Lam = scalarJoin (scalarLocal gamma Lam Lam) (scalarLocal gamma Lam 1) := by
  funext s
  unfold F scalarJoin
  by_cases hs : 0 < s
  · simp only [hs, ↓reduceIte]
    exact Fplus_eq_scalarLocal_of_connection hconnection gamma Lam s hLam hs
  · simp only [hs, ↓reduceIte]
    rw [scalarLocal_one]
    by_cases hs0 : s < 0
    · simp only [hs0, ↓reduceIte]
    · have hz : s = 0 := le_antisymm (le_of_not_gt hs) (le_of_not_gt hs0)
      simp only [hz, lt_self_iff_false, ↓reduceIte, Fminus_zero]

/-- Exact C² matching at the scalar join, conditional only on the complete connection export. -/
theorem F_contDiff_two_of_connection (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    ContDiff ℝ 2 (F gamma Lam) := by
  rw [F_eq_scalarJoin_of_connection hconnection gamma Lam hLam]
  apply contDiff_two_scalarJoin
  · exact (contDiff_scalarLocal gamma Lam Lam).of_le (by norm_num)
  · exact (contDiff_scalarLocal gamma Lam 1).of_le (by norm_num)
  · rw [scalarLocal_zero, scalarLocal_zero]
  · rw [(scalarLocal_hasDerivAt_zero gamma Lam Lam).deriv,
      (scalarLocal_hasDerivAt_zero gamma Lam 1).deriv]
  · rw [scalarLocal_deriv2_zero gamma Lam Lam hLam.ne',
      scalarLocal_deriv2_zero gamma Lam 1 one_ne_zero]

/-- The joined value and first two derivatives have precisely the source normalization. -/
theorem F_zero_jets_of_connection (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    F gamma Lam 0 = gammaA gamma.1 ∧
    deriv (F gamma Lam) 0 = gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3) ∧
    deriv (deriv (F gamma Lam)) 0 = 0 := by
  refine ⟨F_zero gamma Lam, ?_⟩
  have hf : Differentiable ℝ (scalarLocal gamma Lam Lam) :=
    (contDiff_scalarLocal gamma Lam Lam).differentiable (by norm_num)
  have hg : Differentiable ℝ (scalarLocal gamma Lam 1) :=
    (contDiff_scalarLocal gamma Lam 1).differentiable (by norm_num)
  have hfg : scalarLocal gamma Lam Lam 0 = scalarLocal gamma Lam 1 0 := by simp
  have hdfg : deriv (scalarLocal gamma Lam Lam) 0 =
      deriv (scalarLocal gamma Lam 1) 0 := by
    rw [(scalarLocal_hasDerivAt_zero gamma Lam Lam).deriv,
      (scalarLocal_hasDerivAt_zero gamma Lam 1).deriv]
  have hfdd := ((contDiff_scalarLocal gamma Lam Lam).of_le
    (by norm_num : (2 : ℕ∞ω) ≤ ∞)).differentiable_deriv_two
  have hgdd := ((contDiff_scalarLocal gamma Lam 1).of_le
    (by norm_num : (2 : ℕ∞ω) ≤ ∞)).differentiable_deriv_two
  have hddfg : deriv (deriv (scalarLocal gamma Lam Lam)) 0 =
      deriv (deriv (scalarLocal gamma Lam 1)) 0 := by
    rw [scalarLocal_deriv2_zero gamma Lam Lam hLam.ne',
      scalarLocal_deriv2_zero gamma Lam 1 one_ne_zero]
  rw [F_eq_scalarJoin_of_connection hconnection gamma Lam hLam,
    scalarJoin_deriv _ _ hf hg hfg hdfg]
  constructor
  · simp only [scalarJoin, lt_self_iff_false, ↓reduceIte]
    exact (scalarLocal_hasDerivAt_zero gamma Lam 1).deriv
  · rw [scalarJoin_deriv _ _ hfdd hgdd hdfg hddfg]
    simp only [scalarJoin, lt_self_iff_false, ↓reduceIte]
    exact scalarLocal_deriv2_zero gamma Lam 1 one_ne_zero

/-- The glued profile solves the scalar equation, including its regular joining point. -/
theorem F_ode_of_connection (gamma : ScalarGamma) (Lam s : ℝ) (hLam : 0 < Lam) :
    (if 0 < s then Lam else 1) * deriv (deriv (F gamma Lam)) s -
      s ^ 2 / 3 * deriv (F gamma Lam) s + gamma.1 * s * F gamma Lam s = 0 := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have he : F gamma Lam =ᶠ[𝓝 s] Fminus gamma Lam := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      simp only [F, not_lt.mpr ht.le, show t < 0 from ht, ↓reduceIte]
    rw [ite_eq_right (not_lt.mpr hs.le), he.deriv.deriv_eq, he.deriv_eq,
      he.eq_of_nhds, one_mul]
    exact Fminus_ode gamma Lam s
  · subst s
    simp only [lt_self_iff_false, ↓reduceIte,
      (F_zero_jets_of_connection hconnection gamma Lam hLam).2.2,
      zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, mul_zero, sub_zero, add_zero]
  · have he : F gamma Lam =ᶠ[𝓝 s] Fplus gamma Lam := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      simp only [F, show 0 < t from ht, ↓reduceIte]
    rw [ite_eq_left hs, he.deriv.deriv_eq, he.deriv_eq, he.eq_of_nhds]
    exact Fplus_ode gamma Lam s hLam hs

end Connection

/-- The two source branches match with global C² regularity. -/
theorem F_contDiff_two (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    ContDiff ℝ 2 (F gamma Lam) :=
  F_contDiff_two_of_connection Kummer.UNr_connection gamma Lam hLam

/-- The source value and first two derivatives at s=0, with no pending connection premise. -/
theorem F_zero_jets (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    F gamma Lam 0 = gammaA gamma.1 ∧
    deriv (F gamma Lam) 0 = gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3) ∧
    deriv (deriv (F gamma Lam)) 0 = 0 :=
  F_zero_jets_of_connection Kummer.UNr_connection gamma Lam hLam

/-- The actual joined solution satisfies the piecewise scalar ODE everywhere. -/
theorem F_ode (gamma : ScalarGamma) (Lam s : ℝ) (hLam : 0 < Lam) :
    (if 0 < s then Lam else 1) * deriv (deriv (F gamma Lam)) s -
      s ^ 2 / 3 * deriv (F gamma Lam) s + gamma.1 * s * F gamma Lam s = 0 :=
  F_ode_of_connection Kummer.UNr_connection gamma Lam s hLam

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
