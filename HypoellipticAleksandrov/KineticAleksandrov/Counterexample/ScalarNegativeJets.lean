module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeAsymptotics
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarTailJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarEquations
public import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# Differentiated negative scalar tail

The complete exact M jet export is kept explicit until the Kummer lane lands it.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set Asymptotics
open scoped Topology ContDiff

/-- Two simultaneous sign changes preserve the second scalar derivative. -/
theorem scalar_deriv2_comp_neg (f : ℝ → ℝ) (s : ℝ) :
    deriv (deriv (fun t => f (-t))) s = deriv (deriv f) (-s) := by
  have he : deriv (fun t => f (-t)) = -(fun t => deriv f (-t)) := by
    funext t
    simp only [Pi.neg_apply, deriv_comp_neg]
  rw [he, deriv.neg, deriv_comp_neg, neg_neg]

/-- The actual first-truncation remainder in the negative-ray M formula. -/
def scalarMRemainder (a : ℝ) (b : Kummer.Pos) (z : ℝ) : ℝ :=
  Kummer.M a b (-z) - Kummer.mExpansion a b.1 1 z

/-- The first-truncation remainder is smooth on the positive argument ray. -/
theorem contDiffOn_scalarMRemainder (a : ℝ) (b : Kummer.Pos) :
    ContDiffOn ℝ 2 (scalarMRemainder a b) (Ioi 0) := by
  have hm : ContDiff ℝ 2 (fun z : ℝ => Kummer.M a b (-z)) :=
    (Kummer.analyticOnNhd_M a b).contDiff.comp contDiff_neg
  have he : scalarMRemainder a b = fun z => Kummer.M a b (-z) -
      (Real.Gamma b.1 / Real.Gamma (b.1 - a)) * Real.rpow z (-a) := by
    funext z
    unfold scalarMRemainder
    rw [mExpansion_one]
  rw [he]
  have hp : ContDiffOn ℝ 2 (fun z : ℝ => Real.rpow z (-a)) (Ioi 0) := by
    simp only [Real.rpow_eq_pow]
    exact contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)
  exact hm.contDiffOn.sub (contDiffOn_const.mul hp)

section MJet

variable (hmjet : ∀ (a : ℝ) (b : Kummer.Pos), -1 < a → a < b.1 →
  ∀ N j : ℕ, j ≤ 2 →
    IsBigO atTop (Kummer.jet j (fun X => Kummer.M a b (-X) - Kummer.mExpansion a b.1 N X))
      (fun X => Real.rpow X (-a - (N : ℝ) - (j : ℝ))))

include hmjet

/-- Cubic pullback bounds for all three actually differentiated M remainders. -/
theorem scalar_M_tail_derivatives_of_M_jets (a : ℝ) (b : Kummer.Pos)
    (ha : -1 < a) (hab : a < b.1) :
    IsBigO atTop (fun s => scalarMRemainder a b (scalarCubic 1 s))
      (fun s => Real.rpow s (-3 * a - 3)) ∧
    IsBigO atTop (deriv (fun s => scalarMRemainder a b (scalarCubic 1 s)))
      (fun s => Real.rpow s (-3 * a - 4)) ∧
    IsBigO atTop (deriv (deriv (fun s => scalarMRemainder a b (scalarCubic 1 s))))
      (fun s => Real.rpow s (-3 * a - 5)) := by
  have h0 : IsBigO atTop (scalarMRemainder a b) (fun z => Real.rpow z (-a - 1)) := by
    unfold scalarMRemainder
    simpa only [Kummer.jet, Function.iterate_zero_apply, Nat.cast_one,
      Nat.cast_zero, sub_zero] using hmjet a b ha hab 1 0 (by norm_num)
  have h1 : IsBigO atTop (deriv (scalarMRemainder a b))
      (fun z => Real.rpow z (-a - 1 - 1)) := by
    unfold scalarMRemainder
    simpa only [Kummer.jet, Function.iterate_one, Nat.cast_one] using
      hmjet a b ha hab 1 1 (by norm_num)
  have h2 : IsBigO atTop (deriv (deriv (scalarMRemainder a b)))
      (fun z => Real.rpow z (-a - 1 - 2)) := by
    unfold scalarMRemainder
    simpa only [Kummer.jet, Function.iterate_succ_apply, Function.iterate_zero_apply,
      Nat.cast_one, Nat.cast_ofNat] using hmjet a b ha hab 1 2 (by norm_num)
  have h := scalarCubic_remainder_derivatives (scalarMRemainder a b) (-a - 1) 1
    zero_lt_one (contDiffOn_scalarMRemainder a b) h1 h2
  have hb0 := isBigO_comp_scalar_tail (scalarMRemainder a b) (-a - 1) 9 (by norm_num) h0
  refine ⟨?_, ?_, ?_⟩
  · convert hb0 using 1
    · simp only [scalarCubic, mul_one]
    · funext s
      congr 1
      ring
  · convert h.1 using 1
    funext s
    congr 1
    ring
  · convert h.2 using 1
    funext s
    congr 1
    ring

/-- The signed second-M prefactor has the same differentiated scalar orders as the first. -/
theorem scalar_second_M_tail_derivatives_of_M_jets (gamma : ScalarGamma) :
    IsBigO atTop
      (deriv (fun s => s * scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop
      (deriv (deriv (fun s => s *
        scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
  have ha : -1 < 1 / 3 - gamma.1 := by linarith only [gamma.2.2]
  have hab : 1 / 3 - gamma.1 < Kummer.b43.1 := by
    dsimp only [Kummer.b43]
    linarith only [gamma.2.1]
  obtain ⟨h0, h1, h2⟩ := scalar_M_tail_derivatives_of_M_jets hmjet
    (1 / 3 - gamma.1) Kummer.b43 ha hab
  have hf : ContDiffOn ℝ 2
      (fun s => scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s))
      (Ioi 0) := by
    apply (contDiffOn_scalarMRemainder _ _).comp
      ((contDiff_scalarCubic 1).of_le (by norm_num)).contDiffOn
    intro s hs
    exact div_pos (pow_pos hs 3) (by norm_num)
  have he0 : -3 * (1 / 3 - gamma.1) - 3 = 3 * gamma.1 - 4 := by ring
  have he1 : -3 * (1 / 3 - gamma.1) - 4 = (3 * gamma.1 - 4) - 1 := by ring
  have he2 : -3 * (1 / 3 - gamma.1) - 5 = (3 * gamma.1 - 4) - 2 := by ring
  rw [he0] at h0
  rw [he1] at h1
  rw [he2] at h2
  have hb := scalar_linear_remainder_derivatives _ (3 * gamma.1 - 4) hf h0 h1 h2
  simpa only [show 3 * gamma.1 - 4 - 1 = 3 * gamma.1 - 5 by ring] using hb

/-- The two differentiated negative-ray scalar remainders, with the full source coefficient. -/
theorem Fminus_negative_ray_tail_derivatives_of_M_jets (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) :
    IsBigO atTop
      (deriv (fun s => Fminus gamma Lam (-s) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop
      (deriv (deriv (fun s => Fminus gamma Lam (-s) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow s (3 * gamma.1))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
  let f : ℝ → ℝ := fun s => scalarMRemainder (-gamma.1) Kummer.b23 (scalarCubic 1 s)
  let g : ℝ → ℝ := fun s => s *
    scalarMRemainder (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s)
  let c := gammaA gamma.1
  let d := -(gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3))
  have ha : -1 < -gamma.1 := by linarith only [gamma.2.2]
  have hab : -gamma.1 < Kummer.b23.1 := by
    dsimp only [Kummer.b23]
    linarith only [gamma.2.1]
  have hfirst := scalar_M_tail_derivatives_of_M_jets hmjet (-gamma.1) Kummer.b23 ha hab
  have hsecond := scalar_second_M_tail_derivatives_of_M_jets hmjet gamma
  have hf : ContDiffOn ℝ 2 f (Ioi 0) := by
    apply (contDiffOn_scalarMRemainder _ _).comp
      ((contDiff_scalarCubic 1).of_le (by norm_num)).contDiffOn
    intro s hs
    exact div_pos (pow_pos hs 3) (by norm_num)
  have hg : ContDiffOn ℝ 2 g (Ioi 0) := by
    apply contDiffOn_id.mul
    apply (contDiffOn_scalarMRemainder _ _).comp
      ((contDiff_scalarCubic 1).of_le (by norm_num)).contDiffOn
    intro s hs
    exact div_pos (pow_pos hs 3) (by norm_num)
  have hf1 : IsBigO atTop (deriv f) (fun s => Real.rpow s (3 * gamma.1 - 4)) := by
    simpa only [f, show -3 * -gamma.1 - 4 = 3 * gamma.1 - 4 by ring] using hfirst.2.1
  have hf2 : IsBigO atTop (deriv (deriv f)) (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
    simpa only [f, show -3 * -gamma.1 - 5 = 3 * gamma.1 - 5 by ring] using hfirst.2.2
  have hg1 : IsBigO atTop (deriv g) (fun s => Real.rpow s (3 * gamma.1 - 4)) := hsecond.1
  have hg2 : IsBigO atTop (deriv (deriv g)) (fun s => Real.rpow s (3 * gamma.1 - 5)) := hsecond.2
  have hloc (s : ℝ) (hs : 0 < s) : (fun t => c * f t + d * g t) =ᶠ[𝓝 s]
      fun t => Fminus gamma Lam (-t) - Real.rpow 9 (-gamma.1) *
        (Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3))) *
          Real.rpow t (3 * gamma.1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    rw [← scalar_negative_leading gamma Lam t hLam ht]
    dsimp only [f, g, c, d, scalarMRemainder, scalarCubic, Fminus]
    simp only [mul_one, Kummer.b23, Kummer.b43]
    rw [show (-t) ^ 3 / 9 = -(t ^ 3 / 9) by ring]
    ring
  constructor
  · apply ((hf1.const_mul_left c).add (hg1.const_mul_left d)).congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [← (scalar_linear_combination_derivatives f g c d s hf hg hs).1]
    exact (hloc s hs).deriv_eq
  · apply ((hf2.const_mul_left c).add (hg2.const_mul_left d)).congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [← (scalar_linear_combination_derivatives f g c d s hf hg hs).2]
    exact (hloc s hs).deriv.deriv_eq

end MJet

/-- The source differentiated negative tail, using the internally proved Kummer jet exports. -/
theorem Fminus_tail_derivatives (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    IsBigO atBot
      (deriv (fun s => Fminus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow |s| (3 * gamma.1)))
      (fun s => Real.rpow |s| (3 * gamma.1 - 4)) ∧
    IsBigO atBot
      (deriv (deriv (fun s => Fminus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow |s| (3 * gamma.1))))
      (fun s => Real.rpow |s| (3 * gamma.1 - 5)) := by
  have hb := Fminus_negative_ray_tail_derivatives_of_M_jets
    Kummer.M_negative_expansion_jet gamma Lam hLam
  rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hb
  let R : ℝ → ℝ := fun s => Fminus gamma Lam s -
    Real.rpow (9 * Lam) (-gamma.1) * Real.rpow |s| (3 * gamma.1)
  have he (s : ℝ) (hs : 0 < s) :
      (fun t => Fminus gamma Lam (-t) - Real.rpow (9 * Lam) (-gamma.1) *
        Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s] fun t => R (-t) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp only [R, abs_neg, abs_of_pos ht]
  constructor
  · have h := hb.1.neg_left.comp_tendsto tendsto_neg_atBot_atTop
    apply h.congr' _ _
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      simp only [Function.comp_def]
      rw [(he (-s) (neg_pos.mpr hs)).deriv_eq, deriv_comp_neg, neg_neg, neg_neg]
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      simp only [Function.comp_def, abs_of_neg hs]
  · have h := hb.2.comp_tendsto tendsto_neg_atBot_atTop
    apply h.congr' _ _
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      simp only [Function.comp_def]
      rw [(he (-s) (neg_pos.mpr hs)).deriv.deriv_eq, scalar_deriv2_comp_neg, neg_neg]
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      simp only [Function.comp_def, abs_of_neg hs]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
