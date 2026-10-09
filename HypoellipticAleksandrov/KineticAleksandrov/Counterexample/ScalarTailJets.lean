module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAsymptotics
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarReduction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsJets
import Mathlib.Tactic

/-!
# Cubic pullback of differentiated remainders

The derivative estimates below consume bounds for the actual derivatives. No
undifferentiated Big-O assertion is differentiated.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set Asymptotics
open scoped Topology ContDiff

/-- Exact first and second derivatives of a constant linear combination on the positive ray. -/
theorem scalar_linear_combination_derivatives (f g : ℝ → ℝ) (c d s : ℝ)
    (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hg : ContDiffOn ℝ 2 g (Ioi 0)) (hs : 0 < s) :
    deriv (fun t => c * f t + d * g t) s = c * deriv f s + d * deriv g s ∧
    deriv (deriv (fun t => c * f t + d * g t)) s =
      c * deriv (deriv f) s + d * deriv (deriv g) s := by
  have he (t : ℝ) (ht : 0 < t) : HasDerivAt (fun w => c * f w + d * g w)
      (c * deriv f t + d * deriv g t) t := by
    have hdf := (hf.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by norm_num)
    have hdg := (hg.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by norm_num)
    simpa only [Pi.add_def] using (hdf.hasDerivAt.const_mul c).add
      (hdg.hasDerivAt.const_mul d)
  refine ⟨(he s hs).deriv, ?_⟩
  have heq : deriv (fun t => c * f t + d * g t) =ᶠ[𝓝 s]
      fun t => c * deriv f t + d * deriv g t := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (he t ht).deriv
  have hdf := ((hf.contDiffAt (isOpen_Ioi.mem_nhds hs)).derivWithin
    (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hdg := ((hg.contDiffAt (isOpen_Ioi.mem_nhds hs)).derivWithin
    (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hd := (hdf.hasDerivAt.const_mul c).add (hdg.hasDerivAt.const_mul d)
  simp only [Pi.add_def] at hd
  exact (hd.congr_of_eventuallyEq heq).deriv

/-- Differentiating a signed linear prefactor preserves the predicted remainder orders. -/
theorem scalar_linear_remainder_derivatives (f : ℝ → ℝ) (p : ℝ)
    (hf : ContDiffOn ℝ 2 f (Ioi 0))
    (h0 : IsBigO atTop f (fun s => Real.rpow s p))
    (h1 : IsBigO atTop (deriv f) (fun s => Real.rpow s (p - 1)))
    (h2 : IsBigO atTop (deriv (deriv f)) (fun s => Real.rpow s (p - 2))) :
    IsBigO atTop (deriv (fun s => s * f s)) (fun s => Real.rpow s p) ∧
    IsBigO atTop (deriv (deriv (fun s => s * f s)))
      (fun s => Real.rpow s (p - 1)) := by
  have hb1 := Kummer.rpow_mul_isBigO_of_add_eq (deriv f) 1 (p - 1) p
    (by simpa only [Real.rpow_eq_pow] using h1) (by ring)
  have hb2 := Kummer.rpow_mul_isBigO_of_add_eq (deriv (deriv f)) 1 (p - 2) (p - 1)
    (by simpa only [Real.rpow_eq_pow] using h2) (by ring)
  have he (s : ℝ) (hs : 0 < s) : deriv (fun t => t * f t) s = f s + s * deriv f s := by
    have hd := (hf.contDiffAt (isOpen_Ioi.mem_nhds hs)).differentiableAt (by norm_num)
    simpa only [Pi.mul_def, id_eq, one_mul] using ((hasDerivAt_id s).mul hd.hasDerivAt).deriv
  constructor
  · have hb0 : IsBigO atTop f (fun s => s ^ p) := by
      simpa only [Real.rpow_eq_pow] using h0
    apply (hb0.add hb1).congr' _ (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [he s hs]
    simp only [Real.rpow_one]
  · have hb1' : IsBigO atTop (deriv f) (fun s => s ^ (p - 1)) := by
      simpa only [Real.rpow_eq_pow] using h1
    apply ((hb1'.const_mul_left 2).add hb2).congr' _
      (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hc := hf.contDiffAt (isOpen_Ioi.mem_nhds hs)
    have hd := hc.differentiableAt (by norm_num)
    have hd' := (hc.derivWithin (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have heq : deriv (fun t => t * f t) =ᶠ[𝓝 s] fun t => f t + t * deriv f t := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact he t ht
    have hder := hd.hasDerivAt.add ((hasDerivAt_id s).mul hd'.hasDerivAt)
    simp only [Pi.add_def, Pi.mul_def, id_eq, one_mul] at hder
    rw [(hder.congr_of_eventuallyEq heq).deriv]
    simp only [Real.rpow_one]
    ring

/-- First and second derivative remainder estimates after the cubic substitution. -/
theorem scalarCubic_remainder_derivatives (f : ℝ → ℝ) (p a : ℝ) (ha : 0 < a)
    (hf : ContDiffOn ℝ 2 f (Ioi 0))
    (h1 : IsBigO atTop (deriv f) (fun z => Real.rpow z (p - 1)))
    (h2 : IsBigO atTop (deriv (deriv f)) (fun z => Real.rpow z (p - 2))) :
    IsBigO atTop (deriv (fun s => f (scalarCubic a s)))
      (fun s => Real.rpow s (3 * p - 1)) ∧
    IsBigO atTop (deriv (deriv (fun s => f (scalarCubic a s))))
      (fun s => Real.rpow s (3 * p - 2)) := by
  have hD : 0 < 9 * a := mul_pos (by norm_num) ha
  have hb1 := isBigO_comp_scalar_tail (deriv f) (p - 1) (9 * a) hD h1
  have hb2 := isBigO_comp_scalar_tail (deriv (deriv f)) (p - 2) (9 * a) hD h2
  have hfirst := (Kummer.rpow_mul_isBigO_of_add_eq _ 2 (3 * (p - 1))
    (3 * p - 1) (by simpa only [Real.rpow_eq_pow] using hb1) (by ring)).const_mul_left
      ((3 * a)⁻¹)
  have hsecond := (Kummer.rpow_mul_isBigO_of_add_eq _ 4 (3 * (p - 2))
    (3 * p - 2) (by simpa only [Real.rpow_eq_pow] using hb2) (by ring)).const_mul_left
      ((3 * a)⁻¹ ^ 2)
  have hsecond' := (Kummer.rpow_mul_isBigO_of_add_eq _ 1 (3 * (p - 1))
    (3 * p - 2) (by simpa only [Real.rpow_eq_pow] using hb1) (by ring)).const_mul_left
      (2 / (3 * a))
  constructor
  · apply hfirst.congr' _ (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hz : 0 < scalarCubic a s := div_pos (pow_pos hs _) hD
    have hc := hf.contDiffAt (isOpen_Ioi.mem_nhds hz)
    rw [deriv_comp_scalarCubic f a s (hc.differentiableAt (by norm_num))]
    simp only [Real.rpow_ofNat, scalarCubic]
    ring
  · apply (hsecond.add hsecond').congr' _ (by simp only [Real.rpow_eq_pow]; rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hz : 0 < scalarCubic a s := div_pos (pow_pos hs _) hD
    rw [deriv2_comp_scalarCubic f a s (hf.contDiffAt (isOpen_Ioi.mem_nhds hz))]
    simp only [Real.rpow_ofNat, Real.rpow_one, scalarCubic]
    ring

/-- The positive scalar remainder has the exact first two differentiated source orders. -/
theorem Fplus_tail_derivatives (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atTop
      (deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop
      (deriv (deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
  let f : ℝ → ℝ := fun z => Kummer.UNr gamma.negative z -
    Kummer.uExpansion (-gamma.1) (2 / 3) 1 z
  have he : ∀ z : ℝ, Kummer.uExpansion (-gamma.1) (2 / 3) 1 z =
      Real.rpow z gamma.1 := by
    intro z
    simp only [Kummer.uExpansion, Finset.sum_range_one, pow_zero, Kummer.poch_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, one_div, inv_one, neg_neg,
      Real.rpow_eq_pow]
  have hf : ContDiffOn ℝ 2 f (Ioi 0) := by
    have hpow : ContDiffOn ℝ 2 (fun z : ℝ => Real.rpow z gamma.1) (Ioi 0) := by
      simp only [Real.rpow_eq_pow]
      exact contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)
    have hu : ContDiffOn ℝ 2 (Kummer.UNr gamma.negative) (Ioi 0) :=
      (Kummer.contDiffOn_UNr gamma.negative).of_le (by norm_num)
    have hfe : f = fun z => Kummer.UNr gamma.negative z - Real.rpow z gamma.1 := by
      funext z
      dsimp only [f]
      rw [he]
    rw [hfe]
    exact hu.sub hpow
  have h1 : IsBigO atTop (deriv f) (fun z => Real.rpow z (gamma.1 - 2)) := by
    simpa only [f, ScalarGamma.negative, neg_neg, Nat.cast_one,
      show gamma.1 - 1 - 1 = gamma.1 - 2 by ring] using
      Kummer.UNr_expansion_deriv gamma.negative 1
  have h2 : IsBigO atTop (deriv (deriv f)) (fun z => Real.rpow z (gamma.1 - 3)) := by
    simpa only [f, ScalarGamma.negative, neg_neg, Nat.cast_one,
      show gamma.1 - 1 - 2 = gamma.1 - 3 by ring] using
      Kummer.UNr_expansion_deriv2 gamma.negative 1
  have hb := scalarCubic_remainder_derivatives f (gamma.1 - 1) Lam hLam hf
    (by simpa only [show gamma.1 - 1 - 1 = gamma.1 - 2 by ring] using h1)
    (by simpa only [show gamma.1 - 1 - 2 = gamma.1 - 3 by ring] using h2)
  have hloc (s : ℝ) (hs : 0 < s) : (fun t => f (scalarCubic Lam t)) =ᶠ[𝓝 s]
      fun t => Fplus gamma Lam t -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    dsimp only [f, scalarCubic, Fplus]
    rw [he, scalar_tail_power t (9 * Lam) gamma.1 ht (mul_pos (by norm_num) hLam)]
  have hloc' : deriv (fun s => f (scalarCubic Lam s)) =ᶠ[atTop]
      deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (hloc s hs).deriv_eq
  have hloc'' : deriv (deriv (fun s => f (scalarCubic Lam s))) =ᶠ[atTop]
      deriv (deriv (fun s => Fplus gamma Lam s -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (hloc s hs).deriv.deriv_eq
  constructor
  · convert hb.1.congr' hloc' EventuallyEq.rfl using 1
    funext s
    congr 1
    ring
  · convert hb.2.congr' hloc'' EventuallyEq.rfl using 1
    funext s
    congr 1
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
