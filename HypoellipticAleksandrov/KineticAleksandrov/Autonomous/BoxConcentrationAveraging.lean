module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupation

/-! # Averaging a return-time comparison over the literal later time window -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- Averaging over `(2t,3t]` uses its length `t` and the full occupation through `3t`. -/
theorem box_return_time_average (E : FullSpaceEvolution) (z : Z) (A0 r Y t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hcomp : ∀ s ∈ Ioc (2 * t) (3 * t),
      (kernelXV E (Real.toNNReal t) z (box A0 r Y)).toReal ≤
        C * (kernelXV E (Real.toNNReal s) z (box A0 r Y)).toReal) :
    t * (kernelXV E (Real.toNNReal t) z (box A0 r Y)).toReal ≤
      C * ∫ s in Ioc 0 (3 * t),
        (kernelXV E (Real.toNNReal s) z (box A0 r Y)).toReal := by
  let f := fun s : ℝ => (kernelXV E (Real.toNNReal s) z (box A0 r Y)).toReal
  have hi := box_action_integrableOn E z A0 r Y (3 * t)
  have hs : Ioc (2 * t) (3 * t) ⊆ Ioc 0 (3 * t) :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hsmall := hi.mono_set hs
  have hmono := setIntegral_mono_on
    (integrableOn_const (C := f t) (by simp : volume (Ioc (2 * t) (3 * t)) ≠ ⊤))
    (hsmall.const_mul C) measurableSet_Ioc hcomp
  have hvol : volume.real (Ioc (2 * t) (3 * t)) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [setIntegral_const, hvol, smul_eq_mul, integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (Filter.Eventually.of_forall hs)) hC)

/-- The kinetic scaling identity converts occupation decay to a dimensionless time ratio. -/
theorem box_decay_scaling {r t alpha : ℝ} (hr : 0 < r) (ht : 0 < t) :
    r ^ (gamma alpha) * t ^ (alpha / 2) / t = (t / r ^ 2) ^ (-gamma alpha / 2) := by
  have he : -gamma alpha / 2 = alpha / 2 - 1 := by dsimp only [gamma]; ring
  rw [Real.div_rpow ht.le (sq_nonneg r), he, Real.rpow_sub_one ht.ne']
  have hp : (r ^ 2 : ℝ) ^ (alpha / 2 - 1) = r ^ (-gamma alpha) := by
    rw [← Real.rpow_natCast_mul hr.le]
    congr 1
    dsimp only [gamma]
    ring
  rw [hp, Real.rpow_neg hr.le]
  have hpow := (Real.rpow_pos_of_pos hr (gamma alpha)).ne'
  field_simp

/-- Negative powers yield the source's `1+t/r²` decay, with a uniform large-time factor. -/
theorem box_decay_large_comparison {x g : ℝ} (hx : 1 ≤ x) (hg : 0 ≤ g) :
    x ^ (-g / 2) ≤ 2 ^ (g / 2) * (1 + x) ^ (-g / 2) := by
  have hx0 : 0 < x := by linarith
  have h1 : 0 < 1 + x := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos h1 (by linarith : 1 + x ≤ 2 * x)
    (by linarith : -g / 2 ≤ 0)
  rw [Real.mul_rpow (by norm_num) hx0.le] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (g / 2))
  have he : (2 : ℝ) ^ (g / 2) * 2 ^ (-g / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show g / 2 + -g / 2 = 0 by ring, Real.rpow_zero]
  simpa only [← mul_assoc, he, one_mul] using hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
