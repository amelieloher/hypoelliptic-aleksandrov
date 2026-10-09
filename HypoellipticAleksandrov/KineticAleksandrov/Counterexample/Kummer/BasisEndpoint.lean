module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisWronskian
import Mathlib.Tactic

/-!
# Endpoint evaluation of Abel's constant

The regular value and the scaled derivative determine the weighted Wronskian.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter
open scoped Topology

/-- Expanded weighted Wronskian against the fractional-power M solution. -/
theorem weightedWronskian_secondM (a z : ℝ) (hz : 0 < z) (f : ℝ → ℝ) :
    weightedWronskian (2 / 3) f (secondM a) z = Real.exp (-z) *
      (z * deriv f z * M (a + 1 / 3) b43 z -
        f z * ((1 / 3 : ℝ) * M (a + 1 / 3) b43 z +
          z * deriv (M (a + 1 / 3) b43) z)) := by
  have hd := hasDerivAt_power_mul (M (a + 1 / 3) b43) (1 / 3) z hz
    (hasDerivAt_M (a + 1 / 3) b43 z).differentiableAt.hasDerivAt
  have he : deriv (secondM a) z =
      (1 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) * M (a + 1 / 3) b43 z +
        z ^ (1 / 3 : ℝ) * deriv (M (a + 1 / 3) b43) z := hd.deriv
  rw [weightedWronskian, he, secondM]
  have hp : z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = z := by
    rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + 1 / 3 = 1 by ring, Real.rpow_one]
  have hq : z ^ (2 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) = 1 := by
    rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + (1 / 3 - 1) = 0 by ring,
      Real.rpow_zero]
  calc
    _ = Real.exp (-z) *
      ((z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ)) * deriv f z * M (a + 1 / 3) b43 z -
        f z * ((1 / 3 : ℝ) * (z ^ (2 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1)) *
          M (a + 1 / 3) b43 z + (z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ)) *
          deriv (M (a + 1 / 3) b43) z)) := by ring
    _ = _ := by rw [hp, hq]; ring

/-- Endpoint limit of the weighted Wronskian. -/
theorem tendsto_weightedWronskian_secondM_zero (a : ℝ) (f : ℝ → ℝ) (F : ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 F))
    (hf' : Tendsto (fun z : ℝ => z * deriv f z) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (weightedWronskian (2 / 3) f (secondM a)) (𝓝[>] 0)
      (𝓝 (-(1 / 3 : ℝ) * F)) := by
  have hm : Tendsto (M (a + 1 / 3) b43) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hasDerivAt_M (a + 1 / 3) b43 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hmd : ContinuousAt (deriv (M (a + 1 / 3) b43)) 0 := by
    have he : deriv (M (a + 1 / 3) b43) =
        fun z => ((a + 1 / 3) / b43.1) * M (a + 1 / 3 + 1) (next b43) z :=
      funext (deriv_M (a + 1 / 3) b43)
    rw [he]
    exact continuousAt_const.mul (hasDerivAt_M _ _ 0).continuousAt
  have hz : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun z : ℝ => Real.exp (-z)) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun z : ℝ => Real.exp (-z)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hl := he.mul ((hf'.mul hm).sub
    (hf.mul ((hm.const_mul (1 / 3 : ℝ)).add
      (hz.mul (hmd.tendsto.mono_left nhdsWithin_le_nhds)))))
  simp only [zero_mul, mul_one, add_zero, one_mul, zero_sub] at hl
  have hl' : Tendsto (fun z => Real.exp (-z) *
      (z * deriv f z * M (a + 1 / 3) b43 z -
        f z * ((1 / 3 : ℝ) * M (a + 1 / 3) b43 z +
          z * deriv (M (a + 1 / 3) b43) z))) (𝓝[>] 0)
      (𝓝 (-(1 / 3 : ℝ) * F)) := by
    convert hl using 1
    congr 1
    ring
  apply hl'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (weightedWronskian_secondM a z hz f).symm

/-- Evaluation of Abel's constant by the two endpoint limits. -/
theorem weightedWronskian_secondM_eq (a : ℝ) (f : ℝ → ℝ) (F : ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0))
    (ho : ∀ z > 0, z * deriv (deriv f) z + (2 / 3 - z) * deriv f z - a * f z = 0)
    (hlim : Tendsto f (𝓝[>] 0) (𝓝 F))
    (hdlim : Tendsto (fun z : ℝ => z * deriv f z) (𝓝[>] 0) (𝓝 0))
    (z : ℝ) (hz : 0 < z) :
    weightedWronskian (2 / 3) f (secondM a) z = -(1 / 3 : ℝ) * F := by
  have hg := contDiffOn_secondM a
  have hc (x : ℝ) (hx : 0 < x) := weightedWronskian_eq a (2 / 3) f (secondM a)
    (hf.differentiableOn (by simp)) (hg.differentiableOn (by simp))
    ((hf.deriv_of_isOpen (m := 1) isOpen_Ioi (by simp)).differentiableOn (by simp))
    ((hg.deriv_of_isOpen (m := 1) isOpen_Ioi (by simp)).differentiableOn (by simp))
    ho (secondM_ode a) x z hx hz
  have hl := tendsto_weightedWronskian_secondM_zero a f F hlim hdlim
  have hconst : Tendsto (weightedWronskian (2 / 3) f (secondM a)) (𝓝[>] 0)
      (𝓝 (weightedWronskian (2 / 3) f (secondM a) z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hc x hx).symm
  exact tendsto_nhds_unique hconst hl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
