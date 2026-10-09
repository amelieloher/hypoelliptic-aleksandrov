module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactness
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

/-! # Homogeneity passes through a common vague limit -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The pushforward characterization recovers the exact density-degree formula. -/
theorem bellman_degree_of_map_dilation (beta : ℝ) (mu : Measure BellmanPuncturedPlane)
    (hm : ∀ r : ℝ, ∀ hr : 0 < r,
      Measure.map (bellmanDilation r hr) mu = ENNReal.ofReal (r ^ (beta - 4)) • mu) :
    HasBellmanDensityDegree beta mu := by
  intro r hr E hE
  let D := bellmanDilationHomeomorph r hr
  have h := congrArg (fun nu : Measure BellmanPuncturedPlane => nu (D '' E)) (hm r hr)
  change (Measure.map D mu) (D '' E) = _ at h
  rw [Measure.map_apply D.measurable (D.measurableEmbedding.measurableSet_image.mpr hE),
    D.injective.preimage_image, Measure.smul_apply, smul_eq_mul] at h
  have hc : ENNReal.ofReal (r ^ (4 - beta)) * ENNReal.ofReal (r ^ (beta - 4)) = 1 := by
    rw [mul_comm]
    exact bellmanRadial_degreeFactors_cancel beta r hr
  calc mu (bellmanDilation r hr '' E) = 1 * mu (D '' E) := (one_mul _).symm
    _ = ENNReal.ofReal (r ^ (4 - beta)) *
        (ENNReal.ofReal (r ^ (beta - 4)) * mu (D '' E)) := by rw [← mul_assoc, hc]
    _ = ENNReal.ofReal (r ^ (4 - beta)) * mu E := by rw [← h]

/-- Vague limits of boundedly homogeneous measures retain the limiting density degree. -/
theorem bellman_vague_limit_degree (beta : ℕ → ℝ) (betaInf : ℝ)
    (mu : ℕ → Measure BellmanPuncturedPlane) (muInf : Measure BellmanPuncturedPlane)
    (hbeta : Tendsto beta atTop (𝓝 betaInf))
    (hd : ∀ n, HasBellmanDensityDegree (beta n) (mu n))
    (hrad : IsBellmanRadon muInf) (hv : IsBellmanVagueLimit mu muInf) :
    HasBellmanDensityDegree betaInf muInf := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  let := hrad.1
  apply bellman_degree_of_map_dilation
  intro r hr
  let D := bellmanDilationHomeomorph r hr
  let c := ENNReal.ofReal (r ^ (betaInf - 4))
  let : Measure.Regular (Measure.map D muInf) := Measure.Regular.map D
  let : IsFiniteMeasureOnCompacts (c • muInf) :=
    IsFiniteMeasureOnCompacts.smul muInf ENNReal.ofReal_ne_top
  change Measure.map D muInf = c • muInf
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [D.measurableEmbedding.integral_map, integral_smul_measure]
  have hleft := hv (fun q => f (D q)) (f.continuous.comp D.continuous)
    (f.hasCompactSupport.comp_homeomorph D)
  have hcoef : Tendsto (fun n => r ^ (beta n - 4)) atTop (𝓝 (r ^ (betaInf - 4))) :=
    (Real.continuous_const_rpow hr.ne').continuousAt.tendsto.comp
      (hbeta.sub_const 4)
  have hright := hcoef.mul (hv f f.continuous f.hasCompactSupport)
  have he (n : ℕ) : (∫ q, f (D q) ∂mu n) = r ^ (beta n - 4) * ∫ q, f q ∂mu n := by
    have hm := (hd n).map_dilation r hr
    change Measure.map D (mu n) = ENNReal.ofReal (r ^ (beta n - 4)) • mu n at hm
    rw [← D.measurableEmbedding.integral_map, hm, integral_smul_measure,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _), smul_eq_mul]
  rw [show c.toReal = r ^ (betaInf - 4) from
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _), smul_eq_mul]
  exact tendsto_nhds_unique hleft (by simpa only [he] using hright)

end HypoellipticAleksandrov.KineticAleksandrov
