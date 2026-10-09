module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialMeasuresProperties
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftProperties
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationaryTests
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationaryMeasureIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RadialStationaryIntegrability
import Mathlib.Tactic

/-! # Annihilation of homogeneous images gives the literal stationary radial adjoint pair -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- An annihilating sphere probability makes the actual radial measures stationary. -/
theorem radial_bellman_pair_stationary (lam Lam alpha : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (ha : 0 < alpha) (ha1 : alpha < 1)
    (pi : Measure (BellmanSphere × BellmanCoefficient lam Lam)) [IsProbabilityMeasure pi]
    (hann : ∀ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi →
      (∫ w, bellmanOperator w.2.val phi w.1.val ∂pi) = 0) :
    IsBellmanAdjointPair lam Lam (2 + alpha) (radialMu alpha pi) (radialEta alpha pi) := by
  obtain ⟨hm, he, hn, hlo, hhi, hdm, hde⟩ :=
    radial_bellman_measure_properties lam Lam alpha hlam hLam ha ha1 pi
  refine ⟨hm, he, hn, hlo, hhi, ?_, hdm, hde⟩
  intro zeta hz hc hs
  obtain ⟨⟨ht, htc, hts⟩, ⟨hv, hvc, hvs⟩⟩ :=
    bellman_radial_stationary_test_properties zeta hz hc hs
  let FT : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam) → ℝ :=
    fun w => w.1.val ^ (1 - alpha) *
      ((sphereRadialPoint w).val.2 * bellmanDx zeta (sphereRadialPoint w).val)
  let FV : BellmanPositiveTime × (BellmanSphere × BellmanCoefficient lam Lam) → ℝ :=
    fun w => w.1.val ^ (1 - alpha) *
      (w.2.2.val * bellmanDvv zeta (sphereRadialPoint w).val)
  have hFT : Integrable FT (bellmanPositiveTimeVolume.prod pi) := by
    simpa only [one_mul] using bellman_radial_test_integrable alpha pi
      (fun q => q.2 * bellmanDx zeta q) ht htc hts (fun _ => 1) continuous_const
  have hFV : Integrable FV (bellmanPositiveTimeVolume.prod pi) :=
    bellman_radial_test_integrable alpha pi (bellmanDvv zeta) hv hvc hvs
      (fun w => w.2.val) (continuous_subtype_val.comp continuous_snd)
  have hMT : (∫ q, q.val.2 * fderiv ℝ zeta q.val (1, 0) ∂radialMu alpha pi) =
      ∫ w, FT w ∂bellmanPositiveTimeVolume.prod pi :=
    integral_radialMu alpha pi (fun q => q.val.2 * bellmanDx zeta q.val)
      (ht.comp continuous_subtype_val)
  have hMV : (∫ q, fderiv ℝ (fun z => fderiv ℝ zeta z (0, 1)) q.val (0, 1)
      ∂radialEta alpha pi) = ∫ w, FV w ∂bellmanPositiveTimeVolume.prod pi :=
    integral_radialEta alpha pi (fun q => bellmanDvv zeta q.val)
      (hv.comp continuous_subtype_val) hlam.le
  rw [hMT, hMV, ← integral_add hFT hFV,
    integral_prod_symm (fun w => FT w + FV w) (hFT.add hFV)]
  have hLift : IsBellmanHomogeneous alpha (lift alpha zeta) :=
    (bellman_test_lift alpha ha ha1 zeta (hz.of_le (by norm_num)).contDiffOn hc hs).1
  calc
    (∫ w, ∫ r, FT (r, w) + FV (r, w) ∂bellmanPositiveTimeVolume ∂pi) =
        ∫ w, bellmanOperator w.2.val (lift alpha zeta) w.1.val ∂pi := by
      apply integral_congr_ae
      apply ae_of_all
      intro w
      exact (bellman_lift_operator_integral alpha zeta hz hc hs w.1.val w.1.ne_zero
        w.2.val).symm
    _ = 0 := hann (lift alpha zeta) hLift

end HypoellipticAleksandrov.KineticAleksandrov
