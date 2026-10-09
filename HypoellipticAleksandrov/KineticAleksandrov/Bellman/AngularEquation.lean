module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegration
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationProductIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationRadialTest
import Mathlib.Tactic

/-! # Derivation of the source angular weak equation from the actual adjoint pair -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The actual homogeneous stationary pair has angular measures satisfying the source
equation. -/
theorem exists_angular_adjoint (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ F H : Measure ℝ,
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      IsBellmanAngularAdjointPair 1 R β F H := by
  obtain ⟨F, H, hrep, hF, hFi, hH, hHi, hlo, hhi⟩ :=
    angular_disintegration R β hR hβ μ η hp
  let : IsFiniteMeasureOnCompacts F := hF
  let : IsFiniteMeasureOnCompacts H := hH
  refine ⟨F, H, hrep, hF, hFi, hH, hHi, ?_, hhi, ?_⟩
  · simpa only [ENNReal.ofReal_one, one_smul] using hlo
  intro φ hφ hcφ
  obtain ⟨ζ, hζ, hcζ, hsζ, hK, hrel⟩ := exists_bellmanAngularRadialTest β
  have hsζp : tsupport ζ ⊆ Ioi (0 : ℝ) :=
    fun s hs => lt_trans (by norm_num : (0 : ℝ) < 1) (hsζ hs).1
  have ht := bellmanAngularTest_contDiff ζ φ hζ hφ hsζp
  have hc := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).1
  have hs := bellmanAngularTest_support_punctured ζ φ hcζ hcφ hsζp
  have he := hp.2.2.2.2.2.1 (bellmanAngularTest ζ φ) ht hc hs
  let fx : ℝ × ℝ → ℝ :=
    fun q => q.2 * fderiv ℝ (bellmanAngularTest ζ φ) q (1, 0)
  let fv : ℝ × ℝ → ℝ :=
    fun q => fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1)) q (0, 1)
  have hts := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).2
  have hsx : tsupport fx ⊆ {q : ℝ × ℝ | 0 < q.1} :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hts)
  have hsv : tsupport fv ⊆ {q : ℝ × ℝ | 0 < q.1} :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hts)
  change (∫ q, fx q.val ∂μ) + (∫ q, fv q.val ∂η) = 0 at he
  rw [← bellman_integral_positive_restrict μ fx hsx,
    ← bellman_integral_positive_restrict η fv hsv, hrep.1, hrep.2] at he
  change (∫ q, q.val.2 * fderiv ℝ (bellmanAngularTest ζ φ) q.val (1, 0)
    ∂bellmanAngularRep β F) +
    (∫ q, fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
      q.val (0, 1) ∂bellmanAngularRep β H) = 0 at he
  rw [bellmanAngularRep_transport_integral β F ζ φ hζ hφ hcζ hcφ hsζp,
    bellmanAngularRep_velocity_integral β H ζ φ hζ hφ, hrel] at he
  have hzero : (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
      ((∫ y, deriv (deriv φ) y ∂H) - (1 / 3 : ℝ) * (∫ y, y ^ 2 * deriv φ y ∂F) +
        ((β - 2) / 3) * (∫ y, y * φ y ∂F)) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hzero).resolve_left hK.ne'

end HypoellipticAleksandrov.KineticAleksandrov
