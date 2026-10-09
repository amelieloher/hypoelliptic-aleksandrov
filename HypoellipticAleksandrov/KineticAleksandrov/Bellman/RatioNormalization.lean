module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationCalculus
import Mathlib.Tactic

/-! # Ratio-only dependence of the Bellman admissible degree set -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Division by a positive position scale gives the literal finite measure multiplier. -/
theorem bellman_ofReal_div (a s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (a / s) = ENNReal.ofReal s⁻¹ * ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hs.le)]
  congr 1
  ring

/-- Literal position rescaling transports unnormalized adjoint pairs with both bounds divided. -/
theorem IsBellmanAdjointPair.rescale_position {lam Lam β : ℝ}
    {μ η : Measure BellmanPuncturedPlane} (hp : IsBellmanAdjointPair lam Lam β μ η)
    (s : ℝ) (hs : 0 < s) :
    IsBellmanAdjointPair (lam / s) (Lam / s) β
      (Measure.map (bellmanPositionHomeomorph s hs) μ)
      (ENNReal.ofReal s⁻¹ • Measure.map (bellmanPositionHomeomorph s hs) η) := by
  let H := bellmanPositionHomeomorph s hs
  rcases hp with ⟨hμ, hη, hne, hlo, hhi, hstat, hdμ, hdη⟩
  have hμne : μ ≠ 0 :=
    IsBellmanAdjointPair.left_ne_zero ⟨hμ, hη, hne, hlo, hhi, hstat, hdμ, hdη⟩
  refine ⟨hμ.map_homeomorph H,
    (hη.map_homeomorph H).smul _ ENNReal.ofReal_ne_top,
    Or.inl ((Measure.map_ne_zero_iff H.measurable.aemeasurable).mpr hμne), ?_, ?_,
    hstat.map_position s hs, hdμ.map_position s hs, (hdη.map_position s hs).smul _⟩
  · rw [bellman_ofReal_div lam s hs, ← smul_smul]
    apply smul_le_smul_left
    have h := Measure.map_mono hlo H.measurable
    rwa [Measure.map_smul _ H.measurable.aemeasurable] at h
  · rw [bellman_ofReal_div Lam s hs, ← smul_smul]
    apply smul_le_smul_left
    have h := Measure.map_mono hhi H.measurable
    rwa [Measure.map_smul _ H.measurable.aemeasurable] at h

/-- The full admissible-degree set depends only on the ellipticity ratio. -/
theorem bellman_degrees_normalize (lam Lam : ℝ) (hlam : 0 < lam)
    (_hLam : lam ≤ Lam) :
    bellmanDegrees lam Lam = bellmanAdmissibleDegrees (Lam / lam) := by
  ext β
  rw [mem_bellmanAdmissibleDegrees_iff]
  constructor
  · rintro ⟨μ, η, hp⟩
    refine ⟨Measure.map (bellmanPositionHomeomorph lam hlam) μ,
      ENNReal.ofReal lam⁻¹ • Measure.map (bellmanPositionHomeomorph lam hlam) η, ?_⟩
    simpa only [div_self hlam.ne'] using hp.rescale_position lam hlam
  · rintro ⟨μ, η, hp⟩
    refine ⟨Measure.map (bellmanPositionHomeomorph lam⁻¹ (inv_pos.mpr hlam)) μ,
      ENNReal.ofReal (lam⁻¹)⁻¹ •
        Measure.map (bellmanPositionHomeomorph lam⁻¹ (inv_pos.mpr hlam)) η, ?_⟩
    have hlow : (1 : ℝ) / lam⁻¹ = lam := by simp
    have hhigh : (Lam / lam) / lam⁻¹ = Lam := by
      simp [div_inv_eq_mul, hlam.ne']
    simpa only [hlow, hhigh] using hp.rescale_position lam⁻¹ (inv_pos.mpr hlam)

end HypoellipticAleksandrov.KineticAleksandrov
