module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
import Mathlib.Tactic

/-! # Common positive normalization preserves the complete adjoint-pair condition -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Multiplying both measures preserves the literal weak equation. -/
theorem IsBellmanStationaryAdjointPair.smul {mu eta : Measure BellmanPuncturedPlane}
    (h : IsBellmanStationaryAdjointPair mu eta) (c : ENNReal) :
    IsBellmanStationaryAdjointPair (c • mu) (c • eta) := by
  intro phi hphi hc hs
  rw [integral_smul_measure, integral_smul_measure, ← smul_add, h phi hphi hc hs, smul_zero]

/-- Positive finite common scaling preserves every source condition of an admissible pair. -/
theorem IsBellmanAdjointPair.smul {lam Lam beta : ℝ}
    {mu eta : Measure BellmanPuncturedPlane} (h : IsBellmanAdjointPair lam Lam beta mu eta)
    (c : ℝ) (hc : 0 < c) :
    IsBellmanAdjointPair lam Lam beta (ENNReal.ofReal c • mu) (ENNReal.ofReal c • eta) := by
  rcases h with ⟨hm, he, hn, hlo, hhi, hstat, hdm, hde⟩
  refine ⟨hm.smul _ ENNReal.ofReal_ne_top, he.smul _ ENNReal.ofReal_ne_top, ?_, ?_, ?_,
    hstat.smul _, hdm.smul _, hde.smul _⟩
  · have hcn : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
    rcases hn with hn | hn
    · exact Or.inl (fun hz => hn ((Measure.ennreal_smul_eq_zero.mp hz).resolve_left hcn))
    · exact Or.inr (fun hz => hn ((Measure.ennreal_smul_eq_zero.mp hz).resolve_left hcn))
  · simpa only [smul_smul, mul_comm] using smul_le_smul_left (ENNReal.ofReal c) hlo
  · simpa only [smul_smul, mul_comm] using smul_le_smul_left (ENNReal.ofReal c) hhi

end HypoellipticAleksandrov.KineticAleksandrov
