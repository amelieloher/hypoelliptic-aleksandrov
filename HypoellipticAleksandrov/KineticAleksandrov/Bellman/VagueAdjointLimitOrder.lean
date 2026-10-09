module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactness
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

/-! # Positive compact tests determine the order of Radon measures -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ENNReal NNReal
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Nonnegative compact tests control the mass of every compact subset. -/
theorem bellman_compact_measure_le_of_positive_tests (mu nu : Measure X)
    [IsFiniteMeasureOnCompacts mu] [IsFiniteMeasureOnCompacts nu] [nu.OuterRegular]
    (ht : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → ∫ x, f x ∂mu ≤ ∫ x, f x ∂nu)
    {K : Set X} (hK : IsCompact K) : mu K ≤ nu K := by
  refine ENNReal.le_of_forall_pos_le_add fun eps heps hnu => ?_
  have hnuK : nu K ≠ ⊤ := hnu.ne
  have hmuK : mu K ≠ ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, hKV, hV, hmass⟩ :=
    exists_isOpen_le_add K nu (ne_of_gt (ENNReal.coe_lt_coe.mpr heps))
  suffices mu.real K ≤ nu.real K + eps by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  have hVfinite : nu V < ⊤ := hmass.trans_lt (by finiteness)
  obtain ⟨f, hfone, hfc, hfs, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
  let g : C_c(X, ℝ) := ⟨f, hfc⟩
  have hgK (x : X) : K.indicator 1 x ≤ g x := by
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx, Pi.one_apply]
      change 1 ≤ f x
      have he := hfone hx
      change f x = 1 at he
      rw [he]
    · simp only [indicator_of_notMem hx]; exact (hf01 x).1
  have hgV (x : X) : g x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ tsupport g
    · simp only [indicator_of_mem (hfs hx), Pi.one_apply]; exact (hf01 x).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact indicator_nonneg (fun _ _ => zero_le_one) x
  calc mu.real K = ∫ x, K.indicator 1 x ∂mu :=
        (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x, g x ∂mu := integral_mono
      ((continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet)
      g.integrable hgK
    _ ≤ ∫ x, g x ∂nu := ht g (fun x => (hf01 x).1)
    _ ≤ ∫ x, V.indicator 1 x ∂nu := integral_mono g.integrable
      (IntegrableOn.integrable_indicator integrableOn_const hV.measurableSet) hgV
    _ ≤ nu.real K + eps := by
      rw [integral_indicator_one hV.measurableSet]
      have hh := ENNReal.toReal_mono (by finiteness : nu K + (eps : ℝ≥0∞) ≠ ∞) hmass
      rw [ENNReal.toReal_add hnuK ENNReal.coe_ne_top, ENNReal.coe_toReal] at hh
      exact hh

/-- Inner regularity upgrades positive compact-test order to actual measure order. -/
theorem bellman_measure_le_of_positive_tests (mu nu : Measure X)
    [IsFiniteMeasureOnCompacts mu] [IsFiniteMeasureOnCompacts nu]
    [mu.InnerRegular] [nu.OuterRegular]
    (ht : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → ∫ x, f x ∂mu ≤ ∫ x, f x ∂nu) :
    mu ≤ nu := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [hE.measure_eq_iSup_isCompact mu]
  refine iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => ?_
  exact (bellman_compact_measure_le_of_positive_tests mu nu ht hK).trans (measure_mono hKE)

end HypoellipticAleksandrov.KineticAleksandrov
