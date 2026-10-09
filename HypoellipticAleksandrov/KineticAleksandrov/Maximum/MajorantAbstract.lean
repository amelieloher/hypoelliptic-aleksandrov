module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Smooth `Lᵖ`-sharp majorants on compact subsets of an open set

Abstract form of the source step Proposition 6.2.  Let `U` be open in a
finite-dimensional real normed space `E` with an additive Haar measure `μ`, let `K ⊆ U` be
compact, let `h` be continuous and nonnegative on `U`, and let `h ≤ F` almost everywhere on
`U`.  Then for every `ε > 0` there is a nonnegative compactly supported smooth `g` with
`tsupport g ⊆ U`, `g ≥ h` pointwise on `K`, and
`‖g‖_{Lᵖ(U)} ≤ ‖F‖_{Lᵖ(U)} + ε`.

No measurability of `F` is assumed: if `F` is not a.e. strongly measurable on `U`, then
`eLpNorm F p (μ.restrict U) = ∞` and the norm inequality is vacuous, while all other
conclusions hold regardless.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Smooth, compactly supported, nonnegative majorants with sharp `Lᵖ` control.

The construction is: smooth cutoff `χ` equal to `1` on `K`, mollify `χ h`, add the uniform
mollification error times `χ`.  The error is controlled in `Lᵖ` by the finite measure of a
compact thickening of `K` inside `U`. -/
theorem exists_smooth_majorant_eLpNorm_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {h F : E → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(μ.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K, h z ≤ g z) ∧
      eLpNorm g p (μ.restrict U) ≤ eLpNorm F p (μ.restrict U) + ENNReal.ofReal ε := by
  obtain ⟨ε₀, hε₀, hS2U, χ, hχ, hχ01, hχK, hχ0⟩ := exists_smooth_cutoff hU hK hKU
  have hS1c : IsCompact (cthickening ε₀ K) := hK.cthickening
  have hS2c : IsCompact (cthickening (2 * ε₀) K) := hK.cthickening
  have hS1S2 : cthickening ε₀ K ⊆ cthickening (2 * ε₀) K :=
    cthickening_mono (by linarith) K
  have hS1U : cthickening ε₀ K ⊆ U := hS1S2.trans hS2U
  set H : E → ℝ := fun z => χ z * h z with hHdef
  have hH0 : ∀ z, z ∉ cthickening ε₀ K → H z = 0 := fun z hz => by simp [hHdef, hχ0 z hz]
  have hHnn : ∀ z, 0 ≤ H z := by
    intro z
    by_cases hz : z ∈ U
    · exact mul_nonneg (hχ01 z).1 (hnn z hz)
    · rw [hH0 z (fun h' => hz (hS1U h'))]
  have hHcont : Continuous H := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact hχ.continuous.continuousAt.mul (hcont.continuousAt (hU.mem_nhds hz))
    · have hnhds : (cthickening ε₀ K)ᶜ ∈ nhds z :=
        isClosed_cthickening.isOpen_compl.mem_nhds fun h' => hz (hS1U h')
      have hev : H =ᶠ[nhds z] fun _ => 0 := by
        filter_upwards [hnhds] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr hev.symm
  have hHc : HasCompactSupport H := HasCompactSupport.intro hS1c hH0
  set m : ℝ≥0∞ := μ (cthickening (2 * ε₀) K) ^ (1 / p.toReal) with hm
  have hmt : m ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hS2c.measure_lt_top.ne
  set η : ℝ := ε / (2 * (m.toReal + 1)) with hηdef
  have hMpos : 0 < 2 * (m.toReal + 1) := by positivity
  have hη : 0 < η := div_pos hε hMpos
  obtain ⟨ψ, hψ, hψ0, hψH, hψS⟩ :=
    exists_smooth_uniform_approx μ hHcont hHc hHnn hH0 hε₀ hη
  have hS1S2' : cthickening ε₀ (cthickening ε₀ K) ⊆ cthickening (2 * ε₀) K := by
    refine (cthickening_cthickening_subset hε₀.le hε₀.le K).trans ?_
    rw [two_mul]
  have hψS2 : ∀ z, z ∉ cthickening (2 * ε₀) K → ψ z = 0 :=
    fun z hz => hψS z fun h' => hz (hS1S2' h')
  have hχS2 : ∀ z, z ∉ cthickening (2 * ε₀) K → χ z = 0 :=
    fun z hz => hχ0 z fun h' => hz (hS1S2 h')
  have hHS2 : ∀ z, z ∉ cthickening (2 * ε₀) K → H z = 0 :=
    fun z hz => hH0 z fun h' => hz (hS1S2 h')
  have hgS2 : ∀ z, z ∉ cthickening (2 * ε₀) K → ψ z + η * χ z = 0 :=
    fun z hz => by rw [hψS2 z hz, hχS2 z hz]; ring
  have hgc : HasCompactSupport (fun z => ψ z + η * χ z) := HasCompactSupport.intro hS2c hgS2
  have hts : tsupport (fun z => ψ z + η * χ z) ⊆ U := by
    refine (closure_minimal ?_ isClosed_cthickening).trans hS2U
    intro z hz
    by_contra hz'
    exact hz (hgS2 z hz')
  refine ⟨fun z => ψ z + η * χ z, ContDiff.add hψ (contDiff_const.mul hχ), hgc, hts,
    fun z => add_nonneg (hψ0 z) (mul_nonneg hη.le (hχ01 z).1), ?_, ?_⟩
  · intro z hz
    have h1 : H z = h z := by simp [hHdef, hχK z hz]
    have h2 := (abs_le.1 (hψH z)).1
    have h3 : χ z = 1 := hχK z hz
    show h z ≤ ψ z + η * χ z
    rw [h3, ← h1]
    linarith
  · set G : E → ℝ := fun z => (ψ z - H z) + η * χ z with hG
    have hGcont : Continuous G :=
      ((hψ.continuous.sub hHcont).add (continuous_const.mul hχ.continuous))
    have hsplit : (fun z => ψ z + η * χ z) = H + G := by
      funext z
      simp only [hG, Pi.add_apply]
      ring
    have hGbd : ∀ z, ‖G z‖ ≤ (cthickening (2 * ε₀) K).indicator (fun _ => 2 * η) z := by
      intro z
      by_cases hz : z ∈ cthickening (2 * ε₀) K
      · rw [indicator_of_mem hz, Real.norm_eq_abs]
        have h1 := hψH z
        have h2 : |η * χ z| ≤ η := by
          rw [abs_of_nonneg (mul_nonneg hη.le (hχ01 z).1)]
          exact mul_le_of_le_one_right hη.le (hχ01 z).2
        calc |G z| ≤ |ψ z - H z| + |η * χ z| := abs_add_le _ _
          _ ≤ 2 * η := by linarith
      · rw [indicator_of_notMem hz]
        have : G z = 0 := by
          simp only [hG, hψS2 z hz, hχS2 z hz, hHS2 z hz]
          ring
        simp [this]
    have hS2m : MeasurableSet (cthickening (2 * ε₀) K) := isClosed_cthickening.measurableSet
    have hGn : eLpNorm G p (μ.restrict U) ≤ ENNReal.ofReal ε := by
      calc eLpNorm G p (μ.restrict U)
          ≤ eLpNorm ((cthickening (2 * ε₀) K).indicator fun _ => 2 * η) p (μ.restrict U) :=
            eLpNorm_mono_ae_real hGcont.aestronglyMeasurable (Filter.Eventually.of_forall hGbd)
        _ = ‖(2 * η : ℝ)‖ₑ * (μ.restrict U) (cthickening (2 * ε₀) K) ^ (1 / p.toReal) :=
            eLpNorm_indicator_const hS2m.nullMeasurableSet (zero_lt_one.trans_le hp).ne' hpt
        _ = ENNReal.ofReal (2 * η) * m := by
            rw [Measure.restrict_eq_self _ hS2U, Real.enorm_eq_ofReal (by positivity)]
        _ = ENNReal.ofReal (2 * η * m.toReal) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * η), ENNReal.ofReal_toReal hmt]
        _ ≤ ENNReal.ofReal ε := by
            refine ENNReal.ofReal_le_ofReal ?_
            have : 2 * η * (m.toReal + 1) = ε := by
              rw [hηdef]
              field_simp
            nlinarith [this, hη]
    have hHn : eLpNorm H p (μ.restrict U) ≤ eLpNorm F p (μ.restrict U) := by
      refine eLpNorm_mono_ae_real hHcont.aestronglyMeasurable ?_
      filter_upwards [hF, ae_restrict_mem hU.measurableSet] with z hzF hzU
      rw [Real.norm_eq_abs, abs_of_nonneg (hHnn z)]
      calc H z = χ z * h z := rfl
        _ ≤ h z := mul_le_of_le_one_left (hnn z hzU) (hχ01 z).2
        _ ≤ F z := hzF
    rw [hsplit]
    calc eLpNorm (H + G) p (μ.restrict U)
        ≤ eLpNorm H p (μ.restrict U) + eLpNorm G p (μ.restrict U) := eLpNorm_add_le hp
      _ ≤ eLpNorm F p (μ.restrict U) + ENNReal.ofReal ε := add_le_add hHn hGn

/-- Sequence form of `exists_smooth_majorant_eLpNorm_le` with the source error `1 / j`:
for compact sets `K j ⊆ U` there are smooth majorants `g j` with
`‖g j‖_{Lᵖ(U)} ≤ ‖F‖_{Lᵖ(U)} + 1 / j` for every `j ≥ 1`. -/
theorem exists_smooth_majorant_seq (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} {K : ℕ → Set E} (hU : IsOpen U) (hK : ∀ j, IsCompact (K j))
    (hKU : ∀ j, K j ⊆ U)
    {h F : E → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(μ.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    ∃ g : ℕ → E → ℝ, ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (g j) ∧ HasCompactSupport (g j) ∧
      tsupport (g j) ⊆ U ∧ (∀ z, 0 ≤ g j z) ∧ (∀ z ∈ K j, h z ≤ g j z) ∧
      (1 ≤ j → eLpNorm (g j) p (μ.restrict U) ≤
        eLpNorm F p (μ.restrict U) + ENNReal.ofReal (1 / (j : ℝ))) := by
  have key : ∀ j : ℕ, ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ U ∧ (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K j, h z ≤ g z) ∧
      (1 ≤ j → eLpNorm g p (μ.restrict U) ≤
        eLpNorm F p (μ.restrict U) + ENNReal.ofReal (1 / (j : ℝ))) := by
    intro j
    have hjpos : 0 < ((max j 1 : ℕ) : ℝ) := by positivity
    obtain ⟨g, hg1, hg2, hg3, hg4, hg5, hg6⟩ := exists_smooth_majorant_eLpNorm_le μ hU (hK j)
      (hKU j) hcont hnn hF hp hpt (ε := 1 / ((max j 1 : ℕ) : ℝ)) (by positivity)
    refine ⟨g, hg1, hg2, hg3, hg4, hg5, fun hj => ?_⟩
    rwa [max_eq_left hj] at hg6
  choose g hg using key
  exact ⟨g, hg⟩

/-- Real-valued form of `exists_smooth_majorant_eLpNorm_le` when `F ∈ Lᵖ(U)`. -/
theorem exists_smooth_majorant_toReal_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {h F : E → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(μ.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) (hFp : MemLp F p (μ.restrict U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K, h z ≤ g z) ∧
      (eLpNorm g p (μ.restrict U)).toReal ≤ (eLpNorm F p (μ.restrict U)).toReal + ε := by
  obtain ⟨g, hg1, hg2, hg3, hg4, hg5, hg6⟩ :=
    exists_smooth_majorant_eLpNorm_le μ hU hK hKU hcont hnn hF hp hpt hε
  refine ⟨g, hg1, hg2, hg3, hg4, hg5, ?_⟩
  have hfin : eLpNorm F p (μ.restrict U) + ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hFp.eLpNorm_ne_top, ENNReal.ofReal_ne_top⟩
  calc (eLpNorm g p (μ.restrict U)).toReal
      ≤ (eLpNorm F p (μ.restrict U) + ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono hfin hg6
    _ = (eLpNorm F p (μ.restrict U)).toReal + ε := by
        rw [ENNReal.toReal_add hFp.eLpNorm_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hε.le]

end HypoellipticAleksandrov.KineticAleksandrov
