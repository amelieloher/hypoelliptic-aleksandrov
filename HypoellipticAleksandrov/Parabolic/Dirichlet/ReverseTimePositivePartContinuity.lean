module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePart

/-!
# Continuity of the reverse-time positive part

This module proves strong continuity of the pointwise spatial positive-part
operation on the reverse-time Bochner `L²` space.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The pointwise positive-part operation is strongly continuous on the
reverse-time Bochner `L²(V)` space. -/
theorem continuous_reverseTimePositivePart (hΩ : IsOpen Ω) (T : ℝ) :
    Continuous (reverseTimePositivePart hΩ T :
      ReverseTimeL2V hΩ T → ReverseTimeL2V hΩ T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  rw [continuous_iff_seqContinuous]
  intro un u hun
  let f : ℕ → ℝ → H10HilbertGraph hΩ := fun n τ => un n τ
  let g : ℕ → ℝ → H10HilbertGraph hΩ :=
    fun n τ => h10PositivePart hΩ (un n τ)
  let g₀ : ℝ → H10HilbertGraph hΩ := fun τ => h10PositivePart hΩ (u τ)
  have hfMem : ∀ n, MemLp (f n) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    fun n => Lp.memLp (un n)
  have huMem : MemLp (fun τ => u τ) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    Lp.memLp u
  have hfLp : Tendsto (fun n => eLpNorm (f n - fun τ => u τ) 2
      (reverseTimeVolume T)) atTop (nhds 0) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' un u).1 hun
  have hfUI : UnifIntegrable f (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num) hfMem huMem hfLp
  have hgMem : ∀ n, MemLp (g n) (2 : ℝ≥0∞) (reverseTimeVolume T) := by
    intro n
    exact (memLp_congr_ae (coeFn_reverseTimePositivePart hΩ T (un n))).mp
      (Lp.memLp (reverseTimePositivePart hΩ T (un n)))
  have hgUI : UnifIntegrable g (2 : ℝ≥0∞) (reverseTimeVolume T) := by
    apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := unifIntegrable_iff'.mp hfUI ε hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    refine (eLpNorm_mono ((hgMem n).aestronglyMeasurable.restrict) ?_).trans (hbound n s hs hμs)
    intro τ
    exact norm_h10PositivePart_le hΩ _
  have hg₀Mem : MemLp g₀ (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    (memLp_congr_ae (coeFn_reverseTimePositivePart hΩ T u)).mp
      (Lp.memLp (reverseTimePositivePart hΩ T u))
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hun.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume T,
      Tendsto (fun n => g (ns (ms n)) τ) atTop (nhds (g₀ τ)) := by
    filter_upwards [hae] with τ hτ
    exact (continuous_h10PositivePart hΩ).continuousAt.tendsto.comp hτ
  have hnorm : Tendsto (fun n => eLpNorm
      (g (ns (ms n)) - g₀) (2 : ℝ≥0∞) (reverseTimeVolume T))
      atTop (nhds 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    · exact fun n => (hgMem (ns (ms n))).aestronglyMeasurable
    · exact hg₀Mem
    · exact UnifIntegrable.comp (f := g) (p := (2 : ℝ≥0∞))
        (μ := reverseTimeVolume T) (fun n => ns (ms n)) hgUI
    · exact hpoint
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine hnorm.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [coeFn_reverseTimePositivePart hΩ T (un (ns (ms n))),
    coeFn_reverseTimePositivePart hΩ T u] with τ hleft hright
  simp only [Pi.sub_apply, g, g₀]
  change _ = (reverseTimePositivePart hΩ T (un (ns (ms n)))) τ -
    (reverseTimePositivePart hΩ T u) τ
  rw [hleft, hright]

end HypoellipticAleksandrov.Parabolic.Dirichlet
