module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Dominated convergence in finite-exponent `L^p`

This file packages the form of dominated convergence used by Sobolev
composition and truncation arguments.  The exponent is arbitrary and finite:
if a sequence converges almost everywhere and is pointwise dominated in norm
by one `L^p` function, then it converges in `L^p`.

The proof uses Mathlib's finite-measure Vitali theorem.  Domination supplies
uniform integrability directly, with no exponent-dependent loss.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- A family pointwise dominated in norm by one `L^p` function is uniformly
integrable at every finite exponent `p ≥ 1`. -/
theorem unifIntegrable_of_ae_norm_le
    {ι α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ι → α → E} {bound : α → E}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hboundMem : MemLp bound p μ)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ ‖bound x‖) :
    UnifIntegrable F p μ := by
  rw [unifIntegrable_iff']
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ :=
    hboundMem.eLpNorm_indicator_le hp hpTop hε
  refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  refine (eLpNorm_mono_ae ((hF i).indicator hs) ?_).trans (hsmall s hs hμs)
  filter_upwards [hbound i] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
    exact hx
  · simp only [Set.indicator_of_notMem hxs, norm_zero]
    exact le_rfl

/-- Dominated almost-everywhere convergence implies convergence in
finite-exponent `L^p` on a finite measure space. -/
theorem tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ℕ → α → E} {f bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : MemLp f p μ) (hboundMem : MemLp bound p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hFf :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto
      (fun n => eLpNorm (F n - f) p μ)
      atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendsto_ae
    hp hpTop hF hf
    (unifIntegrable_of_ae_norm_le hp hpTop hF hboundMem hbound)
    hFf

end PDE
