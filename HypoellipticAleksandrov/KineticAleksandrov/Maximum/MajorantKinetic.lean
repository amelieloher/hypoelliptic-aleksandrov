module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.MajorantAbstract
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Smooth majorants on kinetic points

Kinetic form of the source step Proposition 6.2.  The kinetic carrier
`KineticPoint d` is identified with `ℝ × (Vec d × Vec d)` by `KineticPoint.equivProd`,
which is a homeomorphism carrying kinetic volume to product Lebesgue measure.  Smoothness
of a function `g : KineticPoint d → ℝ` is read in these coordinates, i.e. as
`ContDiff ℝ (⊤ : ℕ∞) (g ∘ (KineticPoint.equivProd d).symm)`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set
open scoped ENNReal

/-- Product Lebesgue measure on the coordinate space of kinetic points is an additive Haar
measure. -/
theorem isAddHaarMeasure_volume_coordinates (d : ℕ) :
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).IsAddHaarMeasure := by
  have h1 : (volume : Measure (PDE.Vec d × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  exact Measure.prod.instIsAddHaarMeasure volume volume

/-- Kinetic form of the majorant lemma. -/
theorem exists_smooth_majorant_kinetic {d : ℕ} {U K : Set (KineticPoint d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {h F : KineticPoint d → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(volume.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g ((KineticPoint.equivProd d).symm x)) ∧
      HasCompactSupport g ∧ tsupport g ⊆ U ∧ (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K, h z ≤ g z) ∧
      eLpNorm g p (volume.restrict U) ≤ eLpNorm F p (volume.restrict U) + ENNReal.ofReal ε := by
  have := isAddHaarMeasure_volume_coordinates d
  let e := KineticPoint.homeomorphProd d
  have hmp : MeasurePreserving e volume volume := KineticPoint.measurePreserving_equivProd d
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hpre : ∀ s : Set (KineticPoint d), e ⁻¹' (e.symm ⁻¹' s) = s := fun s => by
    ext z
    simp
  have hmpU : MeasurePreserving e (volume.restrict U) (volume.restrict (e.symm ⁻¹' U)) := by
    simpa only [hpre] using hmp.restrict_preimage_emb hemb (e.symm ⁻¹' U)
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hK' : IsCompact (e.symm ⁻¹' K) := e.symm.isCompact_preimage.2 hK
  have hKU' : e.symm ⁻¹' K ⊆ e.symm ⁻¹' U := preimage_mono hKU
  have hcont' : ContinuousOn (h ∘ e.symm) (e.symm ⁻¹' U) :=
    hcont.comp e.symm.continuous.continuousOn (fun x hx => hx)
  have hnn' : ∀ x ∈ e.symm ⁻¹' U, 0 ≤ (h ∘ e.symm) x := fun x hx => hnn _ hx
  have hF' : ∀ᵐ x ∂(volume.restrict (e.symm ⁻¹' U)), (h ∘ e.symm) x ≤ (F ∘ e.symm) x := by
    have hsymm : MeasurePreserving e.symm (volume.restrict (e.symm ⁻¹' U))
        (volume.restrict U) := by
      exact MeasurePreserving.symm e.toMeasurableEquiv hmpU
    exact hsymm.quasiMeasurePreserving.ae hF
  obtain ⟨g₀, hg1, hg2, hg3, hg4, hg5, hg6⟩ := exists_smooth_majorant_eLpNorm_le
    (E := ℝ × (PDE.Vec d × PDE.Vec d)) volume hU' hK'
    hKU' hcont' hnn' hF' hp hpt hε
  have hnormEq' : ∀ f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ,
      eLpNorm f p (volume.restrict (e.symm ⁻¹' U)) = eLpNorm (f ∘ e) p (volume.restrict U) := by
    intro f
    rw [← hmpU.map_eq, hemb.eLpNorm_map_measure]
  have hnormEq : eLpNorm (F ∘ e.symm) p (volume.restrict (e.symm ⁻¹' U)) =
      eLpNorm F p (volume.restrict U) := by
    rw [hnormEq']
    congr 1
  refine ⟨g₀ ∘ e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (fun x => (g₀ ∘ e) ((KineticPoint.equivProd d).symm x)) = g₀ := by
      funext x
      exact congrArg g₀ (e.apply_symm_apply x)
    rw [this]
    exact hg1
  · exact hg2.comp_homeomorph e
  · rw [tsupport_comp_eq_preimage g₀ e]
    exact fun z hz => hg3 hz
  · exact fun z => hg4 _
  · intro z hz
    have := hg5 (e z) (by simpa using hz)
    simpa using this
  · rw [← hnormEq, ← hnormEq']
    exact hg6

/-- Sequence form of `exists_smooth_majorant_kinetic` with the source error `1 / j`:
smooth compactly supported majorants `g j` on compact sets `K j ⊆ U`, with
`‖g j‖_{Lᵖ(U)} ≤ ‖F‖_{Lᵖ(U)} + 1 / j` for `j ≥ 1`. -/
theorem exists_smooth_majorant_kinetic_seq {d : ℕ} {U : Set (KineticPoint d)}
    {K : ℕ → Set (KineticPoint d)} (hU : IsOpen U) (hK : ∀ j, IsCompact (K j))
    (hKU : ∀ j, K j ⊆ U)
    {h F : KineticPoint d → ℝ} (hcont : ContinuousOn h U) (hnn : ∀ z ∈ U, 0 ≤ h z)
    (hF : ∀ᵐ z ∂(volume.restrict U), h z ≤ F z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    ∃ g : ℕ → KineticPoint d → ℝ, ∀ j : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g j ((KineticPoint.equivProd d).symm x)) ∧
      HasCompactSupport (g j) ∧ tsupport (g j) ⊆ U ∧ (∀ z, 0 ≤ g j z) ∧
      (∀ z ∈ K j, h z ≤ g j z) ∧
      (1 ≤ j → eLpNorm (g j) p (volume.restrict U) ≤
        eLpNorm F p (volume.restrict U) + ENNReal.ofReal (1 / (j : ℝ))) := by
  have key : ∀ j : ℕ, ∃ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g ((KineticPoint.equivProd d).symm x)) ∧
      HasCompactSupport g ∧ tsupport g ⊆ U ∧ (∀ z, 0 ≤ g z) ∧ (∀ z ∈ K j, h z ≤ g z) ∧
      (1 ≤ j → eLpNorm g p (volume.restrict U) ≤
        eLpNorm F p (volume.restrict U) + ENNReal.ofReal (1 / (j : ℝ))) := by
    intro j
    have hjpos : 0 < ((max j 1 : ℕ) : ℝ) := by positivity
    obtain ⟨g, hg1, hg2, hg3, hg4, hg5, hg6⟩ := exists_smooth_majorant_kinetic hU (hK j)
      (hKU j) hcont hnn hF hp hpt (ε := 1 / ((max j 1 : ℕ) : ℝ)) (by positivity)
    refine ⟨g, hg1, hg2, hg3, hg4, hg5, fun hj => ?_⟩
    rwa [max_eq_left hj] at hg6
  choose g hg using key
  exact ⟨g, hg⟩

/-- Node Proposition 6.2 in source notation.

`Q` is the open cylinder, `K j` are the compact inner closures `closure (Q_j)`, `u` plays the
role of `U`, `g` the defect `(-K_A U)_+`, `θ` the cutoff, and `g₀` the source bound.  The
hypotheses are the source ones: continuity of `u` and `g` on `Q`, `g ≥ 0`, `0 ≤ θ`, `θ`
continuous, and the almost-everywhere domination
`θ(u) g ≤ g₀ 1_{u>0}` on `Q`.  The conclusion gives nonnegative `C_c^∞(Q)` majorants of
`θ(u) g` on each `K j` with `Lᵖ` norm at most `‖g₀ 1_{u>0}‖_{Lᵖ(Q)} + 1/j`. -/
theorem exists_smooth_majorants_source {d : ℕ} {Q : Set (KineticPoint d)}
    {K : ℕ → Set (KineticPoint d)} (hQ : IsOpen Q) (hK : ∀ j, IsCompact (K j))
    (hKQ : ∀ j, K j ⊆ Q)
    (u g g₀ : KineticPoint d → ℝ) (θ : ℝ → ℝ) (hθ : Continuous θ) (hθ0 : ∀ s, 0 ≤ θ s)
    (hu : ContinuousOn u Q) (hg : ContinuousOn g Q) (hg0 : ∀ z ∈ Q, 0 ≤ g z)
    (hbound : ∀ᵐ z ∂(volume.restrict Q), θ (u z) * g z ≤ {w | 0 < u w}.indicator g₀ z)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    ∃ gj : ℕ → KineticPoint d → ℝ, ∀ j : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => gj j ((KineticPoint.equivProd d).symm x)) ∧
      HasCompactSupport (gj j) ∧ tsupport (gj j) ⊆ Q ∧ (∀ z, 0 ≤ gj j z) ∧
      (∀ z ∈ K j, θ (u z) * g z ≤ gj j z) ∧
      (1 ≤ j → eLpNorm (gj j) p (volume.restrict Q) ≤
        eLpNorm ({w | 0 < u w}.indicator g₀) p (volume.restrict Q) +
          ENNReal.ofReal (1 / (j : ℝ))) :=
  exists_smooth_majorant_kinetic_seq hQ hK hKQ
    (h := fun z => θ (u z) * g z) ((hθ.comp_continuousOn hu).mul hg)
    (fun z hz => mul_nonneg (hθ0 _) (hg0 z hz)) hbound hp hpt

end HypoellipticAleksandrov.KineticAleksandrov
