module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.SmoothProbeDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalExtension

/-!
# Smooth compactly supported terminal probes

The smooth compactly supported terminal data of an open moving fiber form a real vector
space `terminalProbeSubmodule` of functions on the ambient state.  Restriction to the fiber is
an injective linear map `terminalProbeCc` into `C_c(EvolutionState Ω γ τ, ℝ)` whose range is
closed under squaring and uniformly dense.  A probe vanishes off its fiber.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set
open scoped CompactlySupported ContDiff

variable {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (τ : ℝ)

/-- Smooth compactly supported functions on the ambient state with support in the terminal
fiber, as a real vector space of functions. -/
def terminalProbeSubmodule : Submodule ℝ (EvolutionAmbientState n → ℝ) where
  carrier := {F | ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
    tsupport F ⊆ evolutionStateSet Ω γ τ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := fun {F G} hF hG =>
    ⟨hF.1.add hG.1, hF.2.1.add hG.2.1,
      (tsupport_add F G).trans (union_subset hF.2.2 hG.2.2)⟩
  smul_mem' := fun c F hF =>
    ⟨contDiff_const.smul hF.1, hF.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => c) F).trans hF.2.2⟩

variable {Ω γ τ}

/-- A probe vanishes outside the terminal fiber. -/
theorem terminalProbe_apply_eq_zero (F : terminalProbeSubmodule Ω γ τ)
    {q : EvolutionAmbientState n} (hq : q ∉ evolutionStateSet Ω γ τ) : F.1 q = 0 := by
  by_contra h
  exact hq (F.2.2.2 (subset_tsupport _ h))

/-- The bounded Borel datum underlying a probe. -/
def terminalProbeDatum (F : terminalProbeSubmodule Ω γ τ) :
    BoundedBorel (EvolutionAmbientState n) :=
  ⟨F.1, F.2.1.continuous.measurable, by
    obtain ⟨C, hC⟩ := F.2.2.1.exists_bound_of_continuous F.2.1.continuous
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩⟩

/-- The datum of a probe is a smooth compactly supported terminal datum. -/
theorem terminalProbeDatum_isSmoothCompact (F : terminalProbeSubmodule Ω γ τ) :
    IsSmoothCompactTerminalDatum Ω γ τ (terminalProbeDatum F) := F.2

@[simp]
theorem terminalProbeDatum_apply (F : terminalProbeSubmodule Ω γ τ)
    (q : EvolutionAmbientState n) : terminalProbeDatum F q = F.1 q := rfl

/-- Every smooth compactly supported terminal datum is the datum of a probe. -/
def terminalProbeOfDatum (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) : terminalProbeSubmodule Ω γ τ :=
  ⟨F.1, hF⟩

theorem terminalProbeDatum_ofDatum (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    terminalProbeDatum (terminalProbeOfDatum F hF) = F :=
  BoundedBorel.ext fun _ => rfl

/-- The restriction of a smooth compactly supported function with support in `U` to the
subtype `U` has compact support. -/
theorem hasCompactSupport_comp_subtype_val {E : Type*} [TopologicalSpace E] {U : Set E}
    {F : E → ℝ} (hF : HasCompactSupport F) (hFU : tsupport F ⊆ U) :
    HasCompactSupport (fun x : U => F x) := by
  have hK : IsCompact ((Subtype.val : U → E) ⁻¹' tsupport F) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr hFU]
    exact hF
  refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
  exact closure_minimal (fun x hx => subset_tsupport F hx)
    ((isClosed_tsupport F).preimage continuous_subtype_val)

/-- The restriction of a probe to the terminal fiber, as a compactly supported continuous
function on the open state fiber. -/
def terminalProbeCc (F : terminalProbeSubmodule Ω γ τ) :
    C_c(EvolutionState Ω γ τ, ℝ) where
  toFun x := F.1 x.1
  continuous_toFun := F.2.1.continuous.comp continuous_subtype_val
  hasCompactSupport' := hasCompactSupport_comp_subtype_val F.2.2.1 F.2.2.2

@[simp]
theorem terminalProbeCc_apply (F : terminalProbeSubmodule Ω γ τ)
    (x : EvolutionState Ω γ τ) : terminalProbeCc F x = F.1 x.1 := rfl

/-- Restriction of probes to the terminal fiber, as a linear map. -/
def terminalProbeCcLinear :
    terminalProbeSubmodule Ω γ τ →ₗ[ℝ] C_c(EvolutionState Ω γ τ, ℝ) where
  toFun := terminalProbeCc
  map_add' F G := by ext x; rfl
  map_smul' c F := by ext x; rfl

@[simp]
theorem terminalProbeCcLinear_apply (F : terminalProbeSubmodule Ω γ τ)
    (x : EvolutionState Ω γ τ) : terminalProbeCcLinear F x = F.1 x.1 := rfl

/-- A probe is bounded by `c` everywhere iff its restriction to the fiber is. -/
theorem terminalProbe_abs_le {F : terminalProbeSubmodule Ω γ τ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : EvolutionState Ω γ τ, |terminalProbeCc F x| ≤ c) (q : EvolutionAmbientState n) :
    |F.1 q| ≤ c := by
  by_cases hq : q ∈ evolutionStateSet Ω γ τ
  · exact h ⟨q, hq⟩
  · rw [terminalProbe_apply_eq_zero F hq]; simpa using hc

/-- A probe is nonnegative everywhere iff its restriction to the fiber is. -/
theorem terminalProbe_nonneg {F : terminalProbeSubmodule Ω γ τ}
    (h : ∀ x : EvolutionState Ω γ τ, 0 ≤ terminalProbeCc F x) (q : EvolutionAmbientState n) :
    0 ≤ F.1 q := by
  by_cases hq : q ∈ evolutionStateSet Ω γ τ
  · exact h ⟨q, hq⟩
  · rw [terminalProbe_apply_eq_zero F hq]

/-- Squares of probes are probes, and restrict to the pointwise square. -/
theorem exists_terminalProbe_sq (F : terminalProbeSubmodule Ω γ τ) :
    ∃ G : terminalProbeSubmodule Ω γ τ,
      terminalProbeCcLinear G = terminalProbeCcLinear F * terminalProbeCcLinear F := by
  refine ⟨⟨F.1 * F.1, F.2.1.mul F.2.1, F.2.2.1.mul_left,
    (tsupport_mul_subset_left (f := F.1) (g := F.1)).trans F.2.2.2⟩, ?_⟩
  ext x
  rfl

/-- Smooth probes are uniformly dense among compactly supported continuous tests on the open
fiber (the terminal functional in the `C_c` form). -/
theorem exists_terminalProbe_close (hΩ : IsOpen Ω) (f : C_c(EvolutionState Ω γ τ, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : terminalProbeSubmodule Ω γ τ, ∀ x, |terminalProbeCcLinear F x - f x| ≤ ε := by
  obtain ⟨F, hF, hFf⟩ := exists_smooth_terminal_test_close_of_isOpen hΩ γ τ f ε hε
  exact ⟨terminalProbeOfDatum F hF, hFf⟩

end HypoellipticAleksandrov.KineticAleksandrov
