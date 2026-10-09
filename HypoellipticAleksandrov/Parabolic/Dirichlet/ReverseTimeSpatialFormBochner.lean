module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Bochner action of the reverse-time spatial form

This module packages the continuous clamped local reverse-time spatial-form
operator as a bounded action on quotient-valued Bochner `L²` spaces.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance reverseTimeL2VStarModule
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  Lp.instModule

local instance reverseTimeSpatialFormOperatorNormedAddCommGroup
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := by
  letI : NormedAddCommGroup (H10HilbertGraph hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraph hΩ) := by infer_instance
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := by infer_instance
  infer_instance

private theorem AEStronglyMeasurable.clm_apply
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α}
    (K : α → E →L[ℝ] F) (u : α → E)
    (hK : AEStronglyMeasurable K μ) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => K x (u x)) μ := by
  exact ((ContinuousLinearMap.apply ℝ F).flip).aestronglyMeasurable_comp₂ hK hu

/-- Pointwise representative of the Bochner spatial-form action. -/
noncomputable def reverseTimeSpatialFormBochnerRaw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) : ℝ → H10HilbertGraphDual hΩ := fun τ =>
  reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth τ (u τ)

private theorem aestronglyMeasurable_reverseTimeSpatialFormBochnerRaw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    AEStronglyMeasurable
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u)
    (reverseTimeVolume (r₁ - r₀)) := by
  letI : SecondCountableTopologyEither ℝ
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) :=
    { out := Or.inl (by infer_instance) }
  change AEStronglyMeasurable
    (fun τ => reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ (u τ))
    (reverseTimeVolume (r₁ - r₀))
  exact AEStronglyMeasurable.clm_apply
    (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth)
    u
    (continuous_reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth).aestronglyMeasurable
    (Lp.memLp u).aestronglyMeasurable

private theorem norm_reverseTimeSpatialFormBochnerRaw_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (τ : ℝ) :
    ‖reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u τ‖ ≤ C * ‖u τ‖ := by
  change ‖reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth τ (u τ)‖ ≤ C * ‖u τ‖
  simpa only [reverseTimeSpatialFormOperatorClamp] using
    hC (Set.projIcc 0 (r₁ - r₀) (sub_nonneg.mpr h₀₁.le) τ) (u τ)

/-- The pointwise spatial-form action belongs to reverse-time L². -/
theorem memLp_reverseTimeSpatialFormBochnerRaw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    MemLp (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u) (2 : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀)) := by
  refine (Lp.memLp u).of_le_mul (c := C)
    (aestronglyMeasurable_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u) ?_
  exact Eventually.of_forall
    (norm_reverseTimeSpatialFormBochnerRaw_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u)

/-- The spatial form acting on a reverse-time Bochner curve. -/
noncomputable def reverseTimeSpatialFormBochnerRawAction
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) : ReverseTimeL2VStar hΩ (r₁ - r₀) :=
  (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u).toLp
    (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth u)

/-- The Bochner spatial-form action preserves addition. -/
theorem reverseTimeSpatialFormBochnerRawAction_map_add
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u w : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (u + w) =
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u +
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC w := by
    apply Lp.ext
    filter_upwards [
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC (u + w)).coeFn_toLp,
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u).coeFn_toLp,
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC w).coeFn_toLp,
      Lp.coeFn_add u w,
      Lp.coeFn_add
        (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u)
        (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC w)] with τ hsum hu hw huv hout
    calc
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC (u + w) τ =
          reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth (u + w) τ := hsum
      _ = reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u τ +
          reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth w τ := by
        simp only [reverseTimeSpatialFormBochnerRaw, huv, Pi.add_apply]
        exact (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ).map_add _ _
      _ = reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u τ +
          reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth C hC w τ := by
        change _ =
          (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth C hC u).toLp
              (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth u) τ +
            (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth C hC w).toLp
              (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth w) τ
        rw [← hu, ← hw]
      _ = (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u +
          reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth C hC w) τ := hout.symm

/-- The Bochner spatial-form action preserves scalar multiplication. -/
theorem reverseTimeSpatialFormBochnerRawAction_map_smul
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (q : ℝ) (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (q • u) =
      q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u := by
    apply Lp.ext
    filter_upwards [
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC (q • u)).coeFn_toLp,
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u).coeFn_toLp,
      Lp.coeFn_smul q u,
      Lp.coeFn_smul q
        (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u)] with τ hqu hu hquv hout
    change (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (q • u)).toLp
        (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth (q • u)) τ = _
    rw [hqu]
    calc
      reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth (q • u) τ =
          q • reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth u τ := by
        simp only [reverseTimeSpatialFormBochnerRaw, hquv, Pi.smul_apply]
        exact (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ).map_smul q _
      _ = q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u τ := by
        change _ = q • (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u).toLp
            (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth u) τ
        rw [← hu]
      _ = (q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u) τ := hout.symm

/-- The reverse-time Bochner spatial form as a linear map. -/
noncomputable def reverseTimeSpatialFormBochnerRawLinearMap
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖) :
    ReverseTimeL2V hΩ (r₁ - r₀) →ₗ[ℝ] ReverseTimeL2VStar hΩ (r₁ - r₀) where
  toFun := reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC
  map_add' := reverseTimeSpatialFormBochnerRawAction_map_add r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC
  map_smul' := reverseTimeSpatialFormBochnerRawAction_map_smul r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC

private theorem norm_reverseTimeSpatialFormBochnerRawAction_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ‖reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u).coeFn_toLp] with τ hτ
  change ‖(memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u).toLp
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u) τ‖ ≤ C * ‖u τ‖
  rw [hτ]
  exact norm_reverseTimeSpatialFormBochnerRaw_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u τ

/-- The bounded linear Bochner action of the clamped reverse-time spatial form. -/
noncomputable def reverseTimeSpatialFormBochnerAction
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ReverseTimeL2VStar hΩ (r₁ - r₀) := by
  let C := Classical.choose (exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁ hΩ
    hΩbounded a b c haSmooth hbSmooth hcSmooth)
  let hBound := (Classical.choose_spec (exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁
    hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth)).2
  exact LinearMap.mkContinuous
    (reverseTimeSpatialFormBochnerRawLinearMap r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hBound)
    C
    (by
      intro u
      exact norm_reverseTimeSpatialFormBochnerRawAction_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hBound u)

/-- A coefficient-dependent bound chosen before every Bochner input curve. -/
theorem exists_norm_reverseTimeSpatialFormBochnerAction_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ := exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth
  refine ⟨C, hC, ?_⟩
  unfold reverseTimeSpatialFormBochnerAction
  exact LinearMap.mkContinuous_norm_le _ hC
    (by
      intro u
      exact norm_reverseTimeSpatialFormBochnerRawAction_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hBound u)

/-- One event represents the action simultaneously for all spatial tests. -/
theorem ae_reverseTimeSpatialFormBochnerAction_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ v : H10HilbertGraph hΩ,
      reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u τ v = reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v := by
  obtain ⟨C, hC, hBound⟩ := exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth
  unfold reverseTimeSpatialFormBochnerAction
  filter_upwards [
    (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hBound u).coeFn_toLp,
    ae_reverseTimeSpatialFormOperatorClamp_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth] with τ hRaw hClamp
  intro v
  change reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hBound u τ v = _
  change ((memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hBound u).toLp
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u) τ) v = _
  rw [hRaw]
  exact hClamp (u τ) v

end HypoellipticAleksandrov.Parabolic.Dirichlet
