module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2MultiplierDifference
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Continuity of the reverse-time spatial form operator

This module proves operator-norm continuity for the local operator constructed
in ReverseTimeSpatialFormOperatorBase, using private fresh multiplier evidence
for the finite continuous term curve.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem continuousOn_reverseTimeCoefficientEntry_slice
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (a : CoefficientField d) (i j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ContinuousOn (fun y : PDE.Vec d => a (r₁ - τ) y i j) Ω := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
    exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i j) V := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hrow (by
      intro z hz
      exact Set.mem_univ _)
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro y hy
    exact ⟨htime, subset_closure hy⟩
  simpa only [Function.comp_def] using (hentry.continuousOn.mono hKV).comp
    (Continuous.prodMk_right _).continuousOn hmap

private theorem continuousOn_reverseTimeDivergenceDriftEntry_slice
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    ContinuousOn (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j) Ω := by
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hmap : MapsTo (fun y : PDE.Vec d => (r₁ - τ, y)) Ω
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    intro y hy
    exact ⟨htime, subset_closure hy⟩
  have hdiv : ContinuousOn (fun y : PDE.Vec d =>
      scalarSpatialCoefficientDivergence (reverseTimeCoefficient r₁ a) (τ, y) j) Ω := by
    have hcont := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
      r₀ r₁ a ha
    have hvec : ContinuousOn (fun y : PDE.Vec d =>
        scalarSpatialCoefficientDivergence a (r₁ - τ, y)) Ω := by
      simpa only [Function.comp_def] using hcont.comp (Continuous.prodMk_right _).continuousOn hmap
    have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
      (continuous_apply j).continuousOn
    simpa only [scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
      reverseTimeMap_apply, Function.comp_def] using heval.comp hvec (by intro y hy; simp)
  rcases hb with ⟨V, hVopen, hKV, hV⟩
  have hentry : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  have hbcont : ContinuousOn (fun y : PDE.Vec d => b (r₁ - τ) y j) Ω := by
    simpa only [Function.comp_def] using (hentry.continuousOn.mono hKV).comp
      (Continuous.prodMk_right _).continuousOn hmap
  simpa only [reverseTimeDivergenceDrift, reverseTimeVectorCoefficient_apply,
    Pi.sub_def] using hdiv.sub hbcont

private theorem continuousOn_reverseTimeCoefficientEntry_joint
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (a : CoefficientField d) (i j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩
  have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
    exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  exact ((contDiffOn_apply ℝ ℝ j Set.univ).comp hrow (by
    intro z hz
    simp)).continuousOn.mono hKV

private theorem continuousOn_reverseTimeDivergenceDriftEntry_joint
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (fun z : TimeVelocity d =>
      scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  have hdiv := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
    r₀ r₁ a ha
  have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
    (continuous_apply j).continuousOn
  rcases hb with ⟨V, hVopen, hKV, hV⟩
  have hbj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
    exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV (by
      intro z hz
      exact Set.mem_univ _)
  exact heval.comp hdiv (by intro z hz; simp) |>.sub (hbj.continuousOn.mono hKV)

private theorem continuousOn_reverseTimeScalarCoefficient_joint
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  rcases hc with ⟨V, hVopen, hKV, hV⟩
  exact hV.continuousOn.mono hKV

private theorem exists_delta_ae_norm_reverseTime_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (q : TimeVelocity d → ℝ)
    (hq : ContinuousOn q (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : Set.Icc 0 (r₁ - r₀),
      dist σ τ < δ →
        ∀ᵐ y ∂PDE.volumeOn Ω,
          ‖q (r₁ - σ.1, y) - q (r₁ - τ.1, y)‖ ≤ ε := by
  have hUC : UniformContinuousOn q
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
    IsCompact.uniformContinuousOn_of_continuous
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded) hq
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hδUC⟩ := hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
  have hσK : (r₁ - σ.1, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    ⟨by constructor <;> linarith [σ.2.1, σ.2.2], subset_closure hy⟩
  have hτK : (r₁ - τ.1, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    ⟨by constructor <;> linarith [τ.2.1, τ.2.2], subset_closure hy⟩
  have hdist : dist (r₁ - σ.1, y) (r₁ - τ.1, y) < δ := by
    rw [dist_prod_same_right, Real.dist_eq]
    change |σ.1 - τ.1| < δ at hστ
    rw [show r₁ - σ.1 - (r₁ - τ.1) = τ.1 - σ.1 by ring, abs_sub_comm]
    exact hστ
  exact (hδUC _ hσK _ hτK hdist).le

private theorem continuousAt_reverseTimeCoefficientEntry_multiplier
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (i j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt (fun σ : Set.Icc 0 (r₁ - r₀) =>
      scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
        (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j)) τ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩbounded
    (fun z : TimeVelocity d => a z.1 z.2 i j)
    (continuousOn_reverseTimeCoefficientEntry_joint r₀ r₁ a i j ha) τ (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  rw [dist_eq_norm]
  calc
    ‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
        (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
        scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
          (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖ ≤ ε / 2 :=
      norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
        (fun y => a (r₁ - σ.1) y i j) (fun y => a (r₁ - τ.1) y i j)
        (hAMeas σ i j) (hAMeas τ i j) (Ca i j) (hCa i j) (hABound σ i j)
        (Ca i j) (hCa i j) (hABound τ i j) (ε / 2) (le_of_lt (half_pos hε))
        (by simpa using hsub σ hστ)
    _ < ε := half_lt_self hε

private theorem continuousAt_reverseTimeDivergenceDriftEntry_multiplier
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt (fun σ : Set.Icc 0 (r₁ - r₀) =>
      scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
        (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j)) τ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩbounded
    (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
    (continuousOn_reverseTimeDivergenceDriftEntry_joint r₀ r₁ a b j ha hb) τ (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  rw [dist_eq_norm]
  calc
    ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
        (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
        scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
          (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ ≤ ε / 2 :=
      norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
        (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
        (hDriftMeas σ j) (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound σ j)
        (Cd j) (hCd j) (hDriftBound τ j) (ε / 2) (le_of_lt (half_pos hε))
        (by simpa only [reverseTimeDivergenceDrift,
          scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
          reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, Pi.sub_apply] using
          hsub σ hστ)
    _ < ε := half_lt_self hε

private theorem continuousAt_reverseTimeScalarCoefficient_multiplier
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (c : ℝ → PDE.Vec d → ℝ)
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt (fun σ : Set.Icc 0 (r₁ - r₀) =>
      scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
        (hScalarMeas σ) Cc hCc (hScalarBound σ)) τ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩbounded
    (fun z : TimeVelocity d => c z.1 z.2)
    (continuousOn_reverseTimeScalarCoefficient_joint r₀ r₁ c hc) τ (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  rw [dist_eq_norm]
  calc
    ‖scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
        (hScalarMeas σ) Cc hCc (hScalarBound σ) -
        scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
          (hScalarMeas τ) Cc hCc (hScalarBound τ)‖ ≤ ε / 2 :=
      norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
        (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
        (hScalarMeas σ) (hScalarMeas τ) Cc hCc (hScalarBound σ)
        Cc hCc (hScalarBound τ) (ε / 2) (le_of_lt (half_pos hε))
        (by simpa only [reverseTimeScalarCoefficient_apply] using hsub σ hστ)
    _ < ε := half_lt_self hε

private theorem norm_hilbertVectorLpCoord_le_local
    {d : ℕ} {Ω : Set (PDE.Vec d)} (i : Fin d)
    (G : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞)) :
    ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i G‖ ≤ ‖G‖ := by
  rw [PDE.hilbertVectorLpCoord]
  calc
    ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL
        (2 : ℝ≥0∞) (PDE.volumeOn Ω) G‖ ≤
        ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i‖ * ‖G‖ := by
          exact ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ 1 * ‖G‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply, PiLp.proj_apply, one_mul] using
        PiLp.norm_apply_le x i
    _ = ‖G‖ := one_mul _

private noncomputable def reverseTimeSpatialFormPrincipalTerm
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (i j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v =>
        inner ℝ
          (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)))
      (by
        intro u w v
        simp only [map_add, inner_add_left])
      (by
        intro q u v
        simp only [map_smul, inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul])
      (by
        intro u v w
        simp only [map_add, inner_add_right])
      (by
        intro q u v
        simp only [map_smul, inner_smul_right, smul_eq_mul]))
    (Ca i j * ‖gradientCLM hΩ‖ ^ 2)
    (fun u v => by
      rw [Real.norm_eq_abs]
      have hju :
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖ ≤
            ‖gradientCLM hΩ‖ * ‖u‖ :=
        (norm_hilbertVectorLpCoord_le_local j _).trans
          (ContinuousLinearMap.le_opNorm _ _)
      have hiv :
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ ≤
            ‖gradientCLM hΩ‖ * ‖v‖ :=
        (norm_hilbertVectorLpCoord_le_local i _).trans
          (ContinuousLinearMap.le_opNorm _ _)
      calc
        |inner ℝ
            (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
              (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))| ≤
            ‖scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
              (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))‖ *
              ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Ca i j *
              ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖) *
              ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_scalarL2Multiplier_apply_le _ _ _ _ _ _) (norm_nonneg _)
        _ ≤ (Ca i j * (‖gradientCLM hΩ‖ * ‖u‖)) *
              (‖gradientCLM hΩ‖ * ‖v‖) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hju (hCa i j))
            hiv
            (norm_nonneg _)
            (mul_nonneg (hCa i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (Ca i j * ‖gradientCLM hΩ‖ ^ 2) * ‖u‖ * ‖v‖ := by ring)

private theorem reverseTimeSpatialFormPrincipalTerm_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (i j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ u v =
      inner ℝ
        (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
          (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)) := by
  rw [reverseTimeSpatialFormPrincipalTerm, LinearMap.mkContinuous₂_apply]
  rfl

private theorem reverseTimeSpatialFormPrincipalTerm_sub_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (i j : Fin d) (σ τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    (reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ -
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ) u v =
      inner ℝ
        ((scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)) := by
  rw [ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.sub_apply]
  rw [reverseTimeSpatialFormPrincipalTerm_apply (d := d) (Ω := Ω)
    hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ u v]
  have hτapply :
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ u v =
        inner ℝ
          (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)) := by
    exact reverseTimeSpatialFormPrincipalTerm_apply (d := d) (Ω := Ω)
      hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ u v
  calc
    _ = (inner ℝ
            (scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
              (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))) -
          inner ℝ
            (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
              (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)) :=
      congrArg (fun z : ℝ =>
        inner ℝ
          (scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)) - z) hτapply
    _ = _ := by
      exact (inner_sub_left _ _ _).symm.trans
        (congrArg (fun z => inner ℝ z _)
          (ContinuousLinearMap.sub_apply _ _ _).symm)

private theorem norm_reverseTimeSpatialFormPrincipalTerm_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (i j : Fin d) (σ τ : Set.Icc 0 (r₁ - r₀)) :
    ‖reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ -
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ‖ ≤
      ‖gradientCLM hΩ‖ ^ 2 *
        ‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
  intro u v
  rw [reverseTimeSpatialFormPrincipalTerm_sub_apply (d := d) (Ω := Ω)
    hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ τ u v]
  have hju :
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖ ≤
        ‖gradientCLM hΩ‖ * ‖u‖ :=
    (norm_hilbertVectorLpCoord_le_local j _).trans
      (ContinuousLinearMap.le_opNorm _ _)
  have hiv :
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ ≤
        ‖gradientCLM hΩ‖ * ‖v‖ :=
    (norm_hilbertVectorLpCoord_le_local i _).trans
      (ContinuousLinearMap.le_opNorm _ _)
  calc
    ‖inner ℝ
        ((scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))‖ ≤
        ‖(scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖) *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖ *
          (‖gradientCLM hΩ‖ * ‖u‖)) *
          (‖gradientCLM hΩ‖ * ‖v‖) := by
      gcongr
    _ = (‖gradientCLM hΩ‖ ^ 2 *
          ‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
              (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
            scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
              (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖) * ‖u‖ * ‖v‖ := by
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private noncomputable def reverseTimeSpatialFormDriftTerm
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v =>
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (valueCLM hΩ v))
      (by
        intro u w v
        simp only [map_add, inner_add_left])
      (by
        intro q u v
        simp only [map_smul, inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul])
      (by
        intro u v w
        simp only [map_add, inner_add_right])
      (by
        intro q u v
        simp only [map_smul, inner_smul_right, smul_eq_mul]))
    (Cd j * ‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖)
    (fun u v => by
      rw [Real.norm_eq_abs]
      have hju :
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖ ≤
            ‖gradientCLM hΩ‖ * ‖u‖ :=
        (norm_hilbertVectorLpCoord_le_local j _).trans
          (ContinuousLinearMap.le_opNorm _ _)
      have hv : ‖valueCLM hΩ v‖ ≤ ‖valueCLM hΩ‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      calc
        |inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
              (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
            (valueCLM hΩ v)| ≤
            ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
              (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))‖ *
              ‖valueCLM hΩ v‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Cd j *
              ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖) *
              ‖valueCLM hΩ v‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_scalarL2Multiplier_apply_le _ _ _ _ _ _) (norm_nonneg _)
        _ ≤ (Cd j * (‖gradientCLM hΩ‖ * ‖u‖)) *
              (‖valueCLM hΩ‖ * ‖v‖) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hju (hCd j))
            hv
            (norm_nonneg _)
            (mul_nonneg (hCd j) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (Cd j * ‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖) * ‖u‖ * ‖v‖ := by ring)

private theorem reverseTimeSpatialFormDriftTerm_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ u v =
      inner ℝ
        (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
          (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (valueCLM hΩ v) := by
  rw [reverseTimeSpatialFormDriftTerm, LinearMap.mkContinuous₂_apply]
  rfl

private theorem reverseTimeSpatialFormDriftTerm_sub_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (j : Fin d) (σ τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    (reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ -
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ) u v =
      inner ℝ
        ((scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (valueCLM hΩ v) := by
  rw [ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.sub_apply]
  rw [reverseTimeSpatialFormDriftTerm_apply (d := d) (Ω := Ω)
    hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ u v]
  have hτapply :
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ u v =
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (valueCLM hΩ v) := by
    exact reverseTimeSpatialFormDriftTerm_apply (d := d) (Ω := Ω)
      hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ u v
  calc
    _ = (inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
              (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
            (valueCLM hΩ v)) -
          inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
              (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
            (valueCLM hΩ v) :=
      congrArg (fun z : ℝ =>
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (valueCLM hΩ v) - z) hτapply
    _ = _ := by
      exact (inner_sub_left _ _ _).symm.trans
        (congrArg (fun z => inner ℝ z _)
          (ContinuousLinearMap.sub_apply _ _ _).symm)

private theorem norm_reverseTimeSpatialFormDriftTerm_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (j : Fin d) (σ τ : Set.Icc 0 (r₁ - r₀)) :
    ‖reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ -
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ‖ ≤
      (‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖) *
        ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
  intro u v
  rw [reverseTimeSpatialFormDriftTerm_sub_apply (d := d) (Ω := Ω)
    hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ τ u v]
  have hju :
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖ ≤
        ‖gradientCLM hΩ‖ * ‖u‖ :=
    (norm_hilbertVectorLpCoord_le_local j _).trans
      (ContinuousLinearMap.le_opNorm _ _)
  have hv : ‖valueCLM hΩ v‖ ≤ ‖valueCLM hΩ‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm _ _
  calc
    ‖inner ℝ
        ((scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (valueCLM hΩ v)‖ ≤
        ‖(scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u))‖ *
          ‖valueCLM hΩ v‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖) *
          ‖valueCLM hΩ v‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ *
          (‖gradientCLM hΩ‖ * ‖u‖)) *
          (‖valueCLM hΩ‖ * ‖v‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hju (norm_nonneg _))
        hv
        (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖) *
        ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ * ‖u‖ * ‖v‖ := by
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private noncomputable def reverseTimeSpatialFormScalarTerm
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v =>
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
          (valueCLM hΩ v))
      (by
        intro u w v
        simp only [map_add, inner_add_left])
      (by
        intro q u v
        simp only [map_smul, inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul])
      (by
        intro u v w
        simp only [map_add, inner_add_right])
      (by
        intro q u v
        simp only [map_smul, inner_smul_right, smul_eq_mul]))
    (Cc * ‖valueCLM hΩ‖ ^ 2)
    (fun u v => by
      rw [Real.norm_eq_abs]
      have hu : ‖valueCLM hΩ u‖ ≤ ‖valueCLM hΩ‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hv : ‖valueCLM hΩ v‖ ≤ ‖valueCLM hΩ‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      calc
        |inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
              (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
            (valueCLM hΩ v)| ≤
            ‖scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
              (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u)‖ *
              ‖valueCLM hΩ v‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Cc * ‖valueCLM hΩ u‖) * ‖valueCLM hΩ v‖ := by
          exact mul_le_mul_of_nonneg_right
            (norm_scalarL2Multiplier_apply_le _ _ _ _ _ _) (norm_nonneg _)
        _ ≤ (Cc * (‖valueCLM hΩ‖ * ‖u‖)) *
              (‖valueCLM hΩ‖ * ‖v‖) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hu hCc)
            hv
            (norm_nonneg _)
            (mul_nonneg hCc (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (Cc * ‖valueCLM hΩ‖ ^ 2) * ‖u‖ * ‖v‖ := by ring)

private theorem reverseTimeSpatialFormScalarTerm_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ u v =
      inner ℝ
        (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
          (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
        (valueCLM hΩ v) := by
  rw [reverseTimeSpatialFormScalarTerm, LinearMap.mkContinuous₂_apply]
  rfl

private theorem reverseTimeSpatialFormScalarTerm_sub_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (σ τ : Set.Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    (reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ -
      reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ) u v =
      inner ℝ
        ((scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ))
          (valueCLM hΩ u))
        (valueCLM hΩ v) := by
  rw [ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.sub_apply]
  rw [reverseTimeSpatialFormScalarTerm_apply (d := d) (Ω := Ω)
    hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ u v]
  have hτapply :
      reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ u v =
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
          (valueCLM hΩ v) := by
    exact reverseTimeSpatialFormScalarTerm_apply (d := d) (Ω := Ω)
      hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ u v
  calc
    _ = (inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
              (hScalarMeas σ) Cc hCc (hScalarBound σ) (valueCLM hΩ u))
            (valueCLM hΩ v)) -
          inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
              (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
            (valueCLM hΩ v) :=
      congrArg (fun z : ℝ =>
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) (valueCLM hΩ u))
          (valueCLM hΩ v) - z) hτapply
    _ = _ := by
      exact (inner_sub_left _ _ _).symm.trans
        (congrArg (fun z => inner ℝ z _)
          (ContinuousLinearMap.sub_apply _ _ _).symm)

private theorem norm_reverseTimeSpatialFormScalarTerm_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (c : ℝ → PDE.Vec d → ℝ)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (σ τ : Set.Icc 0 (r₁ - r₀)) :
    ‖reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ -
      reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ‖ ≤
      ‖valueCLM hΩ‖ ^ 2 *
        ‖scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
  intro u v
  rw [reverseTimeSpatialFormScalarTerm_sub_apply (d := d) (Ω := Ω)
    hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ τ u v]
  have hu : ‖valueCLM hΩ u‖ ≤ ‖valueCLM hΩ‖ * ‖u‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hv : ‖valueCLM hΩ v‖ ≤ ‖valueCLM hΩ‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm _ _
  calc
    ‖inner ℝ
        ((scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ))
          (valueCLM hΩ u))
        (valueCLM hΩ v)‖ ≤
        ‖(scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ))
          (valueCLM hΩ u)‖ * ‖valueCLM hΩ v‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ)‖ * ‖valueCLM hΩ u‖) *
          ‖valueCLM hΩ v‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ)‖ *
          (‖valueCLM hΩ‖ * ‖u‖)) * (‖valueCLM hΩ‖ * ‖v‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
        hv
        (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (‖valueCLM hΩ‖ ^ 2 *
        ‖scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y)
            (hScalarMeas τ) Cc hCc (hScalarBound τ)‖) * ‖u‖ * ‖v‖ := by
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem continuousAt_of_norm_sub_le_mul
    {X Y Z : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    {f : X → Y} {g : X → Z} {x : X} (K : ℝ) (hK : 0 ≤ K)
    (hsub : ∀ y, ‖g y - g x‖ ≤ K * ‖f y - f x‖)
    (hf : ContinuousAt f x) : ContinuousAt g x := by
  rw [Metric.continuousAt_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [dist_eq_norm]
  have hyf : ‖f y - f x‖ < ε / (K + 1) := by
    simpa only [dist_eq_norm] using hδf hy
  calc
    ‖g y - g x‖ ≤ K * ‖f y - f x‖ := hsub y
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hyf.le hK
    _ < ε := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ (by linarith)).2 (by nlinarith)

section

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
variable (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
variable (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
variable (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
variable (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
variable (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
variable (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  AEStronglyMeasurable
    (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
variable (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
variable (Cc : ℝ) (hCc : 0 ≤ Cc)
variable (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
  AEStronglyMeasurable
    (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
variable (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)

private theorem continuousAt_reverseTimeSpatialFormPrincipalTerm
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (i j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt
      (reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j) τ := by
  exact continuousAt_of_norm_sub_le_mul
    (f := fun σ => scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
      (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j))
    (g := reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j)
    (‖gradientCLM hΩ‖ ^ 2) (sq_nonneg _)
    (fun σ => norm_reverseTimeSpatialFormPrincipalTerm_sub_le hΩ r₀ r₁ a Ca hCa hAMeas
      hABound i j σ τ)
    (continuousAt_reverseTimeCoefficientEntry_multiplier r₀ r₁ hΩ hΩbounded a haSmooth Ca
      hCa hAMeas hABound i j τ)

private theorem continuousAt_reverseTimeSpatialFormDriftTerm
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt
      (reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j) τ := by
  let f : Set.Icc 0 (r₁ - r₀) →
      PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun σ =>
    scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
      (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j)
  refine continuousAt_of_norm_sub_le_mul (f := f)
    (g := reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j)
    (‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_ ?_
  · intro σ
    simpa only [f] using norm_reverseTimeSpatialFormDriftTerm_sub_le hΩ r₀ r₁ a b Cd hCd
      hDriftMeas hDriftBound j σ τ
  · simpa only [f] using
      (continuousAt_reverseTimeDivergenceDriftEntry_multiplier r₀ r₁ hΩ hΩbounded a b haSmooth
        hbSmooth Cd hCd hDriftMeas hDriftBound j τ)

private theorem continuousAt_reverseTimeSpatialFormScalarTerm
    (hΩbounded : Bornology.IsBounded Ω)
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt
      (reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound) τ := by
  exact continuousAt_of_norm_sub_le_mul
    (f := fun σ => scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
      (hScalarMeas σ) Cc hCc (hScalarBound σ))
    (g := reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound)
    (‖valueCLM hΩ‖ ^ 2) (sq_nonneg _)
    (fun σ => norm_reverseTimeSpatialFormScalarTerm_sub_le hΩ r₀ r₁ c Cc hCc hScalarMeas
      hScalarBound σ τ)
    (continuousAt_reverseTimeScalarCoefficient_multiplier r₀ r₁ hΩ hΩbounded c hcSmooth Cc
      hCc hScalarMeas hScalarBound τ)

private theorem continuous_reverseTimeSpatialFormPrincipalTerm
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (i j : Fin d) :
    Continuous
      (reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j) := by
  exact continuous_iff_continuousAt.2 fun τ =>
    continuousAt_reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound
      hΩbounded haSmooth i j τ

private theorem continuous_reverseTimeSpatialFormDriftTerm
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (j : Fin d) :
    Continuous
      (reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j) := by
  exact continuous_iff_continuousAt.2 fun τ =>
    continuousAt_reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound
      hΩbounded haSmooth hbSmooth j τ

private theorem continuous_reverseTimeSpatialFormScalarTerm
    (hΩbounded : Bornology.IsBounded Ω)
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous
      (reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound) := by
  exact continuous_iff_continuousAt.2 fun τ =>
    continuousAt_reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound
      hΩbounded hcSmooth τ

private noncomputable def reverseTimeSpatialFormTermCurve :
    Set.Icc 0 (r₁ - r₀) → H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  fun τ =>
    (∑ i : Fin d, ∑ j : Fin d,
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ) +
    (∑ j : Fin d,
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ) -
    reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ

private theorem continuousAdd_reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    ContinuousAdd (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := by
  let htop : IsTopologicalAddGroup
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := inferInstance
  exact htop.toContinuousAdd

private theorem continuous_add_sub_explicit
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [AddCommGroup E]
    (hadd : ContinuousAdd E) (hneg : ContinuousNeg E)
    (p q s : X → E)
    (hp : Continuous p) (hq : Continuous q) (hs : Continuous s) :
    Continuous (fun x => p x + q x - s x) := by
  letI : ContinuousAdd E := hadd
  letI : ContinuousNeg E := hneg
  letI : ContinuousSub E := ⟨by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hadd.continuous_add.comp
        (continuous_fst.prodMk (hneg.continuous_neg.comp continuous_snd))⟩
  exact (hp.add hq).sub hs

private theorem continuous_reverseTimeSpatialFormPrincipalSum
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (fun τ =>
      ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ) := by
  exact @continuous_finset_sum (Fin d)
    (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ)
    (Set.Icc 0 (r₁ - r₀)) _ _ ContinuousLinearMap.addCommMonoid
    (continuousAdd_reverseTimeSpatialFormOperator hΩ)
    (fun i τ => ∑ j : Fin d,
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ)
    Finset.univ
    (fun i _ => @continuous_finset_sum (Fin d)
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ)
      (Set.Icc 0 (r₁ - r₀)) _ _ ContinuousLinearMap.addCommMonoid
      (continuousAdd_reverseTimeSpatialFormOperator hΩ)
      (fun j τ => reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ)
      Finset.univ
      (fun j _ => continuous_reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas
        hABound hΩbounded haSmooth i j))

private theorem continuous_reverseTimeSpatialFormDriftSum
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (fun τ =>
      ∑ j : Fin d,
        reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ) := by
  exact @continuous_finset_sum (Fin d)
    (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ)
    (Set.Icc 0 (r₁ - r₀)) _ _ ContinuousLinearMap.addCommMonoid
    (continuousAdd_reverseTimeSpatialFormOperator hΩ)
    (fun j τ => reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ)
    Finset.univ
    (fun j _ => continuous_reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas
      hDriftBound
      hΩbounded haSmooth hbSmooth j)

private theorem continuous_reverseTimeSpatialFormTermCurve
    (hΩbounded : Bornology.IsBounded Ω)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
      hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound) := by
  unfold reverseTimeSpatialFormTermCurve
  let htop : IsTopologicalAddGroup
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := inferInstance
  exact continuous_add_sub_explicit htop.toContinuousAdd htop.toContinuousNeg
    (fun τ => ∑ i : Fin d, ∑ j : Fin d,
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ)
    (fun τ => ∑ j : Fin d,
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ)
    (fun τ => reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ)
    (continuous_reverseTimeSpatialFormPrincipalSum hΩ r₀ r₁ a Ca hCa hAMeas hABound
      hΩbounded haSmooth)
    (continuous_reverseTimeSpatialFormDriftSum hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound
      hΩbounded haSmooth hbSmooth)
    (continuous_reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound
      hΩbounded hcSmooth)

end


section

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
variable (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
variable (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))

section

variable (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
variable (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
variable (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
variable (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
variable (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  AEStronglyMeasurable (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
variable (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
variable (Cc : ℝ) (hCc : 0 ≤ Cc)
variable (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
  AEStronglyMeasurable (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
variable (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)

private theorem reverseTimeSpatialFormOperator_eq_termCurve (τ : Set.Icc 0 (r₁ - r₀)) :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ =
      reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
        hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [reverseTimeSpatialFormOperator_apply]
  simp only [reverseTimeSpatialFormTermCurve, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    reverseTimeSpatialFormPrincipalTerm_apply, reverseTimeSpatialFormDriftTerm_apply,
    reverseTimeSpatialFormScalarTerm_apply]
  exact reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ.1 a b c u v
    Ca hCa (hAMeas τ) (hABound τ) Cd hCd (hDriftMeas τ) (hDriftBound τ) Cc hCc
      (hScalarMeas τ) (hScalarBound τ)

end

end

/-- The local reverse-time spatial operator is continuous in operator norm. -/
theorem continuous_reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth) := by
  obtain ⟨Ca, Cd, Cc, hCa, hCd, hCc, hAMeas, hABound, hDriftMeas, hDriftBound,
    hScalarMeas, hScalarBound⟩ := exists_sliceMultiplierBounds_of_smoothOnNeighborhood r₀ r₁
      hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
  rw [show reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth = reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c
        Ca hCa hAMeas hABound Cd hCd hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound by
    funext τ
    exact reverseTimeSpatialFormOperator_eq_termCurve r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth Ca hCa hAMeas hABound Cd hCd hDriftMeas hDriftBound Cc hCc
      hScalarMeas hScalarBound τ]
  exact continuous_reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
    hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound hΩbounded haSmooth hbSmooth hcSmooth


end HypoellipticAleksandrov.Parabolic.Dirichlet
