module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Ring

/-!
# Bounds for the reverse-time spatial form

This module proves boundedness and a Gårding lower estimate for the literal
reverse-time spatial form, always through its explicitly evidenced `L²`
multiplier representation.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem norm_hilbertVectorLpCoord_le
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
      simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply, one_mul, PiLp.proj_apply] using
        PiLp.norm_apply_le x i
    _ = ‖G‖ := one_mul _

private theorem abs_principal_multiplierInner_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    |inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g| ≤ C * ‖f‖ * ‖g‖ := by
  calc
    |inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g| ≤
        ‖scalarL2Multiplier q hq C hC hqBound f‖ * ‖g‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (C * ‖f‖) * ‖g‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_scalarL2Multiplier_apply_le q hq C hC hqBound f) (norm_nonneg _)

private theorem abs_drift_multiplierInner_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    |inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g| ≤ C * ‖f‖ * ‖g‖ :=
  abs_principal_multiplierInner_le q hq C hC hqBound f g

/-- Explicit slice multiplier evidence makes the reverse-time spatial form
bounded on the spatial `H¹₀` Hilbert graph. -/
theorem reverseTimeSpatialForm_bounded_of_sliceMultiplierBounds
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ)
    (hCa : ∀ i j, 0 ≤ Ca i j) (hCd : ∀ j, 0 ≤ Cd j) (hCc : 0 ≤ Cc)
    (hAMeas : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ i j,
      AEStronglyMeasurable (fun y : PDE.Vec d => a (r₁ - τ) y i j)
        (PDE.volumeOn Ω))
    (hABound : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hDriftMeas : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ j,
      AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
        (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (hScalarMeas : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
        (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u v : H10HilbertGraph hΩ,
        |reverseTimeSpatialForm hΩ r₁ τ a b c u v| ≤ C * ‖u‖ * ‖v‖ := by
  let G : ℝ := ‖gradientCLM hΩ‖
  let V : ℝ := ‖valueCLM hΩ‖
  let C : ℝ := (∑ i : Fin d, ∑ j : Fin d, Ca i j) * G ^ 2 +
    (∑ j : Fin d, Cd j) * G * V + Cc * V ^ 2
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => hCa i j) (sq_nonneg _)
      · exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => hCd j)
          (norm_nonneg _)) (norm_nonneg _)
    · exact mul_nonneg hCc (sq_nonneg _)
  intro τ hτ u v
  have hgu (i : Fin d) :
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u)‖ ≤
        G * ‖u‖ := by
    calc
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u)‖ ≤
          ‖gradientCLM hΩ u‖ := norm_hilbertVectorLpCoord_le i _
      _ ≤ G * ‖u‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
  have hgv (i : Fin d) :
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ ≤
        G * ‖v‖ := by
    calc
      ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ ≤
          ‖gradientCLM hΩ v‖ := norm_hilbertVectorLpCoord_le i _
      _ ≤ G * ‖v‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
  have hvv : ‖valueCLM hΩ v‖ ≤ V * ‖v‖ := by
    exact ContinuousLinearMap.le_opNorm _ _
  have hvu : ‖valueCLM hΩ u‖ ≤ V * ‖u‖ := by
    exact ContinuousLinearMap.le_opNorm _ _
  have hprincipal (i j : Fin d) :
      |inner ℝ
        (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
          (hAMeas τ hτ i j) (Ca i j) (hCa i j) (hABound τ hτ i j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))| ≤
        Ca i j * G ^ 2 * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ Ca i j *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v)‖ :=
        abs_principal_multiplierInner_le _ _ _ _ _ _ _
      _ ≤ Ca i j * (G * ‖u‖) * (G * ‖v‖) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hgu j) (hCa i j)
        · exact hgv i
        · exact norm_nonneg _
        · exact mul_nonneg (hCa i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = Ca i j * G ^ 2 * ‖u‖ * ‖v‖ := by ring
  have hdrift (j : Fin d) :
      |inner ℝ
        (scalarL2Multiplier
          (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
          (hDriftMeas τ hτ j) (Cd j) (hCd j) (hDriftBound τ hτ j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (valueCLM hΩ v)| ≤ Cd j * G * V * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ Cd j *
          ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)‖ *
          ‖valueCLM hΩ v‖ := abs_drift_multiplierInner_le _ _ _ _ _ _ _
      _ ≤ Cd j * (G * ‖u‖) * (V * ‖v‖) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hgu j) (hCd j)
        · exact hvv
        · exact norm_nonneg _
        · exact mul_nonneg (hCd j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = Cd j * G * V * ‖u‖ * ‖v‖ := by ring
  have hscalar :
      |inner ℝ
        (scalarL2Multiplier (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
          (hScalarMeas τ hτ) Cc hCc (hScalarBound τ hτ) (valueCLM hΩ u))
        (valueCLM hΩ v)| ≤ Cc * V ^ 2 * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ Cc * ‖valueCLM hΩ u‖ * ‖valueCLM hΩ v‖ :=
        abs_principal_multiplierInner_le _ _ _ _ _ _ _
      _ ≤ Cc * (V * ‖u‖) * (V * ‖v‖) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hvu hCc
        · exact hvv
        · exact norm_nonneg _
        · exact mul_nonneg hCc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = Cc * V ^ 2 * ‖u‖ * ‖v‖ := by ring
  rw [reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ a b c u v
    Ca hCa (hAMeas τ hτ) (hABound τ hτ) Cd hCd (hDriftMeas τ hτ)
    (hDriftBound τ hτ) Cc hCc (hScalarMeas τ hτ) (hScalarBound τ hτ)]
  calc
    |(∑ i : Fin d, ∑ j : Fin d,
      inner ℝ
        (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
          (hAMeas τ hτ i j) (Ca i j) (hCa i j) (hABound τ hτ i j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))) +
      (∑ j : Fin d,
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
            (hDriftMeas τ hτ j) (Cd j) (hCd j) (hDriftBound τ hτ j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (valueCLM hΩ v)) -
      inner ℝ
        (scalarL2Multiplier (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
          (hScalarMeas τ hτ) Cc hCc (hScalarBound τ hτ) (valueCLM hΩ u))
        (valueCLM hΩ v)| ≤
        (∑ i : Fin d, ∑ j : Fin d, Ca i j * G ^ 2 * ‖u‖ * ‖v‖) +
          (∑ j : Fin d, Cd j * G * V * ‖u‖ * ‖v‖) +
          Cc * V ^ 2 * ‖u‖ * ‖v‖ := by
      calc
        _ ≤ |∑ i : Fin d, ∑ j : Fin d,
            inner ℝ
              (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
                (hAMeas τ hτ i j) (Ca i j) (hCa i j) (hABound τ hτ i j)
                (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))| +
            |∑ j : Fin d,
              inner ℝ
                (scalarL2Multiplier
                  (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
                  (hDriftMeas τ hτ j) (Cd j) (hCd j) (hDriftBound τ hτ j)
                  (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
                (valueCLM hΩ v)| +
            |inner ℝ
              (scalarL2Multiplier
                (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
                (hScalarMeas τ hτ) Cc hCc (hScalarBound τ hτ) (valueCLM hΩ u))
              (valueCLM hΩ v)| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ (∑ i : Fin d, ∑ j : Fin d,
            |inner ℝ
              (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
                (hAMeas τ hτ i j) (Ca i j) (hCa i j) (hABound τ hτ i j)
                (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ v))|) +
            (∑ j : Fin d,
              |inner ℝ
                (scalarL2Multiplier
                  (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
                  (hDriftMeas τ hτ j) (Cd j) (hCd j) (hDriftBound τ hτ j)
                  (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
                (valueCLM hΩ v)|) +
            |inner ℝ
              (scalarL2Multiplier
                (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
                (hScalarMeas τ hτ) Cc hCc (hScalarBound τ hτ) (valueCLM hΩ u))
              (valueCLM hΩ v)| := by
          apply add_le_add
          · apply add_le_add
            · calc
                |∑ i : Fin d, ∑ j : Fin d,
                    inner ℝ
                      (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
                        (hAMeas τ hτ i j) (Ca i j) (hCa i j) (hABound τ hτ i j)
                        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
                          (gradientCLM hΩ u)))
                      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
                        (gradientCLM hΩ v))| ≤
                    ∑ i : Fin d, |∑ j : Fin d,
                      inner ℝ
                        (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
                          (hAMeas τ hτ i j) (Ca i j) (hCa i j) (hABound τ hτ i j)
                          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
                            (gradientCLM hΩ u)))
                        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
                          (gradientCLM hΩ v))| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
            · exact Finset.abs_sum_le_sum_abs _ _
          · exact le_rfl
        _ ≤ _ := by
          apply add_le_add
          · apply add_le_add
            · exact Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun j _ => hprincipal i j
            · exact Finset.sum_le_sum fun j _ => hdrift j
          · exact hscalar
    _ = C * ‖u‖ * ‖v‖ := by
      dsimp only [C]
      simp_rw [← Finset.sum_mul]
      ring

private theorem principal_lower_of_loewner
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam τ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (u : H10HilbertGraph hΩ)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ i j, AEStronglyMeasurable (fun y : PDE.Vec d => a (r₁ - τ) y i j)
      (PDE.volumeOn Ω))
    (hABound : ∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    lam * ‖gradientCLM hΩ u‖ ^ 2 ≤
      ∑ i : Fin d, ∑ j : Fin d,
        inner ℝ
          (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
            (hAMeas i j) (Ca i j) (hCa i j) (hABound i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u)) := by
  let G := gradientCLM hΩ u
  have hcoord (i : Fin d) : MemLp (fun y : PDE.Vec d => G y i) (2 : ℝ≥0∞)
      (PDE.volumeOn Ω) :=
    MeasureTheory.MemLp.ae_eq (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i G)
      (Lp.memLp _)
  have hterm (i j : Fin d) : Integrable
      (fun y : PDE.Vec d => a (r₁ - τ) y i j * G y j * G y i) (PDE.volumeOn Ω) := by
    have hprod := (hcoord j).integrable_mul (hcoord i)
    have hbounded := hprod.mul_bdd (hAMeas i j) (hABound i j)
    convert hbounded using 1
    ext y
    simp only [Pi.mul_apply]
    ring
  have hsum : Integrable (fun y : PDE.Vec d => ∑ i : Fin d, ∑ j : Fin d,
      a (r₁ - τ) y i j * G y j * G y i) (PDE.volumeOn Ω) := by
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    exact hterm i j
  have hgrad : Integrable (fun y : PDE.Vec d => lam * ‖G y‖ ^ 2)
      (PDE.volumeOn Ω) := by
    have hinner := L2.integrable_inner (𝕜 := ℝ) G G
    have : Integrable (fun y : PDE.Vec d => ‖G y‖ ^ 2) (PDE.volumeOn Ω) := by
      simpa only [real_inner_self_eq_norm_sq] using hinner
    exact this.const_mul lam
  have hpoint : ∀ y : PDE.Vec d, y ∈ Ω →
      lam * ‖G y‖ ^ 2 ≤ ∑ i : Fin d, ∑ j : Fin d,
        a (r₁ - τ) y i j * G y j * G y i := by
    intro y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [hτ.1, hτ.2]
    have hlo := hLower (r₁ - τ, y) ⟨htime, subset_closure hy⟩
    have hgap : (a (r₁ - τ) y - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hlo
    have hquad := hgap.dotProduct_mulVec_nonneg (G y).toVec
    have hquad' : lam * PDE.vecNormSq (G y).toVec ≤
        PDE.vecDot (G y).toVec (Matrix.mulVec (a (r₁ - τ) y) (G y).toVec) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul] at hquad
      simpa [PDE.vecNormSq, HypoellipticAleksandrov.vecDot_eq_dotProduct,
        sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using sub_nonneg.mp hquad
    simpa [PDE.HilbertVec.norm_eq_vecEuclideanNorm, PDE.vecEuclideanNorm_sq,
      PDE.vecNormSq_eq_sum_sq, PDE.vecDot, dotProduct, Matrix.mulVec, Finset.mul_sum,
      PDE.HilbertVec.toVec_apply, mul_comm, mul_left_comm, mul_assoc] using hquad'
  have hmono : (∫ y, lam * ‖G y‖ ^ 2 ∂PDE.volumeOn Ω) ≤
      ∫ y, ∑ i : Fin d, ∑ j : Fin d, a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω := by
    apply integral_mono_ae hgrad hsum
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    exact hpoint y hy
  have hgrad_eq : (∫ y, lam * ‖G y‖ ^ 2 ∂PDE.volumeOn Ω) = lam * ‖G‖ ^ 2 := by
    rw [integral_const_mul, ← real_inner_self_eq_norm_sq G, L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    exact (real_inner_self_eq_norm_sq (G y)).symm
  rw [← hgrad_eq]
  refine hmono.trans_eq ?_
  calc
    (∫ y, ∑ i : Fin d, ∑ j : Fin d,
        a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω) =
      ∑ i : Fin d, ∫ y, ∑ j : Fin d,
        a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω := by
          apply integral_finset_sum
          intro i _
          apply integrable_finset_sum
          intro j _
          exact hterm i j
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ y,
        a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_finset_sum _ (fun j _ => hterm i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [scalarL2Multiplier_apply_ae _ _ _ _ _ _,
        PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G,
        PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i G] with y hm hj hi
      rw [hm, hj, hi]
      simp only [RCLike.inner_apply, conj_trivial]
      ring

private theorem drift_lower_of_sliceMultiplierBounds
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ j, AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
      (PDE.volumeOn Ω))
    (hDriftBound : ∀ j, ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (u : H10HilbertGraph hΩ) :
    -((∑ j : Fin d, Cd j) * ‖gradientCLM hΩ u‖ * ‖valueCLM hΩ u‖) ≤
      ∑ j : Fin d,
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
            (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (valueCLM hΩ u) := by
  let G := gradientCLM hΩ u
  let U := valueCLM hΩ u
  have hcoord (j : Fin d) : ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ ≤ ‖G‖ :=
    norm_hilbertVectorLpCoord_le j G
  have hterm (j : Fin d) :
      |inner ℝ
        (scalarL2Multiplier
          (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
          (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G)) U| ≤
        Cd j * ‖G‖ * ‖U‖ := by
    calc
      _ ≤ Cd j * ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ * ‖U‖ :=
        abs_drift_multiplierInner_le _ _ _ _ _ _ _
      _ ≤ Cd j * ‖G‖ * ‖U‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoord j) (hCd j)) (norm_nonneg _)
  let B := ∑ j : Fin d,
    inner ℝ
      (scalarL2Multiplier
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
        (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G)) U
  have habs : |B| ≤ (∑ j : Fin d, Cd j) * ‖G‖ * ‖U‖ := by
    calc
      |B| ≤ ∑ j : Fin d,
          |inner ℝ
            (scalarL2Multiplier
              (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
              (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G)) U| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d, Cd j * ‖G‖ * ‖U‖ := Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j : Fin d, Cd j) * ‖G‖ * ‖U‖ := by
        simp_rw [← Finset.sum_mul]
  change -((∑ j : Fin d, Cd j) * ‖G‖ * ‖U‖) ≤ B
  exact (neg_le_neg habs).trans (neg_abs_le B)

private theorem scalar_multiplierInner_nonpos_of_nonpos
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ τ : ℝ) (hΩ : IsOpen Ω) (c : ℝ → PDE.Vec d → ℝ)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
      (PDE.volumeOn Ω))
    (hScalarBound : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ) :
    inner ℝ
      (scalarL2Multiplier (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
        hScalarMeas Cc hCc hScalarBound (valueCLM hΩ u))
      (valueCLM hΩ u) ≤ 0 := by
  let U := valueCLM hΩ u
  let q := fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hq : ∀ᵐ y ∂PDE.volumeOn Ω, q y ≤ 0 := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa only [q, reverseTimeScalarCoefficient_apply] using
      hcNonpos (r₁ - τ, y) ⟨htime, subset_closure hy⟩
  have hint : Integrable (fun y : PDE.Vec d => q y * U y * U y) (PDE.volumeOn Ω) := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (scalarL2Multiplier q hScalarMeas Cc hCc hScalarBound U) U).congr ?_
    filter_upwards [scalarL2Multiplier_apply_ae q hScalarMeas Cc hCc hScalarBound U] with y hy
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hnonpos : (∫ y, q y * U y * U y ∂PDE.volumeOn Ω) ≤ 0 := by
    rw [← integral_zero]
    apply integral_mono_ae hint (integrable_zero (PDE.Vec d) ℝ (PDE.volumeOn Ω))
    filter_upwards [hq] with y hy
    have hm := mul_nonpos_of_nonpos_of_nonneg hy (sq_nonneg (U y))
    simpa only [pow_two, mul_assoc, Pi.zero_apply] using hm
  rw [L2.inner_def]
  calc
    (∫ y, inner ℝ
        ((scalarL2Multiplier q hScalarMeas Cc hCc hScalarBound U) y) (U y)
        ∂PDE.volumeOn Ω) = ∫ y, q y * U y * U y ∂PDE.volumeOn Ω := by
          apply integral_congr_ae
          filter_upwards [scalarL2Multiplier_apply_ae q hScalarMeas Cc hCc hScalarBound U] with y hy
          rw [hy]
          simp only [RCLike.inner_apply, conj_trivial]
          ring
    _ ≤ 0 := hnonpos

private theorem garding_young
    (lam D G U : ℝ) (hlam : 0 < lam) :
    (lam / 2) * G ^ 2 - (D ^ 2 / (2 * lam)) * U ^ 2 ≤
      lam * G ^ 2 - D * G * U := by
  field_simp
  nlinarith [sq_nonneg (lam * G - D * U)]

/-- Explicit slice multiplier evidence and a local Loewner lower bound give a
uniform reverse-time spatial Gårding estimate. -/
theorem reverseTimeSpatialForm_garding_of_sliceMultiplierBounds
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (hlam : 0 < lam) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (Ca : Fin d → Fin d → ℝ) (Cd : Fin d → ℝ) (Cc : ℝ)
    (hCa : ∀ i j, 0 ≤ Ca i j) (hCd : ∀ j, 0 ≤ Cd j) (hCc : 0 ≤ Cc)
    (hAMeas : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ i j,
      AEStronglyMeasurable (fun y : PDE.Vec d => a (r₁ - τ) y i j)
        (PDE.volumeOn Ω))
    (hABound : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hDriftMeas : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ j,
      AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
        (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) → ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (hScalarMeas : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      AEStronglyMeasurable
        (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
        (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ᵐ y ∂PDE.volumeOn Ω,
        ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc)
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u : H10HilbertGraph hΩ,
        (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
          K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u := by
  let D : ℝ := ∑ j : Fin d, Cd j
  refine ⟨D ^ 2 / (2 * lam), div_nonneg (sq_nonneg _) (by positivity), ?_⟩
  intro τ hτ u
  have hprincipal := principal_lower_of_loewner r₀ r₁ lam τ hΩ a u Ca hCa
    (hAMeas τ hτ) (hABound τ hτ) hLower hτ
  have hdrift := drift_lower_of_sliceMultiplierBounds hΩ r₁ τ a b Cd hCd
    (hDriftMeas τ hτ) (hDriftBound τ hτ) u
  have hscalar := scalar_multiplierInner_nonpos_of_nonpos r₀ r₁ τ hΩ c Cc hCc
    (hScalarMeas τ hτ) (hScalarBound τ hτ) hcNonpos hτ u
  rw [reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ a b c u u
    Ca hCa (hAMeas τ hτ) (hABound τ hτ) Cd hCd (hDriftMeas τ hτ)
    (hDriftBound τ hτ) Cc hCc (hScalarMeas τ hτ) (hScalarBound τ hτ)]
  have hyoung := garding_young lam D ‖gradientCLM hΩ u‖ ‖valueCLM hΩ u‖ hlam
  change (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
      (D ^ 2 / (2 * lam)) * ‖valueCLM hΩ u‖ ^ 2 ≤ _
  linarith

private theorem continuousOn_reverseTimeCoefficientEntry_slice_of_smoothOnNeighborhood
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

private theorem continuousOn_reverseTimeDivergenceDriftEntry_slice_of_smoothOnNeighborhood
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
  exact hdiv.sub hbcont

/-- Smooth coefficients on a bounded closed cylinder give a bounded reverse-time
spatial form. -/
theorem reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u v : H10HilbertGraph hΩ,
        |reverseTimeSpatialForm hΩ r₁ τ a b c u v| ≤ C * ‖u‖ * ‖v‖ := by
  have haCont (i j : Fin d) : ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    rcases haSmooth with ⟨V, hVopen, hKV, hV⟩
    have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
      exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV
        (by intro z hz; exact Set.mem_univ _)
    exact ((contDiffOn_apply ℝ ℝ j Set.univ).comp hrow
      (by intro z hz; exact Set.mem_univ _)).continuousOn.mono hKV
  choose ca hca using fun i j =>
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (haCont i j)
  let Ca : Fin d → Fin d → ℝ := fun i j => max (ca i j) 0
  have hCa (i j : Fin d) : 0 ≤ Ca i j := le_max_right _ _
  have hCaBound (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (i j : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [h₀₁, hτ.1, hτ.2]
    exact (hca i j (r₁ - τ, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  have hCdCont (j : Fin d) : ContinuousOn
      (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    have hdiv := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
      r₀ r₁ a haSmooth
    have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
      (continuous_apply j).continuousOn
    rcases hbSmooth with ⟨V, hVopen, hKV, hV⟩
    have hbj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV
        (by intro z hz; exact Set.mem_univ _)
    exact heval.comp hdiv (by intro z hz; exact Set.mem_univ _) |>.sub (hbj.continuousOn.mono hKV)
  choose cd hcd using fun j =>
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hCdCont j)
  let Cd : Fin d → ℝ := fun j => max (cd j) 0
  have hCd (j : Fin d) : 0 ≤ Cd j := le_max_right _ _
  have hCdBound (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (j : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [h₀₁, hτ.1, hτ.2]
    simpa only [reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
      reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, Pi.sub_apply,
      Function.comp_def] using
      (hcd j (r₁ - τ, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  obtain ⟨Cc, hCc, hCcBound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood r₀ r₁ hΩbounded c hcSmooth
  exact reverseTimeSpatialForm_bounded_of_sliceMultiplierBounds r₀ r₁ hΩ a b c Ca Cd Cc hCa hCd hCc
    (fun τ hτ i j =>
      ContinuousOn.aestronglyMeasurable
        (continuousOn_reverseTimeCoefficientEntry_slice_of_smoothOnNeighborhood r₀ r₁ τ a i j
          haSmooth hτ) hΩ.measurableSet)
    hCaBound
    (fun τ hτ j =>
      (continuousOn_reverseTimeDivergenceDriftEntry_slice_of_smoothOnNeighborhood r₀ r₁ τ a b j
        haSmooth hbSmooth hτ).aestronglyMeasurable hΩ.measurableSet)
    hCdBound
    (fun τ hτ =>
      ContinuousOn.aestronglyMeasurable
        (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood r₀ r₁ τ c hcSmooth
          hτ) hΩ.measurableSet)
    (fun τ hτ => by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
      simpa only [Real.norm_eq_abs] using hCcBound τ hτ y hy)

/-- Smooth coefficients on a bounded closed cylinder and a local lower
Loewner bound give a reverse-time spatial Gårding estimate. -/
theorem reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u : H10HilbertGraph hΩ,
        (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
          K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u := by
  have haCont (i j : Fin d) : ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    rcases haSmooth with ⟨V, hVopen, hKV, hV⟩
    have hrow : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) V := by
      exact (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV
        (by intro z hz; exact Set.mem_univ _)
    exact ((contDiffOn_apply ℝ ℝ j Set.univ).comp hrow
      (by intro z hz; exact Set.mem_univ _)).continuousOn.mono hKV
  choose ca hca using fun i j =>
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (haCont i j)
  let Ca : Fin d → Fin d → ℝ := fun i j => max (ca i j) 0
  have hCa (i j : Fin d) : 0 ≤ Ca i j := le_max_right _ _
  have hCaBound (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (i j : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [h₀₁, hτ.1, hτ.2]
    exact (hca i j (r₁ - τ, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  have hCdCont (j : Fin d) : ContinuousOn
      (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
    have hdiv := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
      r₀ r₁ a haSmooth
    have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
      (continuous_apply j).continuousOn
    rcases hbSmooth with ⟨V, hVopen, hKV, hV⟩
    have hbj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) V := by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV
        (by intro z hz; exact Set.mem_univ _)
    exact heval.comp hdiv (by intro z hz; exact Set.mem_univ _) |>.sub (hbj.continuousOn.mono hKV)
  choose cd hcd using fun j =>
    (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded).exists_bound_of_continuousOn
      (hCdCont j)
  let Cd : Fin d → ℝ := fun j => max (cd j) 0
  have hCd (j : Fin d) : 0 ≤ Cd j := le_max_right _ _
  have hCdBound (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (j : Fin d) :
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [h₀₁, hτ.1, hτ.2]
    simpa only [reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
      reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, Pi.sub_apply,
      Function.comp_def] using
      (hcd j (r₁ - τ, y) ⟨htime, subset_closure hy⟩).trans (le_max_left _ _)
  obtain ⟨Cc, hCc, hCcBound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood r₀ r₁ hΩbounded c hcSmooth
  exact reverseTimeSpatialForm_garding_of_sliceMultiplierBounds r₀ r₁ lam hlam hΩ a b c
    Ca Cd Cc hCa hCd hCc
    (fun τ hτ i j =>
      (continuousOn_reverseTimeCoefficientEntry_slice_of_smoothOnNeighborhood r₀ r₁ τ a i j
        haSmooth hτ).aestronglyMeasurable hΩ.measurableSet)
    hCaBound
    (fun τ hτ j =>
      (continuousOn_reverseTimeDivergenceDriftEntry_slice_of_smoothOnNeighborhood r₀ r₁ τ a b j
        haSmooth hbSmooth hτ).aestronglyMeasurable hΩ.measurableSet)
    hCdBound
    (fun τ hτ =>
      (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood r₀ r₁ τ c hcSmooth
        hτ).aestronglyMeasurable hΩ.measurableSet)
    (fun τ hτ => by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
      simpa only [Real.norm_eq_abs] using hCcBound τ hτ y hy)
    hLower hcNonpos

/-- The full smooth Dirichlet coefficient package supplies both reverse-time
spatial form bounds. -/
theorem exists_reverseTimeSpatialForm_bounds_of_dirichletData
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam Lam : ℝ) (h₀₁ : r₀ < r₁)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      (∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
        ∀ u v : H10HilbertGraph hΩ,
          |reverseTimeSpatialForm hΩ r₁ τ a b c u v| ≤ C * ‖u‖ * ‖v‖) ∧
      (∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
        ∀ u : H10HilbertGraph hΩ,
          (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
            K * ‖valueCLM hΩ u‖ ^ 2 ≤
          reverseTimeSpatialForm hΩ r₁ τ a b c u u) := by
  obtain ⟨C, hC, hbounded⟩ :=
    reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth
  obtain ⟨K, hK, hgarding⟩ :=
    reverseTimeSpatialForm_garding_of_smoothOnNeighborhood r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth hLower hcNonpos
  exact ⟨C, K, hC, hK, hbounded, hgarding⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
