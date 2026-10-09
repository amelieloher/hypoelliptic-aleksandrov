module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Finite-vector `L^p` convergence

This file turns coordinatewise `L^p` convergence of native vector fields into
`L^p` convergence of their explicit Euclidean magnitudes.  The finite
coordinate sum is used only as a convergence majorant; the resulting norm is
the exact Euclidean norm and carries no comparison constant.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

private theorem eLpNorm_abs_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) (p : ℝ≥0∞) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => |f x|) p μ = eLpNorm f p μ := by
  simpa only [Real.norm_eq_abs] using!
    eLpNorm_norm f (p := p) (μ := μ) hf

private theorem aestronglyMeasurable_vecEuclideanNorm_of_coord'
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {F : α → Vec d}
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) μ) :
    AEStronglyMeasurable (fun x => vecEuclideanNorm (F x)) μ := by
  have hsquare (i : Fin d) :
      AEStronglyMeasurable (fun x => (F x i) ^ 2) μ := (hF i).pow 2
  have hsum : AEStronglyMeasurable (fun x => ∑ i : Fin d, (F x i) ^ 2) μ := by
    convert Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hsquare i) using 1
    ext x
    simp
  exact Real.continuous_sqrt.comp_aestronglyMeasurable (by
    simpa only [vecEuclideanNorm, vecNormSq_eq_sum_sq] using hsum)

/-- Coordinatewise `L^p` convergence of native vector fields implies
`L^p` convergence of their explicit Euclidean difference. -/
theorem tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {p : ℝ≥0∞}
    {F : ℕ → α → Vec d} {G : α → Vec d}
    (hp : 1 ≤ p)
    (hMeas :
      ∀ n i,
        AEStronglyMeasurable
          (fun x => F n x i - G x i) μ)
    (hCoordinate :
      ∀ i,
        Filter.Tendsto
          (fun n =>
            eLpNorm (fun x => F n x i - G x i) p μ)
          Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        eLpNorm
          (fun x => vecEuclideanNorm (F n x - G x))
          p μ)
      Filter.atTop (nhds 0) := by
  have hCoordinateAbs :
      ∀ i,
        Filter.Tendsto
          (fun n =>
            eLpNorm (fun x => |F n x i - G x i|) p μ)
          Filter.atTop (nhds 0) := by
    intro i
    have hFunctions :
        (fun n =>
          eLpNorm (fun x => |F n x i - G x i|) p μ) =
        fun n =>
          eLpNorm (fun x => F n x i - G x i) p μ := by
      funext n
      exact
        eLpNorm_abs_eq
          (fun x => F n x i - G x i) p (hMeas n i)
    rw [hFunctions]
    exact hCoordinate i
  have hSum :
      Filter.Tendsto
        (fun n =>
          ∑ i : Fin d,
            eLpNorm (fun x => |F n x i - G x i|) p μ)
        Filter.atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ
        (fun i _hi => hCoordinateAbs i)
  have hBound :
      ∀ n,
        eLpNorm
            (fun x => vecEuclideanNorm (F n x - G x))
            p μ ≤
          ∑ i : Fin d,
            eLpNorm
              (fun x => |F n x i - G x i|)
              p μ := by
    intro n
    calc
      eLpNorm
          (fun x => vecEuclideanNorm (F n x - G x))
          p μ ≤
        eLpNorm
          (fun x =>
            ∑ i : Fin d, |F n x i - G x i|)
          p μ := by
        apply eLpNorm_mono_ae
          (aestronglyMeasurable_vecEuclideanNorm_of_coord'
            (F := fun x => F n x - G x) (hMeas n))
        filter_upwards with x
        have hsumNonneg :
            0 ≤ ∑ i : Fin d, |F n x i - G x i| :=
          Finset.sum_nonneg fun i _hi =>
            abs_nonneg (F n x i - G x i)
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (vecEuclideanNorm_nonneg _),
          abs_of_nonneg hsumNonneg, Pi.sub_apply] using
            vecEuclideanNorm_le_sum_abs (F n x - G x)
      _ ≤
          ∑ i : Fin d,
            eLpNorm
              (fun x => |F n x i - G x i|)
              p μ := by
        rw [← Finset.sum_fn]
        exact
          eLpNorm_sum_le
            (s := Finset.univ)
            (f := fun i x =>
              |F n x i - G x i|)
            (μ := μ) (p := p)
            hp
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hSum
      (fun _ => zero_le) hBound

end PDE
