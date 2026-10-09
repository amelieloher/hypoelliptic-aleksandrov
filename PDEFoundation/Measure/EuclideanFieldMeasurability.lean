module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-! # Measurability of Euclidean magnitudes from native coordinates -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- Coordinatewise almost-everywhere strong measurability implies the same
for the explicit Euclidean magnitude. -/
theorem aestronglyMeasurable_vecEuclideanNorm_of_coord
    {d : ℕ} {μ : Measure (Vec d)} {F : Vec d → Vec d}
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

end PDE
