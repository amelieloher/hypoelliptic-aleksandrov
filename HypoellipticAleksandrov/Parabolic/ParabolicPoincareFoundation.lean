module

public import Mathlib.Analysis.Normed.Group.Bounded
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm

/-!
# Normalized parabolic moment-projection foundation

This file fixes the unit forward coordinate box and its canonical
time-independent velocity-affine moment projection for the parabolic Morrey
program. It also proves that every globally continuous scalar field has a
genuine finite restricted `L^(d + 1)` norm on that box.

## Main definitions

* `parabolicMorreyUnitBox` is the literal box `(0, 1) × (-1, 1)^d`.
* `parabolicMorreyUnitAverage` is its ordinary volume average.
* `parabolicMorreyUnitVelocityCoeff` is the moment coefficient with the
  normalization factor `3`.
* `parabolicMorreyUnitAffineProjection` is the resulting velocity-affine
  polynomial.

## Main results

* The unit box has positive finite volume, with real value `2 ^ d`.
* `Continuous.memLp_parabolicMorreyUnitBox` gives honest restricted
  `L^(d + 1)` membership without a compact-support premise.

This module proves no Poincare, Morrey, Campanato, representative, or PDE
estimate.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

/-- The literal forward unit coordinate box used by the affine Poincare node. -/
def parabolicMorreyUnitBox (d : ℕ) : Set (TimeVelocity d) :=
  parabolicBox 1 1 0 0

/-- The ordinary volume average on the fixed unit coordinate box. -/
noncomputable def parabolicMorreyUnitAverage {d : ℕ}
    (f : TimeVelocity d → ℝ) : ℝ :=
  ((volume (parabolicMorreyUnitBox d)).toReal)⁻¹ *
    ∫ z in parabolicMorreyUnitBox d, f z

/-- The moment-defined coefficient of `v_i` in the unit-box affine projection. -/
noncomputable def parabolicMorreyUnitVelocityCoeff {d : ℕ}
    (f : TimeVelocity d → ℝ) (i : Fin d) : ℝ :=
  3 * parabolicMorreyUnitAverage fun z => f z * z.2 i

/-- The fixed unit-box projection onto functions constant in time and affine in velocity. -/
noncomputable def parabolicMorreyUnitAffineProjection {d : ℕ}
    (f : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  fun z => parabolicMorreyUnitAverage f +
    ∑ i : Fin d, parabolicMorreyUnitVelocityCoeff f i * z.2 i

/-- The real volume of the literal unit box is `2 ^ d`. -/
theorem volume_parabolicMorreyUnitBox_toReal (d : ℕ) :
    (volume (parabolicMorreyUnitBox d)).toReal = (2 : ℝ) ^ d := by
  simpa only [parabolicMorreyUnitBox, one_mul, one_pow, mul_one]
    using
      (volume_parabolicBox_toReal (d := d) (vartheta := (1 : ℝ)) (r := (1 : ℝ))
        (t₀ := (0 : ℝ)) (v₀ := (0 : PDE.Vec d)) (by norm_num) (by norm_num))

/-- The literal unit coordinate box has positive real volume. -/
theorem volume_parabolicMorreyUnitBox_toReal_pos (d : ℕ) :
    0 < (volume (parabolicMorreyUnitBox d)).toReal := by
  rw [volume_parabolicMorreyUnitBox_toReal]
  exact pow_pos (by norm_num) _

/-- The literal unit coordinate box has finite volume. -/
theorem volume_parabolicMorreyUnitBox_ne_top (d : ℕ) :
    volume (parabolicMorreyUnitBox d) ≠ ∞ := by
  intro htop
  have hzero : (volume (parabolicMorreyUnitBox d)).toReal = 0 := by
    simp only [htop, ENNReal.toReal_top]
  exact (volume_parabolicMorreyUnitBox_toReal_pos d).ne' hzero

/-- A globally continuous scalar field has finite `L^(d + 1)` norm on the
literal open unit box, without any compact-support assumption. -/
theorem Continuous.memLp_parabolicMorreyUnitBox {d : ℕ}
    {f : TimeVelocity d → ℝ} (hf : Continuous f) :
    MemLp f (parabolicExponent d)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  let K : Set (TimeVelocity d) :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact : IsCompact K :=
    isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKmeasurable : MeasurableSet K := hKcompact.measurableSet
  have hunitSubset : parabolicMorreyUnitBox d ⊆ K := by
    rintro ⟨t, v⟩ hz
    change (t, v) ∈ parabolicBox 1 1 0 0 at hz
    change (t, v) ∈ parabolicClosedBox 1 1 0 0
    rcases hz with ⟨⟨htLeft, htRight⟩, hv⟩
    exact ⟨⟨htLeft.le, htRight.le⟩, fun i => (hv i).le⟩
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn hKcompact hf.continuousOn
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  have hfK : MemLp f (parabolicExponent d) (volume.restrict K) := by
    refine MemLp.of_bound hf.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hKmeasurable] with z hz
    exact hC z hz
  exact hfK.mono_measure (Measure.restrict_mono_set volume hunitSubset)

end HypoellipticAleksandrov.Parabolic
