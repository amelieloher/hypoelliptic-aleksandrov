module

public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.InnerCylinder
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyScaling

/-! # Restricted norms of the scalar residual and its inward compression -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open MeasureTheory Set Filter
open scoped ENNReal

/-- The positive continuous residual is dominated in norm by an a.e. source. -/
theorem positive_residual_memLp_norm_le
    {N : ℕ} {Q : Set (TimeVelocity N)} (hQ : MeasurableSet Q)
    (a : TimeVelocity N → PDE.Mat N) (u f : TimeVelocity N → ℝ)
    (hg : AEStronglyMeasurable (residual a u) (volume.restrict Q))
    (hf : MemLp f (parabolicExponent N) (volume.restrict Q))
    (hsub : ∀ᵐ z ∂volume.restrict Q, residual a u z ≤ f z) :
    MemLp (fun z => max (residual a u z) 0) (parabolicExponent N)
        (volume.restrict Q) ∧
      parabolicLpNormOn N (fun z => max (residual a u z) 0) Q ≤
        parabolicLpNormOn N f Q := by
  have hm : AEStronglyMeasurable (fun z => max (residual a u z) 0)
      (volume.restrict Q) :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable hg
  have hb : ∀ᵐ z ∂volume.restrict Q, ‖max (residual a u z) 0‖ ≤ ‖f z‖ := by
    filter_upwards [hsub] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (hz.trans (le_abs_self _)) (abs_nonneg _)
  refine ⟨hf.of_le hm hb, ?_⟩
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_ae hm hb)

/-- Inward parabolic compression does not increase the amplified source norm. -/
theorem compressed_source_memLp_norm_le
    {N : ℕ} (hN : 1 ≤ N) (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (g : TimeVelocity N → ℝ)
    (hg : MemLp g (parabolicExponent N)
      (volume.restrict (krylovCylinder t₀ h v₀))) :
    MemLp (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z))
        (parabolicExponent N)
        (volume.restrict (parabolicInterior h (0 : PDE.Vec N))) ∧
      parabolicLpNormOn N (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z))
          (parabolicInterior h (0 : PDE.Vec N)) ≤
        parabolicLpNormOn N g (krylovCylinder t₀ h v₀) := by
  let S := parabolicInterior h (0 : PDE.Vec N)
  let J := innerMap t₀ h v₀ ρ '' S
  have hJ : J ⊆ krylovCylinder t₀ h v₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact innerMap_mapsTo t₀ h v₀ hh hρ hρ1
      (parabolicInterior_subset_closedParabolicCylinder h 0 hz)
  have hgJ : MemLp g (parabolicExponent N) (volume.restrict J) :=
    hg.mono_measure (Measure.restrict_mono hJ le_rfl)
  have hscale := parabolicELpNormOn_pullback_raw
    (t₀ - h + (1 - ρ ^ 2) * h / 2) v₀ hρ g S
  change parabolicELpNormOn N (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z)) S =
    ‖ρ ^ 2‖ₑ * (ENNReal.ofReal ((ρ ^ (N + 2))⁻¹) ^
      (1 / parabolicExponent N).toReal) * parabolicELpNormOn N g J at hscale
  have hfac : ‖ρ ^ 2‖ₑ * (ENNReal.ofReal ((ρ ^ (N + 2))⁻¹) ^
      (1 / parabolicExponent N).toReal) ≤ 1 := by
    rw [Real.enorm_eq_ofReal (sq_nonneg ρ), ENNReal.ofReal_rpow_of_nonneg
      (by positivity) ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (sq_nonneg ρ)]
    apply ENNReal.ofReal_le_one.mpr
    have hp : (1 / parabolicExponent N).toReal = 1 / ((N : ℝ) + 1) := by
      have hpval : parabolicExponent N = ((N + 1 : ℕ) : ℝ≥0∞) := by
        simp only [parabolicExponent, Nat.cast_add, Nat.cast_one]
      rw [hpval, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
      norm_num
    rw [hp, Real.inv_rpow (by positivity)]
    rw [← Real.rpow_natCast ρ (N + 2), ← Real.rpow_mul hρ.le,
      ← Real.rpow_neg hρ.le, ← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ]
    have he : (2 : ℝ) + -((N + 2 : ℝ) * (1 / ((N : ℝ) + 1))) =
        (N : ℝ) / ((N : ℝ) + 1) := by field_simp; ring
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at *
    rw [he]
    exact Real.rpow_le_one hρ.le hρ1.le (by positivity)
  have hnorm : parabolicELpNormOn N
      (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z)) S ≤
      parabolicELpNormOn N g J := by
    rw [hscale]
    exact (mul_le_mul_left hfac _).trans_eq (one_mul _)
  have hmem : MemLp (fun z => ρ ^ 2 * g (innerMap t₀ h v₀ ρ z))
      (parabolicExponent N) (volume.restrict S) := hnorm.trans_lt hgJ
  refine ⟨hmem, ?_⟩
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top
    (hnorm.trans (eLpNorm_mono_measure g (Measure.restrict_mono hJ le_rfl)))

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
