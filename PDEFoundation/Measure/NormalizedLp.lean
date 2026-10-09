module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Restricted and normalized `L^p` norms

This file defines raw extended-real `L^p` norms on restricted volume and on
normalized restricted volume. Real-valued facades require a `MemLp` proof, so
an infinite extended-real norm can never be silently converted to zero.

Vector-field norms are scalarized with `PDE.vecEuclideanNorm`; they do not use
the inherited finite-product supremum norm on `PDE.Vec`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- Volume restricted to `U`, rescaled by the inverse volume of `U`.

The definition is total. It is a probability measure only when `U` has
positive finite volume; those hypotheses are explicit in the corresponding
theorems.
-/
noncomputable def normalizedVolumeOn {d : ℕ} (U : Set (Vec d)) :
    Measure (Vec d) :=
  (volume U)⁻¹ • volumeOn U

/-- Integrability on a positive-volume set implies integrability against its
normalized restricted volume. -/
theorem integrable_normalizedVolumeOn_of_integrableOn
    {d : ℕ} {E : Type*}
    [TopologicalSpace E] [ESeminormedAddMonoid E]
    {U : Set (Vec d)} {f : Vec d → E}
    (hf : IntegrableOn f U volume)
    (hUPos : 0 < volume U) :
    Integrable f (normalizedVolumeOn U) := by
  rw [normalizedVolumeOn]
  exact hf.integrable.smul_measure
    (ENNReal.inv_ne_top.mpr hUPos.ne')

/-- Restricted-volume `L^p` membership passes to normalized restricted
volume whenever the set has positive volume. -/
theorem memLp_normalizedVolumeOn_of_memLpOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f : Vec d → E}
    (hf : MemLp f p (volumeOn U))
    (hUPos : 0 < volume U) :
    MemLp f p (normalizedVolumeOn U) := by
  rw [normalizedVolumeOn]
  exact hf.smul_measure
    (ENNReal.inv_ne_top.mpr hUPos.ne')

/-- On a positive finite-volume set, normalized-volume integrability is
equivalent to ordinary restricted-volume integrability. -/
theorem integrable_normalizedVolumeOn_iff
    {d : ℕ} {E : Type*}
    [TopologicalSpace E] [ESeminormedAddMonoid E]
    {U : Set (Vec d)} {f : Vec d → E}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    Integrable f (normalizedVolumeOn U) ↔
      IntegrableOn f U volume := by
  simpa only [normalizedVolumeOn, IntegrableOn] using
    (integrable_inv_smul_measure
      (μ := volumeOn U) (f := f) hUPos.ne' hUTop.ne)

theorem normalizedVolumeOn_apply_univ_of_pos_of_lt_top
    {d : ℕ} {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    normalizedVolumeOn U Set.univ = 1 := by
  rw [normalizedVolumeOn, Measure.smul_apply, volumeOn,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hUPos.ne' hUTop.ne

theorem isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
    {d : ℕ} {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    IsProbabilityMeasure (normalizedVolumeOn U) :=
  ⟨normalizedVolumeOn_apply_univ_of_pos_of_lt_top hUPos hUTop⟩

theorem normalizedVolumeOn_ne_zero_of_pos_of_lt_top
    {d : ℕ} {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    normalizedVolumeOn U ≠ 0 := by
  intro hzero
  have huniv :=
    normalizedVolumeOn_apply_univ_of_pos_of_lt_top hUPos hUTop
  rw [hzero] at huniv
  simp only [Measure.coe_zero, Pi.zero_apply, zero_ne_one] at huniv

/-- On a positive finite-volume domain, multiplying normalized volume by the
domain volume recovers restricted volume exactly. -/
theorem volume_smul_normalizedVolumeOn_eq_volumeOn
    {d : ℕ} {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    volume U • normalizedVolumeOn U = volumeOn U := by
  rw [normalizedVolumeOn, smul_smul,
    ENNReal.mul_inv_cancel hUPos.ne' hUTop.ne, one_smul]

/-- The raw extended-real `L^p` norm with respect to volume restricted to `U`. -/
noncomputable def eLpNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (volumeOn U)

/-- The raw extended-real normalized `L^p` norm on `U`. -/
noncomputable def eLpMeanNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (normalizedVolumeOn U)

/-- Exact conversion from the normalized to the unnormalized extended
`L^p` norm. -/
theorem eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (f : Vec d → E) :
    eLpMeanNormOn U p f =
      (volume U)⁻¹ ^ (1 / p).toReal *
        eLpNormOn U p f := by
  have hinv : (volume U)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr hUTop.ne
  rw [eLpMeanNormOn, normalizedVolumeOn,
    eLpNorm_smul_measure_of_ne_zero hinv]
  rfl

/-- Exact conversion from the unnormalized to the normalized extended
`L^p` norm on a positive finite-volume domain. -/
theorem eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (f : Vec d → E) :
    eLpNormOn U p f =
      volume U ^ (1 / p).toReal *
        eLpMeanNormOn U p f := by
  have hvol : volume U ≠ 0 := hUPos.ne'
  calc
    eLpNormOn U p f =
        eLpNorm f p (volume U • normalizedVolumeOn U) := by
      rw [volume_smul_normalizedVolumeOn_eq_volumeOn hUPos hUTop]
      rfl
    _ = volume U ^ (1 / p).toReal *
        eLpMeanNormOn U p f := by
      rw [eLpNorm_smul_measure_of_ne_zero hvol]
      rfl

/-- The real `L^p` norm on restricted volume, guarded by membership in `L^p`. -/
noncomputable def lpNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MemLp f p (volumeOn U)) : ℝ :=
  let finiteNorm : {q : ℝ≥0∞ // q ≠ ∞} :=
    ⟨eLpNormOn U p f, ne_of_lt <| by
      simpa only [eLpNormOn] using hf.eLpNorm_lt_top⟩
  finiteNorm.1.toReal

/-- The real normalized `L^p` norm, guarded by membership in normalized `L^p`. -/
noncomputable def lpMeanNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MemLp f p (normalizedVolumeOn U)) : ℝ :=
  let finiteNorm : {q : ℝ≥0∞ // q ≠ ∞} :=
    ⟨eLpMeanNormOn U p f, ne_of_lt <| by
      simpa only [eLpMeanNormOn] using hf.eLpNorm_lt_top⟩
  finiteNorm.1.toReal

theorem lpNormOn_eq_toReal
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MemLp f p (volumeOn U)) :
    lpNormOn U p f hf = (eLpNormOn U p f).toReal :=
  rfl

theorem lpMeanNormOn_eq_toReal
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E)
    (hf : MemLp f p (normalizedVolumeOn U)) :
    lpMeanNormOn U p f hf = (eLpMeanNormOn U p f).toReal :=
  rfl

theorem eLpNormOn_congr_ae
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f g : Vec d → E}
    (hfg : f =ᵐ[volumeOn U] g) :
    eLpNormOn U p f = eLpNormOn U p g := by
  simpa only [eLpNormOn] using MeasureTheory.eLpNorm_congr_ae hfg

theorem eLpMeanNormOn_congr_ae
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f g : Vec d → E}
    (hfg : f =ᵐ[normalizedVolumeOn U] g) :
    eLpMeanNormOn U p f = eLpMeanNormOn U p g := by
  simpa only [eLpMeanNormOn] using MeasureTheory.eLpNorm_congr_ae hfg

theorem eLpNormOn_mono_ae
    {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {U : Set (Vec d)} {p : ℝ≥0∞}
    {f : Vec d → E} {g : Vec d → F}
    (hf : AEStronglyMeasurable f (volumeOn U))
    (hfg : ∀ᵐ x ∂(volumeOn U), ‖f x‖ ≤ ‖g x‖) :
    eLpNormOn U p f ≤ eLpNormOn U p g := by
  simpa only [eLpNormOn] using MeasureTheory.eLpNorm_mono_ae hf hfg

theorem eLpMeanNormOn_mono_ae
    {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {U : Set (Vec d)} {p : ℝ≥0∞}
    {f : Vec d → E} {g : Vec d → F}
    (hf : AEStronglyMeasurable f (normalizedVolumeOn U))
    (hfg : ∀ᵐ x ∂(normalizedVolumeOn U), ‖f x‖ ≤ ‖g x‖) :
    eLpMeanNormOn U p f ≤ eLpMeanNormOn U p g := by
  simpa only [eLpMeanNormOn] using MeasureTheory.eLpNorm_mono_ae hf hfg

theorem eLpNormOn_mono_set
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U V : Set (Vec d)} {p : ℝ≥0∞} (f : Vec d → E)
    (hUV : U ⊆ V) :
    eLpNormOn U p f ≤ eLpNormOn V p f := by
  exact eLpNorm_mono_measure f <|
    Measure.restrict_mono hUV le_rfl

theorem lpNormOn_congr_ae
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f g : Vec d → E}
    (hf : MemLp f p (volumeOn U))
    (hg : MemLp g p (volumeOn U))
    (hfg : f =ᵐ[volumeOn U] g) :
    lpNormOn U p f hf = lpNormOn U p g hg := by
  rw [lpNormOn_eq_toReal, lpNormOn_eq_toReal,
    eLpNormOn_congr_ae hfg]

theorem lpMeanNormOn_congr_ae
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {f g : Vec d → E}
    (hf : MemLp f p (normalizedVolumeOn U))
    (hg : MemLp g p (normalizedVolumeOn U))
    (hfg : f =ᵐ[normalizedVolumeOn U] g) :
    lpMeanNormOn U p f hf = lpMeanNormOn U p g hg := by
  rw [lpMeanNormOn_eq_toReal, lpMeanNormOn_eq_toReal,
    eLpMeanNormOn_congr_ae hfg]

theorem lpNormOn_mono_ae
    {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {U : Set (Vec d)} {p : ℝ≥0∞}
    {f : Vec d → E} {g : Vec d → F}
    (hf : MemLp f p (volumeOn U))
    (hg : MemLp g p (volumeOn U))
    (hfg : ∀ᵐ x ∂(volumeOn U), ‖f x‖ ≤ ‖g x‖) :
    lpNormOn U p f hf ≤ lpNormOn U p g hg := by
  rw [lpNormOn_eq_toReal, lpNormOn_eq_toReal]
  exact ENNReal.toReal_mono (ne_of_lt <| by
    simpa only [eLpNormOn] using hg.eLpNorm_lt_top)
    (eLpNormOn_mono_ae hf.aestronglyMeasurable hfg)

theorem lpMeanNormOn_mono_ae
    {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {U : Set (Vec d)} {p : ℝ≥0∞}
    {f : Vec d → E} {g : Vec d → F}
    (hf : MemLp f p (normalizedVolumeOn U))
    (hg : MemLp g p (normalizedVolumeOn U))
    (hfg : ∀ᵐ x ∂(normalizedVolumeOn U), ‖f x‖ ≤ ‖g x‖) :
    lpMeanNormOn U p f hf ≤ lpMeanNormOn U p g hg := by
  rw [lpMeanNormOn_eq_toReal, lpMeanNormOn_eq_toReal]
  exact ENNReal.toReal_mono (ne_of_lt <| by
    simpa only [eLpMeanNormOn] using hg.eLpNorm_lt_top)
    (eLpMeanNormOn_mono_ae hf.aestronglyMeasurable hfg)

/-- The raw restricted `L^p` norm of the Euclidean magnitude of a vector field. -/
noncomputable def euclideanFieldELpNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNormOn U p (fun x => vecEuclideanNorm (F x))

/-- The raw normalized `L^p` norm of the Euclidean magnitude of a vector field. -/
noncomputable def euclideanFieldELpMeanNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpMeanNormOn U p (fun x => vecEuclideanNorm (F x))

theorem euclideanFieldELpMeanNormOn_eq_volume_inv_rpow_mul
    {d : ℕ} {U : Set (Vec d)} (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (F : Vec d → Vec d) :
    euclideanFieldELpMeanNormOn U p F =
      (volume U)⁻¹ ^ (1 / p).toReal *
        euclideanFieldELpNormOn U p F := by
  exact
    eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hUTop p (fun x => vecEuclideanNorm (F x))

theorem euclideanFieldELpNormOn_eq_volume_rpow_mul
    {d : ℕ} {U : Set (Vec d)}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (p : ℝ≥0∞) (F : Vec d → Vec d) :
    euclideanFieldELpNormOn U p F =
      volume U ^ (1 / p).toReal *
        euclideanFieldELpMeanNormOn U p F := by
  exact
    eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      hUPos hUTop p (fun x => vecEuclideanNorm (F x))

/-- The guarded real restricted `L^p` norm of a vector field's Euclidean magnitude. -/
noncomputable def euclideanFieldLpNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p (volumeOn U)) : ℝ :=
  lpNormOn U p (fun x => vecEuclideanNorm (F x)) hF

/-- The guarded real normalized `L^p` norm of a vector field's Euclidean magnitude. -/
noncomputable def euclideanFieldLpMeanNormOn
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) p
      (normalizedVolumeOn U)) : ℝ :=
  lpMeanNormOn U p (fun x => vecEuclideanNorm (F x)) hF

theorem euclideanFieldELpNormOn_congr_ae
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {F G : Vec d → Vec d} (hFG : F =ᵐ[volumeOn U] G) :
    euclideanFieldELpNormOn U p F =
      euclideanFieldELpNormOn U p G := by
  apply eLpNormOn_congr_ae
  exact hFG.fun_comp vecEuclideanNorm

theorem euclideanFieldELpMeanNormOn_congr_ae
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {F G : Vec d → Vec d}
    (hFG : F =ᵐ[normalizedVolumeOn U] G) :
    euclideanFieldELpMeanNormOn U p F =
      euclideanFieldELpMeanNormOn U p G := by
  apply eLpMeanNormOn_congr_ae
  exact hFG.fun_comp vecEuclideanNorm

theorem euclideanFieldELpNormOn_mono_ae
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {F G : Vec d → Vec d}
    (hF : AEStronglyMeasurable (fun x => vecEuclideanNorm (F x)) (volumeOn U))
    (hFG : ∀ᵐ x ∂(volumeOn U),
      vecEuclideanNorm (F x) ≤ vecEuclideanNorm (G x)) :
    euclideanFieldELpNormOn U p F ≤
      euclideanFieldELpNormOn U p G := by
  apply eLpNormOn_mono_ae hF
  filter_upwards [hFG] with x hx
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (vecEuclideanNorm_nonneg (F x)),
    abs_of_nonneg (vecEuclideanNorm_nonneg (G x))] using hx

theorem euclideanFieldELpMeanNormOn_mono_ae
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {F G : Vec d → Vec d}
    (hF : AEStronglyMeasurable (fun x => vecEuclideanNorm (F x))
      (normalizedVolumeOn U))
    (hFG : ∀ᵐ x ∂(normalizedVolumeOn U),
      vecEuclideanNorm (F x) ≤ vecEuclideanNorm (G x)) :
    euclideanFieldELpMeanNormOn U p F ≤
      euclideanFieldELpMeanNormOn U p G := by
  apply eLpMeanNormOn_mono_ae hF
  filter_upwards [hFG] with x hx
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (vecEuclideanNorm_nonneg (F x)),
    abs_of_nonneg (vecEuclideanNorm_nonneg (G x))] using hx

theorem eLpNormOn_comp_subRight_translateSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) (U : Set (Vec d)) (p : ℝ≥0∞)
    (f : Vec d → E) (hf : AEStronglyMeasurable f (volumeOn U)) :
    eLpNormOn (translateSet z U) p (fun x => f (x - z)) =
      eLpNormOn U p f := by
  simpa only [eLpNormOn, Function.comp_def] using
    eLpNorm_comp_measurePreserving hf
      (measurePreserving_subRight_restrict_translateSet z U)

theorem measurePreserving_subRight_normalizedVolumeOn_translateSet
    {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x - z)
      (normalizedVolumeOn (translateSet z U))
      (normalizedVolumeOn U) := by
  refine ⟨(measurePreserving_subRight_restrict_translateSet z U).measurable, ?_⟩
  rw [normalizedVolumeOn, normalizedVolumeOn,
    Measure.map_smul _ (measurePreserving_subRight_restrict_translateSet z U).aemeasurable,
    (measurePreserving_subRight_restrict_translateSet z U).map_eq,
    volume_translateSet_eq]

theorem eLpMeanNormOn_comp_subRight_translateSet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (z : Vec d) (U : Set (Vec d)) (p : ℝ≥0∞)
    (f : Vec d → E)
    (hf : AEStronglyMeasurable f (normalizedVolumeOn U)) :
    eLpMeanNormOn (translateSet z U) p (fun x => f (x - z)) =
      eLpMeanNormOn U p f := by
  simpa only [eLpMeanNormOn, Function.comp_def] using
    eLpNorm_comp_measurePreserving hf
      (measurePreserving_subRight_normalizedVolumeOn_translateSet z U)

end PDE
