module

public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity

/-! # Arbitrary-exponent norms under parabolic dilation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal

/-- Restricted volume under the parabolic affine change of variables. -/
theorem occupation_map_restrict_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (s : Set (TimeVelocity d)) :
    Measure.map (parabolicAffine t₀ v₀ r) (volume.restrict s) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) •
        volume.restrict (parabolicAffine t₀ v₀ r '' s) := by
  have he := parabolicAffine_measurableEmbedding (t₀ := t₀) (v₀ := v₀) hr
  have hp : parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' s) = s :=
    preimage_image_eq _ (parabolicAffine_injective hr)
  calc
    _ = (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' s) := by
      have hh := (he.restrict_map volume (parabolicAffine t₀ v₀ r '' s)).symm
      simpa only [hp] using hh
    _ = _ := by rw [map_volume_parabolicAffine t₀ v₀ hr, Measure.restrict_smul]

/-- Pullback norm with a scalar prefactor, at every extended exponent. -/
theorem occupation_eLpNorm_pullback {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a : ℝ) (g : TimeVelocity d → ℝ)
    (p : ℝ≥0∞) (s : Set (TimeVelocity d)) :
    eLpNorm (fun z => a * g (parabolicAffine t₀ v₀ r z)) p (volume.restrict s) =
      ‖a‖ₑ * (ENNReal.ofReal ((r ^ (d + 2))⁻¹) ^ (1 / p).toReal) *
        eLpNorm g p (volume.restrict (parabolicAffine t₀ v₀ r '' s)) := by
  have hc : ENNReal.ofReal ((r ^ (d + 2))⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (pow_pos hr _))
  have he := parabolicAffine_measurableEmbedding (t₀ := t₀) (v₀ := v₀) hr
  change eLpNorm (a • (g ∘ parabolicAffine t₀ v₀ r)) p (volume.restrict s) = _
  rw [eLpNorm_const_smul, ← he.eLpNorm_map_measure,
    occupation_map_restrict_parabolicAffine t₀ v₀ hr s,
    eLpNorm_smul_measure_of_ne_zero hc]
  simp only [smul_eq_mul, mul_assoc]

/-- Inverse parabolic dilation carries the length-T open slab onto the unit slab. -/
theorem occupation_inverseScaling_image_slab {d : ℕ} {T : ℝ} (hT : 0 < T) :
    parabolicAffine 0 (0 : PDE.Vec d) (Real.sqrt T)⁻¹ ''
      (Ioo (0 : ℝ) T ×ˢ univ) = Ioo (0 : ℝ) 1 ×ˢ univ := by
  have hs : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  have hs0 : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (0 < 0 + (Real.sqrt T)⁻¹ ^ 2 * z.1 ∧
      0 + (Real.sqrt T)⁻¹ ^ 2 * z.1 < 1) ∧ _
    rw [inv_pow, hs]
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · simpa only [zero_add] using mul_pos (inv_pos.mpr hT) hz.1.1
    · simpa only [zero_add, inv_mul_eq_div] using (div_lt_one hT).mpr hz.1.2
  · intro hq
    refine ⟨(T * q.1, Real.sqrt T • q.2), ?_, ?_⟩
    · exact ⟨⟨mul_pos hT hq.1.1, by nlinarith only [hq.1.2, hT]⟩, mem_univ _⟩
    · apply Prod.ext
      · change 0 + (Real.sqrt T)⁻¹ ^ 2 * (T * q.1) = q.1
        rw [inv_pow, hs]
        field_simp
        simp only [zero_add]
      · ext j
        change 0 + (Real.sqrt T)⁻¹ * (Real.sqrt T * q.2 j) = q.2 j
        field_simp
        simp only [zero_add]

/-- The scalar determinant factor is exactly the source time exponent. -/
theorem occupation_scaling_factor {d : ℕ} {T γ : ℝ} (hT : 0 < T) :
    T ^ (-(d : ℝ) / 2) *
      (((Real.sqrt T)⁻¹ ^ (d + 2))⁻¹) ^ (1 / γ) =
        T ^ occupationBeta d γ := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [inv_pow, inv_inv, ← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_add hT]
  congr 1
  unfold occupationBeta
  push_cast
  ring

/-- The real norm of the constructed scaled density has the exact source factor. -/
theorem occupationLpNorm_scaledDensity {d : ℕ} {T γ : ℝ} (hT : 0 < T)
    (hγ : 0 ≤ γ) (g : TimeVelocity d → ℝ) :
    occupationLpNorm T γ
      (fun q => T ^ (-(d : ℝ) / 2) * g (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) =
        T ^ occupationBeta d γ * occupationLpNorm 1 γ g := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsq := Real.sq_sqrt hT.le
  have hf : (fun q : TimeVelocity d =>
      T ^ (-(d : ℝ) / 2) * g (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) =
      fun q => T ^ (-(d : ℝ) / 2) *
        g (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) := by
    funext q
    congr 2
    apply Prod.ext
    · change q.1 / T = 0 + (Real.sqrt T)⁻¹ ^ 2 * q.1
      rw [inv_pow, hsq]
      simp only [zero_add, inv_mul_eq_div]
    · simp only [parabolicAffine, zero_add]
  unfold occupationLpNorm
  rw [hf, occupation_eLpNorm_pullback 0 0 (inv_pos.mpr hs),
    occupation_inverseScaling_image_slab hT, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, Real.enorm_of_nonneg (Real.rpow_nonneg hT.le _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hT.le _),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hs.le) _)),
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hγ,
    occupation_scaling_factor hT]

/-- Parabolic pullback with a finite prefactor preserves finite extended norms. -/
theorem occupation_memLp_pullback {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (a : ℝ) (g : TimeVelocity d → ℝ)
    (p : ℝ≥0∞) (s : Set (TimeVelocity d))
    (hg : MemLp g p (volume.restrict (parabolicAffine t₀ v₀ r '' s))) :
    MemLp (fun z => a * g (parabolicAffine t₀ v₀ r z)) p (volume.restrict s) := by
  change eLpNorm _ _ _ < ⊤
  rw [occupation_eLpNorm_pullback t₀ v₀ hr]
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top enorm_lt_top
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact hg

/-- The inverse-density prefactor times its Jacobian equals the elapsed-time scale. -/
theorem occupation_density_jacobian {d : ℕ} {T : ℝ} (hT : 0 < T) :
    T ^ (-(d : ℝ) / 2) * ((Real.sqrt T)⁻¹ ^ (d + 2))⁻¹ = T := by
  have hh := occupation_scaling_factor (d := d) (γ := 1) hT
  have hb : occupationBeta d 1 = 1 := by unfold occupationBeta; ring
  simpa only [div_one, Real.rpow_one, hb] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
