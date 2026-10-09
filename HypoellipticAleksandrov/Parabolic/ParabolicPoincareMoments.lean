module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareFoundation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Unit-box parabolic moment projection

This module computes the first two velocity moments of the literal open
parabolic Morrey unit box and records the resulting algebra of its normalized
velocity-affine moment projection. Endpoint and product-factorization
calculations remain private.
-/

@[expose] public section

noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory
open scoped BigOperators ENNReal

private theorem int_one : ∫ _ in Set.Ioo (-1 : ℝ) 1, (1 : ℝ) = 2 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [intervalIntegral.integral_const]

private theorem int_id : ∫ x in Set.Ioo (-1 : ℝ) 1, x = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [integral_id]

private theorem int_sq : ∫ x in Set.Ioo (-1 : ℝ) 1, x * x = 2 / 3 := by
  rw [show (fun x : ℝ => x * x) = fun x => x ^ 2 by ext; ring,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [integral_pow]

private theorem cube_measure (d : ℕ) :
    volume.restrict (velocityCube (0 : PDE.Vec d) 1) =
      Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
  rw [velocityCube_eq_pi]
  simp only [Pi.zero_apply, zero_sub, zero_add]
  change (Measure.pi (fun _ : Fin d => volume)).restrict
    (Set.univ.pi fun _ : Fin d => Set.Ioo (-1 : ℝ) 1) = _
  rw [Measure.restrict_pi_pi]

private theorem box_measure (d : ℕ) :
    volume.restrict (parabolicMorreyUnitBox d) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (velocityCube (0 : PDE.Vec d) 1)) := by
  rw [parabolicMorreyUnitBox, volume_timeVelocity_eq_prod]
  symm
  simpa [parabolicBox] using Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (PDE.Vec d))) (Set.Ioo 0 1)
    (velocityCube (0 : PDE.Vec d) 1)

private theorem cube_int_eval {d : ℕ} (i : Fin d) :
    ∫ v in velocityCube (0 : PDE.Vec d) 1, v i = 0 := by
  rw [cube_measure]
  let q : Fin d → ℝ → ℝ := fun k x => if k = i then x else 1
  have hq : (fun v : PDE.Vec d => v i) = fun v => ∏ k, q k (v k) := by
    ext v
    simp [q]
  rw [hq, integral_fintype_prod_eq_prod]
  simp only [q]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [q] using int_id

private theorem box_int_eval {d : ℕ} (i : Fin d) :
    ∫ z in parabolicMorreyUnitBox d, z.2 i = 0 := by
  rw [box_measure]
  change ∫ z, z.2 i ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (volume.restrict (velocityCube (0 : PDE.Vec d) 1))) = 0
  simpa using (integral_fun_snd (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
    (ν := volume.restrict (velocityCube (0 : PDE.Vec d) 1))
    (fun v : PDE.Vec d => v i)).trans (by rw [cube_int_eval i]; simp)

private theorem cube_int_eval_mul_eval {d : ℕ} (i j : Fin d) :
    ∫ v in velocityCube (0 : PDE.Vec d) 1, v i * v j =
      if i = j then (2 : ℝ) ^ d / 3 else 0 := by
  classical
  rw [cube_measure]
  by_cases hij : i = j
  · subst j
    let q : Fin d → ℝ → ℝ := fun k x => if k = i then x * x else 1
    have hq : (fun v : PDE.Vec d => v i * v i) = fun v => ∏ k, q k (v k) := by
      ext v
      simp [q]
    rw [hq, integral_fintype_prod_eq_prod]
    have hqint : (fun k : Fin d => ∫ x in Set.Ioo (-1 : ℝ) 1, q k x) =
        fun k => if k = i then 2 / 3 else 2 := by
      funext k
      by_cases hki : k = i
      · subst k
        simpa [q] using int_sq
      · simp [q, hki]
        norm_num
    rw [hqint, if_pos rfl]
    have hfactor : (fun k : Fin d => if k = i then (2 / 3 : ℝ) else 2) =
        fun k => 2 * (if k = i then (1 / 3 : ℝ) else 1) := by
      funext k
      by_cases hki : k = i
      · simp [hki]
        norm_num
      · simp [hki]
    rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Fintype.prod_ite_eq']
    simp only [Finset.card_univ, Fintype.card_fin]
    ring
  · let q : Fin d → ℝ → ℝ := fun k x => if k = i then x else if k = j then x else 1
    have hq : (fun v : PDE.Vec d => v i * v j) = fun v => ∏ k, q k (v k) := by
      ext v
      calc
        v i * v j = q i (v i) * q j (v j) := by simp [q]
        _ = q i (v i) * (q j (v j) *
            ∏ k ∈ (Finset.univ.erase i).erase j, q k (v k)) := by
          congr 1
          have hprod : ∏ k ∈ (Finset.univ.erase i).erase j, q k (v k) = 1 := by
            apply Finset.prod_eq_one
            intro k hk
            rcases Finset.mem_erase.mp hk with ⟨hkj, hki_mem⟩
            exact by simp [q, hkj, (Finset.mem_erase.mp hki_mem).1]
          rw [hprod, mul_one]
        _ = ∏ k, q k (v k) := by
          rw [Finset.mul_prod_erase (Finset.univ.erase i) (fun k => q k (v k))]
          · rw [Finset.mul_prod_erase Finset.univ (fun k => q k (v k))]
            exact Finset.mem_univ _
          · exact Finset.mem_erase.mpr ⟨fun h => hij h.symm, Finset.mem_univ _⟩
    rw [hq, integral_fintype_prod_eq_prod]
    rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [q, hij] using int_id

private theorem box_int_eval_mul_eval {d : ℕ} (i j : Fin d) :
    ∫ z in parabolicMorreyUnitBox d, z.2 i * z.2 j =
      if i = j then (2 : ℝ) ^ d / 3 else 0 := by
  rw [box_measure]
  change ∫ z, z.2 i * z.2 j ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
    (volume.restrict (velocityCube (0 : PDE.Vec d) 1))) = _
  calc
    _ = (∫ _ in Set.Ioo (0 : ℝ) 1, (1 : ℝ)) *
        ∫ v in velocityCube (0 : PDE.Vec d) 1, v i * v j := by
      simpa using integral_prod_mul (μ := volume.restrict (Set.Ioo (0 : ℝ) 1))
        (ν := volume.restrict (velocityCube (0 : PDE.Vec d) 1)) (fun _ : ℝ => (1 : ℝ))
        (fun v : PDE.Vec d => v i * v j)
    _ = _ := by simp [cube_int_eval_mul_eval]

/-- The unit-box average of the constant function one is one. -/
theorem parabolicMorreyUnitAverage_one (d : ℕ) :
    parabolicMorreyUnitAverage (fun _ : TimeVelocity d => (1 : ℝ)) = 1 := by
  rw [parabolicMorreyUnitAverage, MeasureTheory.integral_const,
    Measure.real, Measure.restrict_apply_univ,
    volume_parabolicMorreyUnitBox_toReal]
  simp only [smul_eq_mul]
  field_simp

/-- Every velocity coordinate has zero average on the symmetric unit box. -/
theorem parabolicMorreyUnitAverage_velocity {d : ℕ} (i : Fin d) :
    parabolicMorreyUnitAverage (fun z : TimeVelocity d => z.2 i) = 0 := by
  rw [parabolicMorreyUnitAverage, box_int_eval]
  ring

/-- The unit-box velocity-coordinate moment matrix is diagonal with diagonal
entry `1 / 3`. -/
theorem parabolicMorreyUnitAverage_velocity_mul_velocity {d : ℕ} (i j : Fin d) :
    parabolicMorreyUnitAverage (fun z : TimeVelocity d => z.2 i * z.2 j) =
      if i = j then (1 / 3 : ℝ) else 0 := by
  rw [parabolicMorreyUnitAverage, box_int_eval_mul_eval,
    volume_parabolicMorreyUnitBox_toReal]
  by_cases hij : i = j
  · simp [hij]
    field_simp
  · simp [hij]

/-- The unit-box average is additive on genuinely integrable inputs. -/
theorem parabolicMorreyUnitAverage_add {d : ℕ} (f g : TimeVelocity d → ℝ)
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d)))
    (hg : Integrable g (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitAverage (f + g) =
      parabolicMorreyUnitAverage f + parabolicMorreyUnitAverage g := by
  simp only [parabolicMorreyUnitAverage]
  simp only [Pi.add_apply]
  rw [integral_add hf hg]
  ring

/-- The unit-box average commutes with real scalar multiplication. -/
theorem parabolicMorreyUnitAverage_smul {d : ℕ} (c : ℝ) (f : TimeVelocity d → ℝ) :
    parabolicMorreyUnitAverage (c • f) = c • parabolicMorreyUnitAverage f := by
  simp only [parabolicMorreyUnitAverage]
  change (volume (parabolicMorreyUnitBox d)).toReal⁻¹ *
      ∫ z in parabolicMorreyUnitBox d, c • f z = c •
    ((volume (parabolicMorreyUnitBox d)).toReal⁻¹ *
      ∫ z in parabolicMorreyUnitBox d, f z)
  rw [integral_smul]
  simp only [smul_eq_mul]
  ring

/-- A velocity moment coefficient is additive when its two weighted inputs
are integrable on the unit box. -/
theorem parabolicMorreyUnitVelocityCoeff_add {d : ℕ} (f g : TimeVelocity d → ℝ) (i : Fin d)
    (hf : Integrable (fun z => f z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)))
    (hg : Integrable (fun z => g z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitVelocityCoeff (f + g) i =
      parabolicMorreyUnitVelocityCoeff f i +
        parabolicMorreyUnitVelocityCoeff g i := by
  simp only [parabolicMorreyUnitVelocityCoeff]
  rw [show (fun z : TimeVelocity d =>
      (f + g) z * z.2 i) = (fun z => f z * z.2 i) + fun z => g z * z.2 i by
        ext z
        simp only [Pi.add_apply]
        ring, parabolicMorreyUnitAverage_add _ _ hf hg]
  ring

/-- A velocity moment coefficient commutes with real scalar multiplication. -/
theorem parabolicMorreyUnitVelocityCoeff_smul {d : ℕ} (c : ℝ) (f : TimeVelocity d → ℝ) (i : Fin d) :
    parabolicMorreyUnitVelocityCoeff (c • f) i =
      c • parabolicMorreyUnitVelocityCoeff f i := by
  simp only [parabolicMorreyUnitVelocityCoeff]
  rw [show (fun z : TimeVelocity d =>
      (c • f) z * z.2 i) = c • (fun z => f z * z.2 i) by
        ext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring, parabolicMorreyUnitAverage_smul]
  simp only [smul_eq_mul]
  ring

/-- The moment projection is additive when the value and every first moment
of both inputs are integrable on the unit box. -/
theorem parabolicMorreyUnitAffineProjection_add {d : ℕ} (f g : TimeVelocity d → ℝ)
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d)))
    (hg : Integrable g (volume.restrict (parabolicMorreyUnitBox d)))
    (hfv : ∀ i : Fin d, Integrable (fun z => f z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d)))
    (hgv : ∀ i : Fin d, Integrable (fun z => g z * z.2 i)
      (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitAffineProjection (f + g) =
      parabolicMorreyUnitAffineProjection f +
        parabolicMorreyUnitAffineProjection g := by
  funext z
  have hcoeff : ∀ i : Fin d,
      parabolicMorreyUnitVelocityCoeff (f + g) i =
        parabolicMorreyUnitVelocityCoeff f i +
          parabolicMorreyUnitVelocityCoeff g i :=
    fun i => parabolicMorreyUnitVelocityCoeff_add f g i (hfv i) (hgv i)
  simp only [parabolicMorreyUnitAffineProjection, Pi.add_apply]
  rw [parabolicMorreyUnitAverage_add f g hf hg]
  simp_rw [hcoeff]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

/-- The moment projection commutes with real scalar multiplication. -/
theorem parabolicMorreyUnitAffineProjection_smul {d : ℕ} (c : ℝ) (f : TimeVelocity d → ℝ) :
    parabolicMorreyUnitAffineProjection (c • f) =
      c • parabolicMorreyUnitAffineProjection f := by
  funext z
  simp only [parabolicMorreyUnitAffineProjection, Pi.smul_apply]
  rw [parabolicMorreyUnitAverage_smul]
  simp_rw [parabolicMorreyUnitVelocityCoeff_smul]
  simp only [smul_eq_mul]
  rw [mul_add, Finset.mul_sum]
  simp_rw [mul_assoc]

private theorem continuous_integrable_unit {d : ℕ} {f : TimeVelocity d → ℝ}
    (hf : Continuous f) :
    Integrable f (volume.restrict (parabolicMorreyUnitBox d)) := by
  let K : Set (TimeVelocity d) := parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact : IsCompact K :=
    isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hunitSubset : parabolicMorreyUnitBox d ⊆ K := by
    rintro ⟨t, v⟩ hz
    change (t, v) ∈ parabolicBox 1 1 0 0 at hz
    change (t, v) ∈ parabolicClosedBox 1 1 0 0
    rcases hz with ⟨⟨htLeft, htRight⟩, hv⟩
    exact ⟨⟨htLeft.le, htRight.le⟩, fun i => (hv i).le⟩
  exact (hf.continuousOn.integrableOn_compact hKcompact).mono_set hunitSubset

private theorem average_finset_sum {d ι : ℕ} (s : Finset (Fin ι))
    (f : Fin ι → TimeVelocity d → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicMorreyUnitAverage (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, parabolicMorreyUnitAverage (f i) := by
  simp only [parabolicMorreyUnitAverage]
  rw [integral_finset_sum s hf, Finset.mul_sum]

private theorem average_velocity_affine {d : ℕ} (a : ℝ) (b : Fin d → ℝ) :
    parabolicMorreyUnitAverage
        (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) = a := by
  let f : Fin d → TimeVelocity d → ℝ := fun i z => b i * z.2 i
  have hconst : Integrable (fun _ : TimeVelocity d => a)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    apply continuous_integrable_unit
    fun_prop
  have hf : ∀ i : Fin d, Integrable (f i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i
    apply continuous_integrable_unit
    fun_prop
  have hsum : Integrable (fun z => ∑ i : Fin d, f i z)
      (volume.restrict (parabolicMorreyUnitBox d)) :=
    integrable_finset_sum _ fun i _ => hf i
  rw [show (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) =
      (fun _ => a) + fun z => ∑ i : Fin d, f i z by
        ext z
        simp only [Pi.add_apply, f]
    , parabolicMorreyUnitAverage_add _ _ hconst hsum,
      average_finset_sum Finset.univ f (fun i _ => hf i)]
  have hconst_avg : parabolicMorreyUnitAverage (fun _ : TimeVelocity d => a) = a := by
    rw [show (fun _ : TimeVelocity d => a) = a • (fun _ => (1 : ℝ)) by
      ext z
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      , parabolicMorreyUnitAverage_smul, parabolicMorreyUnitAverage_one]
    simp only [smul_eq_mul, mul_one]
  rw [hconst_avg]
  simp_rw [show f = fun i => b i • (fun z : TimeVelocity d => z.2 i) by
    funext i z
    simp only [f, Pi.smul_apply, smul_eq_mul]]
  simp_rw [parabolicMorreyUnitAverage_smul, parabolicMorreyUnitAverage_velocity]
  simp only [smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]

private theorem coeff_velocity_affine {d : ℕ} (a : ℝ) (b : Fin d → ℝ)
    (j : Fin d) :
    parabolicMorreyUnitVelocityCoeff
        (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) j = b j := by
  let g : Fin d → TimeVelocity d → ℝ := fun i z => b i * (z.2 i * z.2 j)
  have hfirst : Integrable (fun z : TimeVelocity d => a * z.2 j)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    apply continuous_integrable_unit
    fun_prop
  have hg : ∀ i : Fin d, Integrable (g i)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i
    apply continuous_integrable_unit
    fun_prop
  have hsum : Integrable (fun z => ∑ i : Fin d, g i z)
    (volume.restrict (parabolicMorreyUnitBox d)) :=
    integrable_finset_sum _ fun i _ => hg i
  rw [parabolicMorreyUnitVelocityCoeff]
  rw [show (fun z : TimeVelocity d =>
      (a + ∑ i : Fin d, b i * z.2 i) * z.2 j) =
      (fun z => a * z.2 j) + fun z => ∑ i : Fin d, g i z by
        ext z
        simp only [Pi.add_apply, g]
        rw [add_mul, Finset.sum_mul]
        ring_nf
    , parabolicMorreyUnitAverage_add _ _ hfirst hsum,
      average_finset_sum Finset.univ g (fun i _ => hg i)]
  have hfirst_avg : parabolicMorreyUnitAverage (fun z : TimeVelocity d => a * z.2 j) = 0 := by
    rw [show (fun z : TimeVelocity d => a * z.2 j) =
        a • (fun z : TimeVelocity d => z.2 j) by
          ext z
          simp only [Pi.smul_apply, smul_eq_mul]
      , parabolicMorreyUnitAverage_smul, parabolicMorreyUnitAverage_velocity]
    simp only [smul_eq_mul, mul_zero]
  rw [hfirst_avg]
  simp_rw [show g = fun i => b i • (fun z : TimeVelocity d => z.2 i * z.2 j) by
    funext i z
    simp only [g, Pi.smul_apply, smul_eq_mul]]
  simp_rw [parabolicMorreyUnitAverage_smul,
    parabolicMorreyUnitAverage_velocity_mul_velocity]
  simp only [smul_eq_mul, zero_add]
  have hnormalization : 3 * (1 / 3 : ℝ) = 1 := by norm_num
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · simp only [ite_true]
    calc
      _ = b j * (3 * (1 / 3)) := by ring
      _ = b j := by rw [hnormalization, mul_one]
  · intro i _ hij
    simp [hij]

/-- The canonical unit-box moment projection exactly reproduces every
time-independent velocity-affine scalar field. -/
theorem parabolicMorreyUnitAffineProjection_reproduces_velocity_affine
    {d : ℕ} (a : ℝ) (b : Fin d → ℝ) :
    parabolicMorreyUnitAffineProjection
        (fun z : TimeVelocity d => a + ∑ i : Fin d, b i * z.2 i) =
      fun z => a + ∑ i : Fin d, b i * z.2 i := by
  funext z
  rw [parabolicMorreyUnitAffineProjection, average_velocity_affine]
  simp_rw [coeff_velocity_affine]

end HypoellipticAleksandrov.Parabolic
