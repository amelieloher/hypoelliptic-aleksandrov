module

public import HypoellipticAleksandrov.Parabolic.WeakEquation
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Parabolic regularization of coefficient fields

This module repairs local almost-everywhere ellipticity on a measurable null
set, extends the repair by the ellipticity midpoint, and regularizes the
result entrywise with the parabolic mollifier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal MatrixOrder Topology

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance matrixMeasurableSpace (d : Nat) : MeasurableSpace (PDE.Mat d) := by
  unfold PDE.Mat Matrix
  infer_instance

variable {d : Nat}

/-- The scalar midpoint of the lower and upper ellipticity bounds, times the
identity matrix. -/
noncomputable def ellipticityMidpoint (d : Nat) (lam Lam : Real) : PDE.Mat d :=
  ((lam + Lam) / 2) • (1 : PDE.Mat d)

/-- A coefficient field obtained by assigning a fixed matrix on a prescribed
exceptional set. -/
noncomputable def modifyCoefficientOnNullSet
    (A : CoefficientField d) (N : Set (TimeVelocity d)) (M : PDE.Mat d) :
    CoefficientField d := by
  classical
  exact fun t v => if (t, v) ∈ N then M else A t v

/-- A coefficient field extended by a fixed matrix outside a prescribed set. -/
noncomputable def extendCoefficientByMidpoint
    (A : CoefficientField d) (U : Set (TimeVelocity d)) (M : PDE.Mat d) :
    CoefficientField d := by
  classical
  exact fun t v => if (t, v) ∈ U then A t v else M

/-- The entrywise right convolution of a coefficient field with the
native-norm parabolic mollifier. -/
noncomputable def parabolicMollifyCoefficient
    (A : CoefficientField d) (n : Nat) : CoefficientField d :=
  fun t v i j => parabolicConvolution
    (fun z : TimeVelocity d => coefficientAt A z i j)
    (parabolicMollifier d n) (t, v)

/-- Evaluation of a null-set modification. -/
@[simp] theorem coefficientAt_modifyCoefficientOnNullSet
    (A : CoefficientField d) (N : Set (TimeVelocity d)) (M : PDE.Mat d)
    (z : TimeVelocity d) :
    coefficientAt (modifyCoefficientOnNullSet A N M) z =
      if z ∈ N then M else coefficientAt A z :=
  by
    classical
    rfl

/-- Evaluation of a midpoint extension. -/
@[simp] theorem coefficientAt_extendCoefficientByMidpoint
    (A : CoefficientField d) (U : Set (TimeVelocity d)) (M : PDE.Mat d)
    (z : TimeVelocity d) :
    coefficientAt (extendCoefficientByMidpoint A U M) z =
      if z ∈ U then coefficientAt A z else M :=
  by
    classical
    rfl

/-- Evaluation of an entrywise parabolic coefficient mollification. -/
@[simp] theorem coefficientAt_parabolicMollifyCoefficient
    (A : CoefficientField d) (n : Nat) (z : TimeVelocity d) (i j : Fin d) :
    coefficientAt (parabolicMollifyCoefficient A n) z i j =
      parabolicConvolution (fun y : TimeVelocity d => coefficientAt A y i j)
        (parabolicMollifier d n) z :=
  rfl

private theorem midpoint_isSymm (d : Nat) (lam Lam : Real) :
    (ellipticityMidpoint d lam Lam).IsSymm := by
  unfold ellipticityMidpoint
  exact Matrix.isSymm_one.smul _

private theorem isHermitian_of_isSymm {d : Nat} {M : PDE.Mat d} (hM : M.IsSymm) :
    M.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa using hM.apply i j

private theorem vecDot_smul_right (c : Real) (x : PDE.Vec d) :
    PDE.vecDot x (c • x) = c * PDE.vecNormSq x := by
  unfold PDE.vecNormSq
  unfold PDE.vecDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem quadratic_lower_of_loewner {d : Nat} {lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) (x : PDE.Vec d) :
    lam * PDE.vecNormSq x ≤ PDE.vecDot x (Matrix.mulVec M x) := by
  have hgap : (M - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hLower
  have hquad := hgap.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad

private theorem quadratic_upper_of_loewner {d : Nat} {Lam : Real} {M : PDE.Mat d}
    (hUpper : M ≤ Lam • (1 : PDE.Mat d)) (x : PDE.Vec d) :
    PDE.vecDot x (Matrix.mulVec M x) ≤ Lam * PDE.vecNormSq x := by
  have hgap : (Lam • (1 : PDE.Mat d) - M).PosSemidef := Matrix.le_iff.mp hUpper
  have hquad := hgap.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad

private theorem isSymm_of_lower_ellipticity {d : Nat} {lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) : M.IsSymm := by
  have hgap : (M - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hLower
  apply Matrix.IsSymm.ext
  intro i j
  have hherm := hgap.isHermitian.apply i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij, hji] using hherm

private theorem sum_single_mul {d : Nat} (i : Fin d) (f : Fin d → Real) :
    ∑ x : Fin d, (Pi.single i (1 : Real) : PDE.Vec d) x * f x = f i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _hb hbi
    simp [hbi]
  · simp

private theorem quadratic_single {d : Nat} (M : PDE.Mat d) (i : Fin d) :
    PDE.vecDot (Pi.single i 1) (Matrix.mulVec M (Pi.single i 1)) = M i i := by
  simp only [PDE.vecDot, Matrix.mulVec_single_one]
  exact sum_single_mul i fun x => M x i

private theorem quadratic_single_add {d : Nat} (M : PDE.Mat d) (i j : Fin d) :
    PDE.vecDot (Pi.single i 1 + Pi.single j 1)
      (Matrix.mulVec M (Pi.single i 1 + Pi.single j 1)) =
        M i i + M i j + M j i + M j j := by
  simp only [PDE.vecDot, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply,
    mul_add, add_mul, Finset.sum_add_distrib]
  rw [sum_single_mul i, sum_single_mul i, sum_single_mul j, sum_single_mul j]
  simp only [Matrix.col_apply]
  ring

private theorem vecNormSq_single_add_le_four {d : Nat} (i j : Fin d) :
    PDE.vecNormSq (Pi.single i 1 + Pi.single j 1) ≤ 4 := by
  by_cases hij : i = j
  · subst j
    simp [PDE.vecNormSq, PDE.vecDot, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib, sum_single_mul]
    norm_num
  · simp [PDE.vecNormSq, PDE.vecDot, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib, sum_single_mul, hij]
    norm_num

private theorem vecNormSq_single (i : Fin d) : PDE.vecNormSq (Pi.single i 1) = 1 := by
  simp [PDE.vecNormSq, PDE.vecDot, sum_single_mul]

private theorem coefficient_entry_abs_le {d : Nat} {lam Lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M) (hUpper : M ≤ Lam • (1 : PDE.Mat d))
    (i j : Fin d) :
    |M i j| ≤ 3 * (|lam| + |Lam|) := by
  let q : PDE.Vec d := Pi.single i 1 + Pi.single j 1
  have hqnonneg : 0 ≤ PDE.vecNormSq q := PDE.vecNormSq_nonneg q
  have hqle : PDE.vecNormSq q ≤ 4 := vecNormSq_single_add_le_four i j
  have hquadLower := quadratic_lower_of_loewner hLower q
  have hquadUpper := quadratic_upper_of_loewner hUpper q
  have hquadLower' : -(4 * |lam|) ≤ PDE.vecDot q (Matrix.mulVec M q) := by
    have hlam : -|lam| ≤ lam := neg_abs_le lam
    have hmul : -|lam| * PDE.vecNormSq q ≤ lam * PDE.vecNormSq q :=
      mul_le_mul_of_nonneg_right hlam hqnonneg
    have hfour : -(4 * |lam|) ≤ -|lam| * PDE.vecNormSq q := by
      have hmul' : |lam| * PDE.vecNormSq q ≤ |lam| * 4 :=
        mul_le_mul_of_nonneg_left hqle (abs_nonneg lam)
      nlinarith
    exact hfour.trans (hmul.trans hquadLower)
  have hquadUpper' : PDE.vecDot q (Matrix.mulVec M q) ≤ 4 * |Lam| := by
    have hLam : Lam ≤ |Lam| := le_abs_self Lam
    have hmul : Lam * PDE.vecNormSq q ≤ |Lam| * PDE.vecNormSq q :=
      mul_le_mul_of_nonneg_right hLam hqnonneg
    have hfour : |Lam| * PDE.vecNormSq q ≤ 4 * |Lam| := by
      have hmul' : |Lam| * PDE.vecNormSq q ≤ |Lam| * 4 :=
        mul_le_mul_of_nonneg_left hqle (abs_nonneg Lam)
      nlinarith
    exact hquadUpper.trans (hmul.trans hfour)
  have hdiagLower (k : Fin d) : -|lam| ≤ M k k := by
    have h := quadratic_lower_of_loewner hLower (Pi.single k 1)
    rw [quadratic_single, vecNormSq_single] at h
    have hk : lam ≤ M k k := by simpa only [mul_one] using h
    exact (neg_abs_le lam).trans hk
  have hdiagUpper (k : Fin d) : M k k ≤ |Lam| := by
    have h := quadratic_upper_of_loewner hUpper (Pi.single k 1)
    rw [quadratic_single, vecNormSq_single] at h
    have hk : M k k ≤ Lam := by simpa only [mul_one] using h
    exact hk.trans (le_abs_self Lam)
  have hsymm := isSymm_of_lower_ellipticity hLower
  have hquad : PDE.vecDot q (Matrix.mulVec M q) = M i i + 2 * M i j + M j j := by
    dsimp only [q]
    rw [quadratic_single_add, hsymm.apply i j]
    ring
  rw [abs_le]
  constructor
  · rw [hquad] at hquadLower'
    have hsum : 0 ≤ |lam| + |Lam| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [hdiagUpper i, hdiagUpper j, abs_nonneg lam, abs_nonneg Lam]
  · rw [hquad] at hquadUpper'
    have hsum : 0 ≤ |lam| + |Lam| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [hdiagLower i, hdiagLower j, abs_nonneg lam, abs_nonneg Lam]

private theorem locallyIntegrable_coefficient_entry
    {d : Nat} {lam Lam : Real} {A : CoefficientField d}
    (hA : IsBorelCoefficient A) (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (i j : Fin d) :
    LocallyIntegrable (fun z : TimeVelocity d => coefficientAt A z i j) volume := by
  have hmeas : Measurable (fun z : TimeVelocity d => coefficientAt A z i j) :=
    (measurable_pi_iff.mp (measurable_pi_iff.mp hA i) j)
  intro z
  rcases (volume : Measure (TimeVelocity d)).finiteAt_nhds z with ⟨V, hV, hVfinite⟩
  refine ⟨V, hV, IntegrableOn.of_bound hVfinite hmeas.aestronglyMeasurable
    (3 * (|lam| + |Lam|)) ?_⟩
  filter_upwards with y
  simpa only [Real.norm_eq_abs, coefficientAt, Function.uncurry_def] using coefficient_entry_abs_le
    (hLower y.1 y.2) (hUpper y.1 y.2) i j

/-- An entry of a matrix between scalar lower and upper ellipticity bounds is
bounded by the corresponding absolute scalar bounds. -/
theorem coefficient_entry_abs_le_of_ellipticity
    {d : Nat} {lam Lam : Real} {M : PDE.Mat d}
    (hLower : lam • (1 : PDE.Mat d) ≤ M)
    (hUpper : M ≤ Lam • (1 : PDE.Mat d))
    (i j : Fin d) :
    |M i j| ≤ 3 * (|lam| + |Lam|) :=
  coefficient_entry_abs_le hLower hUpper i j

/-- A Borel coefficient entry with global scalar ellipticity bounds is locally
integrable with respect to time--velocity volume. -/
theorem locallyIntegrable_coefficientAt_entry_of_ellipticity
    {d : Nat} {lam Lam : Real} {A : CoefficientField d}
    (hA : IsBorelCoefficient A)
    (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (i j : Fin d) :
    LocallyIntegrable (fun z : TimeVelocity d => coefficientAt A z i j) volume :=
  locallyIntegrable_coefficient_entry hA hLower hUpper i j

private theorem midpoint_lower (d : Nat) (lam Lam : Real) (hLam : lam ≤ Lam) :
    lam • (1 : PDE.Mat d) ≤ ellipticityMidpoint d lam Lam := by
  apply loewner_lower_of_quadraticForm (midpoint_isSymm d lam Lam)
  intro x
  unfold ellipticityMidpoint
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, vecDot_smul_right]
  have hx : 0 ≤ PDE.vecNormSq x := PDE.vecNormSq_nonneg x
  have hmid : lam ≤ (lam + Lam) / 2 := by linarith
  nlinarith

private theorem midpoint_upper (d : Nat) (lam Lam : Real) (hLam : lam ≤ Lam) :
    ellipticityMidpoint d lam Lam ≤ Lam • (1 : PDE.Mat d) := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact isHermitian_of_isSymm <|
      (Matrix.isSymm_one.smul Lam).sub (midpoint_isSymm d lam Lam)
  · intro x
    unfold ellipticityMidpoint
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub]
    have hx : 0 ≤ PDE.vecNormSq x := PDE.vecNormSq_nonneg x
    have hmid : (lam + Lam) / 2 ≤ Lam := by linarith
    have hcalc : 0 ≤ PDE.vecDot x (Lam • x) -
        PDE.vecDot x (((lam + Lam) / 2) • x) := by
      rw [vecDot_smul_right, vecDot_smul_right]
      nlinarith
    simpa only [PDE.vecDot, dotProduct, star_trivial] using hcalc

/-- A Borel coefficient field with local a.e. ellipticity has a Borel
representative satisfying the same bounds pointwise on the open domain. -/
theorem exists_borel_pointwise_elliptic_representative_on
    (d : Nat) (lam Lam : Real) (A : CoefficientField d)
    (U : Set (TimeVelocity d))
    (hU : IsOpen U) (hA : IsBorelCoefficient A)
    (hSymm : IsSymmetricCoefficientAEOn A U)
    (hLower : HasLowerEllipticityAEOn lam A U)
    (hUpper : HasUpperEllipticityAEOn Lam A U)
    (hLam : lam ≤ Lam) :
    ∃ (N : Set (TimeVelocity d)) (Abar : CoefficientField d),
      MeasurableSet N ∧ volume N = 0 ∧
      (∀ z, coefficientAt Abar z =
        if z ∈ N then ellipticityMidpoint d lam Lam else coefficientAt A z) ∧
      IsBorelCoefficient Abar ∧
      coefficientAt Abar =ᵐ[timeVelocityVolumeOn U] coefficientAt A ∧
      (∀ z ∈ U, (coefficientAt Abar z).IsSymm) ∧
      (∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt Abar z) ∧
      (∀ z ∈ U, coefficientAt Abar z ≤ Lam • (1 : PDE.Mat d)) := by
  let good : TimeVelocity d → Prop := fun z =>
    (coefficientAt A z).IsSymm ∧
      lam • (1 : PDE.Mat d) ≤ coefficientAt A z ∧
        coefficientAt A z ≤ Lam • (1 : PDE.Mat d)
  let E : Set (TimeVelocity d) := U ∩ {z | ¬good z}
  have hgood : ∀ᵐ z ∂timeVelocityVolumeOn U, good z :=
    hSymm.and (hLower.and hUpper)
  have hbad : (timeVelocityVolumeOn U) {z | ¬good z} = 0 := ae_iff.mp hgood
  have hEres : (timeVelocityVolumeOn U) E = 0 :=
    measure_mono_null (by
      intro z hz
      exact hz.2) hbad
  have hE : volume E = 0 := by
    rw [Measure.restrict_apply₀' hU.measurableSet.nullMeasurableSet] at hEres
    have hEU : E ∩ U = E := by
      ext z
      simp only [E, mem_inter_iff]
      tauto
    rwa [hEU] at hEres
  obtain ⟨N, hEN, hNmeas, hN⟩ := exists_measurable_superset_of_null hE
  let Abar : CoefficientField d :=
    modifyCoefficientOnNullSet A N (ellipticityMidpoint d lam Lam)
  have hAbar : IsBorelCoefficient Abar := by
    change Measurable fun z => if z ∈ N then ellipticityMidpoint d lam Lam else
      coefficientAt A z
    exact Measurable.ite hNmeas measurable_const hA
  have hNae : ∀ᵐ z ∂timeVelocityVolumeOn U, z ∉ N := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_mem_eq]
    rw [show timeVelocityVolumeOn U = volume.restrict U by rfl,
      Measure.restrict_apply hNmeas]
    exact measure_mono_null inter_subset_left hN
  have hAbarAE : coefficientAt Abar =ᵐ[timeVelocityVolumeOn U] coefficientAt A := by
    filter_upwards [hNae] with z hz
    simp only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_neg hz]
  refine ⟨N, Abar, hNmeas, hN, ?_, hAbar, hAbarAE, ?_, ?_, ?_⟩
  · intro z
    exact coefficientAt_modifyCoefficientOnNullSet A N (ellipticityMidpoint d lam Lam) z
  · intro z hzU
    by_cases hzN : z ∈ N
    · simp only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_pos hzN]
      exact midpoint_isSymm d lam Lam
    · have hzE : z ∉ E := fun hzE => hzN (hEN hzE)
      have hgoodz : good z := by
        by_contra hnot
        exact hzE ⟨hzU, hnot⟩
      simpa only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_neg hzN] using hgoodz.1
  · intro z hzU
    by_cases hzN : z ∈ N
    · simpa only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_pos hzN] using
        midpoint_lower d lam Lam hLam
    · have hzE : z ∉ E := fun hzE => hzN (hEN hzE)
      have hgoodz : good z := by
        by_contra hnot
        exact hzE ⟨hzU, hnot⟩
      simpa only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_neg hzN] using hgoodz.2.1
  · intro z hzU
    by_cases hzN : z ∈ N
    · simpa only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_pos hzN] using
        midpoint_upper d lam Lam hLam
    · have hzE : z ∉ E := fun hzE => hzN (hEN hzE)
      have hgoodz : good z := by
        by_contra hnot
        exact hzE ⟨hzU, hnot⟩
      simpa only [Abar, coefficientAt_modifyCoefficientOnNullSet, if_neg hzN] using hgoodz.2.2

/-- A Borel coefficient field stays Borel after midpoint extension from an
open set. -/
theorem extendCoefficientByMidpoint_isBorel
    (d : Nat) (lam Lam : Real) (Abar : CoefficientField d)
    (U : Set (TimeVelocity d))
    (hU : IsOpen U) (hAbar : IsBorelCoefficient Abar) :
    IsBorelCoefficient
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) := by
  change Measurable fun z => if z ∈ U then coefficientAt Abar z else
    ellipticityMidpoint d lam Lam
  exact Measurable.ite hU.measurableSet hAbar measurable_const

/-- Midpoint extension preserves exact lower and upper ellipticity and
symmetry globally. -/
theorem extendCoefficientByMidpoint_global_ellipticity
    (d : Nat) (lam Lam : Real) (Abar : CoefficientField d)
    (U : Set (TimeVelocity d))
    (hAbarSymm : ∀ z ∈ U, (coefficientAt Abar z).IsSymm)
    (hAbarLower : ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt Abar z)
    (hAbarUpper : ∀ z ∈ U, coefficientAt Abar z ≤ Lam • (1 : PDE.Mat d))
    (hLam : lam ≤ Lam) :
    IsSymmetricCoefficient
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) ∧
    HasLowerEllipticity lam
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) ∧
    HasUpperEllipticity Lam
      (extendCoefficientByMidpoint Abar U (ellipticityMidpoint d lam Lam)) := by
  constructor
  · intro t v
    by_cases hUV : (t, v) ∈ U
    · simpa only [extendCoefficientByMidpoint, if_pos hUV, coefficientAt,
        Function.uncurry_def] using
        hAbarSymm (t, v) hUV
    · simpa only [extendCoefficientByMidpoint, if_neg hUV] using
        midpoint_isSymm d lam Lam
  constructor
  · intro t v
    by_cases hUV : (t, v) ∈ U
    · simpa only [extendCoefficientByMidpoint, if_pos hUV, coefficientAt,
        Function.uncurry_def] using
        hAbarLower (t, v) hUV
    · simpa only [extendCoefficientByMidpoint, if_neg hUV] using
        midpoint_lower d lam Lam hLam
  · intro t v
    by_cases hUV : (t, v) ∈ U
    · simpa only [extendCoefficientByMidpoint, if_pos hUV, coefficientAt,
        Function.uncurry_def] using
        hAbarUpper (t, v) hUV
    · simpa only [extendCoefficientByMidpoint, if_neg hUV] using
        midpoint_upper d lam Lam hLam

/-- Entrywise mollification produces a smooth coefficient field. -/
theorem isSmoothCoefficient_parabolicMollifyCoefficient
    (d : Nat) (lam Lam : Real) (A : CoefficientField d)
    (hA : IsBorelCoefficient A)
    (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat) :
    IsSmoothCoefficient (parabolicMollifyCoefficient A n) := by
  change ContDiff Real (⊤ : ℕ∞)
    (fun z i j => coefficientAt (parabolicMollifyCoefficient A n) z i j)
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  change ContDiff Real (⊤ : ℕ∞) (parabolicConvolution
    (fun z : TimeVelocity d => coefficientAt A z i j) (parabolicMollifier d n))
  exact contDiff_parabolicConvolution
    (locallyIntegrable_coefficient_entry hA hLower hUpper i j)
    (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)

/-- Entrywise mollification preserves pointwise matrix symmetry. -/
theorem isSymmetricCoefficient_parabolicMollifyCoefficient
    (d : Nat) (lam Lam : Real) (A : CoefficientField d)
    (hSymm : IsSymmetricCoefficient A) (n : Nat) :
    IsSymmetricCoefficient (parabolicMollifyCoefficient A n) := by
  let _ := lam
  let _ := Lam
  intro t v
  apply Matrix.IsSymm.ext
  intro i j
  have hentries : (fun z : TimeVelocity d => coefficientAt A z j i) =
      fun z : TimeVelocity d => coefficientAt A z i j := by
    funext z
    exact hSymm z.1 z.2 |>.apply i j
  simp only [parabolicMollifyCoefficient]
  rw [hentries]

private theorem locallyIntegrable_coefficient_quadratic
    {d : Nat} {lam Lam : Real} {A : CoefficientField d}
    (hA : IsBorelCoefficient A) (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (x : PDE.Vec d) :
    LocallyIntegrable (fun z : TimeVelocity d =>
      PDE.vecDot x (Matrix.mulVec (coefficientAt A z) x)) volume := by
  have hterm (i j : Fin d) : LocallyIntegrable
      (fun z : TimeVelocity d => (x i * x j) • coefficientAt A z i j) volume :=
    (locallyIntegrable_coefficient_entry hA hLower hUpper i j).smul (x i * x j)
  have hrow (i : Fin d) : LocallyIntegrable
      (fun z : TimeVelocity d => ∑ j : Fin d, (x i * x j) • coefficientAt A z i j) volume := by
    simpa only [Finset.sum_const_zero, Finset.sum_apply] using
      locallyIntegrable_finset_sum Finset.univ (fun j _hj => hterm i j)
  have hsum : LocallyIntegrable
      (fun z : TimeVelocity d => ∑ i : Fin d, ∑ j : Fin d,
        (x i * x j) • coefficientAt A z i j) volume := by
    simpa only [Finset.sum_const_zero, Finset.sum_apply] using
      locallyIntegrable_finset_sum Finset.univ (fun i _hi => hrow i)
  convert hsum using 1
  ext z
  simp only [PDE.vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem quadratic_parabolicMollifyCoefficient_eq
    {d : Nat} {lam Lam : Real} {A : CoefficientField d}
    (hA : IsBorelCoefficient A) (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat)
    (x z : TimeVelocity d) :
    PDE.vecDot x.2
      (Matrix.mulVec (coefficientAt (parabolicMollifyCoefficient A n) z) x.2) =
      parabolicConvolution
        (fun y : TimeVelocity d =>
          PDE.vecDot x.2 (Matrix.mulVec (coefficientAt A y) x.2))
        (parabolicMollifier d n) z := by
  let rhoz : TimeVelocity d → Real := fun y => parabolicMollifier d n (z - y)
  have hrhozCont : Continuous rhoz := by
    dsimp only [rhoz]
    exact (contDiff_parabolicMollifier d n).continuous.comp
      (continuous_const.sub continuous_id)
  have hrhozCompact : HasCompactSupport rhoz := by
    dsimp only [rhoz]
    exact (hasCompactSupport_parabolicMollifier d n).comp_homeomorph (Homeomorph.subLeft z)
  have hint (i j : Fin d) : Integrable
      (fun y : TimeVelocity d => (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y) volume := by
    have hloc :=
      (locallyIntegrable_coefficient_entry hA hLower hUpper i j).smul (x.2 i * x.2 j)
    convert hloc.integrable_smul_right_of_hasCompactSupport hrhozCont hrhozCompact using 1
  change (∑ i : Fin d, x.2 i * ∑ j : Fin d,
      (∫ y, coefficientAt A y i j * rhoz y) * x.2 j) =
    ∫ y, (∑ i : Fin d, x.2 i * ∑ j : Fin d,
      coefficientAt A y i j * x.2 j) * rhoz y
  have hsum : (fun y : TimeVelocity d =>
      (∑ i : Fin d, x.2 i * ∑ j : Fin d, coefficientAt A y i j * x.2 j) * rhoz y) =
      fun y => ∑ i : Fin d, ∑ j : Fin d,
        (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y := by
    funext y
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    calc
      (x.2 i * ∑ j : Fin d, coefficientAt A y i j * x.2 j) * rhoz y =
          x.2 i * ((∑ j : Fin d, coefficientAt A y i j * x.2 j) * rhoz y) := by
            ring
      _ = x.2 i * ∑ j : Fin d, (coefficientAt A y i j * x.2 j) * rhoz y := by
            rw [Finset.sum_mul]
      _ = ∑ j : Fin d, x.2 i * x.2 j * coefficientAt A y i j * rhoz y := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
  rw [hsum, integral_finset_sum Finset.univ]
  · rw [show (fun i : Fin d => ∫ y, ∑ j : Fin d,
        (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y) =
        fun i => ∑ j : Fin d, ∫ y,
          (x.2 i * x.2 j) * coefficientAt A y i j * rhoz y by
      funext i
      rw [integral_finset_sum Finset.univ]
      intro j _hj
      exact hint i j]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  · intro i _hi
    apply integrable_finset_sum
    intro j _hj
    exact hint i j

private theorem parabolicConvolution_eq_normed_left
    {d : Nat} (f : TimeVelocity d → Real) (n : Nat) (z : TimeVelocity d) :
    parabolicConvolution f (parabolicMollifier d n) z =
      (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real,
        (volume : Measure (TimeVelocity d))] f) z := by
  rw [← convolution_flip]
  simp only [parabolicConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  change f y * parabolicMollifier d n (z - y) =
    parabolicMollifier d n (z - y) * f y
  ring

/-- Entrywise mollification preserves the exact lower Loewner ellipticity
bound. -/
theorem hasLowerEllipticity_parabolicMollifyCoefficient
    (d : Nat) (lam Lam : Real) (A : CoefficientField d)
    (hA : IsBorelCoefficient A)
    (hSymm : IsSymmetricCoefficient A)
    (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat) :
    HasLowerEllipticity lam (parabolicMollifyCoefficient A n) := by
  intro t v
  have hMollSymm := isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam A hSymm n
  apply loewner_lower_of_quadraticForm
    (hMollSymm t v)
  intro x
  let q : TimeVelocity d := (t, v)
  let quad : TimeVelocity d → Real := fun y =>
    PDE.vecDot x (Matrix.mulVec (coefficientAt A y) x)
  let c : Real := lam * PDE.vecNormSq x
  have hquadLoc : LocallyIntegrable quad volume :=
    locallyIntegrable_coefficient_quadratic hA hLower hUpper x
  have hconstLoc : LocallyIntegrable (fun _ : TimeVelocity d => c) volume :=
    locallyIntegrable_const c
  have hquadExists := (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
    (ContinuousLinearMap.lsmul Real Real) (contDiff_parabolicMollifier d n).continuous hquadLoc q
  have hconstExists := (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
    (ContinuousLinearMap.lsmul Real Real) (contDiff_parabolicMollifier d n).continuous hconstLoc q
  have hpoint : ∀ y : TimeVelocity d, c ≤ quad y := by
    intro y
    exact quadratic_lower_of_loewner (hLower y.1 y.2) x
  have hmono := convolution_mono_right hconstExists hquadExists
    (parabolicMollifier_nonneg d n) hpoint
  have hconst :
      (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
        (fun _ : TimeVelocity d => c)) q = c := by
    exact ContDiffBump.normed_convolution_eq_right
      (φ := parabolicMollifierBump d n) (μ := volume) (fun _ _ => rfl)
  have hquad :
      PDE.vecDot x (Matrix.mulVec
        (coefficientAt (parabolicMollifyCoefficient A n) q) x) =
        (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume] quad) q := by
    calc
      PDE.vecDot x (Matrix.mulVec
          (coefficientAt (parabolicMollifyCoefficient A n) q) x) =
          parabolicConvolution quad (parabolicMollifier d n) q := by
            simpa only [quad] using
              (quadratic_parabolicMollifyCoefficient_eq hA hLower hUpper n (0, x) q)
      _ = (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume] quad) q :=
        parabolicConvolution_eq_normed_left quad n q
  change c ≤ PDE.vecDot x (Matrix.mulVec
    (coefficientAt (parabolicMollifyCoefficient A n) q) x)
  rw [hquad]
  exact hconst.symm.le.trans hmono

/-- Entrywise mollification preserves the exact upper Loewner ellipticity
bound. -/
theorem hasUpperEllipticity_parabolicMollifyCoefficient
    (d : Nat) (lam Lam : Real) (A : CoefficientField d)
    (hA : IsBorelCoefficient A)
    (hSymm : IsSymmetricCoefficient A)
    (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) (n : Nat) :
    HasUpperEllipticity Lam (parabolicMollifyCoefficient A n) := by
  intro t v
  have hMollSymm := isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam A hSymm n
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact isHermitian_of_isSymm <|
      (Matrix.isSymm_one.smul Lam).sub
        (hMollSymm t v)
  · intro x
    let q : TimeVelocity d := (t, v)
    let quad : TimeVelocity d → Real := fun y =>
      PDE.vecDot x (Matrix.mulVec (coefficientAt A y) x)
    let c : Real := Lam * PDE.vecNormSq x
    have hquadLoc : LocallyIntegrable quad volume :=
      locallyIntegrable_coefficient_quadratic hA hLower hUpper x
    have hconstLoc : LocallyIntegrable (fun _ : TimeVelocity d => c) volume :=
      locallyIntegrable_const c
    have hquadExists := (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
      (ContinuousLinearMap.lsmul Real Real) (contDiff_parabolicMollifier d n).continuous hquadLoc q
    have hconstExists := (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
      (ContinuousLinearMap.lsmul Real Real) (contDiff_parabolicMollifier d n).continuous hconstLoc q
    have hpoint : ∀ y : TimeVelocity d, quad y ≤ c := by
      intro y
      exact quadratic_upper_of_loewner (hUpper y.1 y.2) x
    have hmono := convolution_mono_right hquadExists hconstExists
      (parabolicMollifier_nonneg d n) hpoint
    have hconst :
        (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
          (fun _ : TimeVelocity d => c)) q = c := by
      exact ContDiffBump.normed_convolution_eq_right
        (φ := parabolicMollifierBump d n) (μ := volume) (fun _ _ => rfl)
    have hquad :
        PDE.vecDot x (Matrix.mulVec
          (coefficientAt (parabolicMollifyCoefficient A n) q) x) =
          (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume] quad) q := by
      calc
        PDE.vecDot x (Matrix.mulVec
            (coefficientAt (parabolicMollifyCoefficient A n) q) x) =
            parabolicConvolution quad (parabolicMollifier d n) q := by
              simpa only [quad] using
                (quadratic_parabolicMollifyCoefficient_eq hA hLower hUpper n (0, x) q)
        _ = (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume] quad) q :=
          parabolicConvolution_eq_normed_left quad n q
    have hupperQuad : PDE.vecDot x (Matrix.mulVec
        (coefficientAt (parabolicMollifyCoefficient A n) q) x) ≤ c := by
      rw [hquad]
      exact hmono.trans hconst.le
    have hcalc : 0 ≤ star x ⬝ᵥ
        (Matrix.mulVec (Lam • (1 : PDE.Mat d) -
          coefficientAt (parabolicMollifyCoefficient A n) q) x) := by
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      simpa only [c, PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using
        sub_nonneg.mpr hupperQuad
    exact hcalc

/-- The right parabolic convolution converges almost everywhere for
every locally integrable scalar function. -/
theorem tendsto_ae_parabolicConvolution_of_locallyIntegrable
    {d : Nat} {f : TimeVelocity d → Real}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ z ∂volume,
      Tendsto (fun n =>
        parabolicConvolution f (parabolicMollifier d n) z)
        atTop (nhds (f z)) := by
  have hratio : ∀ᶠ n : Nat in atTop,
      (parabolicMollifierBump d n).rOut ≤ 2 * (parabolicMollifierBump d n).rIn :=
    Filter.Eventually.of_forall fun n => by
      rw [parabolicMollifierBump_rOut]
      change parabolicMollifierScale n ≤ 2 * (parabolicMollifierScale n / 2)
      ring_nf
      exact le_rfl
  have hleft := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun n : Nat => parabolicMollifierBump d n)
    tendsto_parabolicMollifierScale_zero hratio hf
  filter_upwards [hleft] with z hz
  apply hz.congr'
  filter_upwards with n
  simpa only [parabolicMollifier] using (parabolicConvolution_eq_normed_left f n z).symm

/-- Entrywise parabolic coefficient mollification converges almost everywhere
to every globally Borel, elliptically bounded coefficient field. -/
theorem ae_tendsto_parabolicMollifyCoefficient
    (d : Nat) (lam Lam : Real) (A : CoefficientField d)
    (hA : IsBorelCoefficient A)
    (hLower : HasLowerEllipticity lam A)
    (hUpper : HasUpperEllipticity Lam A) :
    ∀ᵐ z ∂(volume : Measure (TimeVelocity d)),
      Filter.Tendsto
        (fun n : Nat => coefficientAt (parabolicMollifyCoefficient A n) z)
        Filter.atTop (nhds (coefficientAt A z)) := by
  have hentries : ∀ᵐ z ∂(volume : Measure (TimeVelocity d)),
      ∀ i j : Fin d, Tendsto
        (fun n : Nat => coefficientAt (parabolicMollifyCoefficient A n) z i j)
        atTop (nhds (coefficientAt A z i j)) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    simpa only [coefficientAt_parabolicMollifyCoefficient] using
      (tendsto_ae_parabolicConvolution_of_locallyIntegrable
        (locallyIntegrable_coefficient_entry hA hLower hUpper i j))
  filter_upwards [hentries] with z hz
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact hz i j

/-- On a restricted domain, mollifications of a bounded Borel extension
converge almost everywhere to any coefficient field agreeing with it there. -/
theorem ae_tendsto_parabolicMollified_extension_eq_original_on
    (d : Nat) (lam Lam : Real) (A Aext : CoefficientField d)
    (U : Set (TimeVelocity d))
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext) :
    ∀ᵐ z ∂timeVelocityVolumeOn U,
      Filter.Tendsto
        (fun n : Nat => coefficientAt (parabolicMollifyCoefficient Aext n) z)
        Filter.atTop (nhds (coefficientAt A z)) := by
  have hglobal := ae_tendsto_parabolicMollifyCoefficient d lam Lam Aext
    hExtBorel hExtLower hExtUpper
  have hrestricted : ∀ᵐ z ∂timeVelocityVolumeOn U,
      Tendsto (fun n : Nat => coefficientAt (parabolicMollifyCoefficient Aext n) z)
        atTop (nhds (coefficientAt Aext z)) :=
    hglobal.filter_mono <| ae_mono <| Measure.restrict_le_self
  filter_upwards [hrestricted, hExtAE] with z hz hEq
  simpa only [hEq] using hz

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

/-- A pointwise lower Loewner ellipticity bound entails pointwise matrix
symmetry. -/
theorem isSymmetricCoefficient_of_hasLowerEllipticity
    {d : Nat} {lam : Real} {A : CoefficientField d}
    (hLower : HasLowerEllipticity lam A) :
    IsSymmetricCoefficient A := by
  intro t v
  exact isSymm_of_lower_ellipticity (hLower t v)

end HypoellipticAleksandrov.Parabolic
