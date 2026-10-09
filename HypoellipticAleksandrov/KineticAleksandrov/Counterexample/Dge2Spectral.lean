module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SpectralMeasurable
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The canonical spectral trace solver of Appendix C

The positive and negative masses are traces of the actual matrix positive parts.
The trace equation is algebraic; uniform ellipticity requires the separate sign argument.
-/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Positive spectral part of a real matrix. -/
def positiveSpectralPart {d : ℕ} (M : PDE.Mat d) : PDE.Mat d := cfc (max (0 : ℝ)) M

/-- Sum of the positive eigenvalues. -/
def positiveSpectralMass {d : ℕ} (M : PDE.Mat d) : ℝ := (positiveSpectralPart M).trace

/-- Sum of the absolute values of the negative eigenvalues. -/
def negativeSpectralMass {d : ℕ} (M : PDE.Mat d) : ℝ := positiveSpectralMass (-M)

/-- The source's canonical weighted spectral matrix. -/
def spectralTraceMatrix {d : ℕ} (M : PDE.Mat d) (b cminus : ℝ) : PDE.Mat d :=
  ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) •
      positiveSpectralProjection M +
    cminus • negativeSpectralProjection M + zeroSpectralProjection M

private theorem continuousOn_matrix_spectrum {d : ℕ} (M : PDE.Mat d) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

/-- The positive projection times the original matrix is its positive part. -/
theorem positiveSpectralProjection_mul {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    positiveSpectralProjection M * M = positiveSpectralPart M := by
  unfold positiveSpectralProjection positiveSpectralPart
  conv_lhs => rhs; rw [← cfc_id (p := IsSelfAdjoint) ℝ M hM.isSelfAdjoint]
  rw [← cfc_mul (p := IsSelfAdjoint) positiveSpectralIndicator (id : ℝ → ℝ) M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  apply cfc_congr
  intro t _
  by_cases ht : 0 < t
  · simp [positiveSpectralIndicator, ht, max_eq_right ht.le]
  · simp [positiveSpectralIndicator, ht, max_eq_left (le_of_not_gt ht)]

/-- The positive projection has contraction equal to the positive spectral mass. -/
theorem contraction_positiveSpectralProjection {d : ℕ}
    (M : PDE.Mat d) (hM : M.IsHermitian) :
    matrixContraction (positiveSpectralProjection M) M = positiveSpectralMass M := by
  rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hM.isSymm,
    positiveSpectralProjection_mul M hM]
  rfl

/-- The negative projection has contraction equal to minus the negative spectral mass. -/
theorem contraction_negativeSpectralProjection {d : ℕ}
    (M : PDE.Mat d) (hM : M.IsHermitian) :
    matrixContraction (negativeSpectralProjection M) M = -negativeSpectralMass M := by
  have hh := contraction_positiveSpectralProjection (-M) hM.neg
  change matrixContraction (positiveSpectralProjection (-M)) M =
    -positiveSpectralMass (-M)
  rw [matrixContraction_neg_right] at hh
  linarith

/-- The difference of the spectral positive parts is the original Hermitian matrix. -/
theorem spectralParts_sub {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    positiveSpectralPart M - positiveSpectralPart (-M) = M := by
  unfold positiveSpectralPart
  rw [← cfc_comp_neg (p := IsSelfAdjoint) (max (0 : ℝ)) M
    (by fun_prop) hM.isSelfAdjoint,
    ← cfc_sub (p := IsSelfAdjoint) (max (0 : ℝ)) (fun t => max 0 (-t)) M
      (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  conv_rhs => rw [← cfc_id (p := IsSelfAdjoint) ℝ M hM.isSelfAdjoint]
  apply cfc_congr
  intro t _
  dsimp
  by_cases ht : 0 ≤ t
  · rw [max_eq_right ht, max_eq_left (neg_nonpos.mpr ht)]
    ring
  · have htn : t ≤ 0 := le_of_not_ge ht
    rw [max_eq_left htn, max_eq_right (neg_nonneg.mpr htn)]
    ring

/-- The matrix trace is the positive spectral mass minus the negative spectral mass. -/
theorem trace_eq_spectralMass_sub {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    M.trace = positiveSpectralMass M - negativeSpectralMass M := by
  have hh := congrArg Matrix.trace (spectralParts_sub M hM)
  simpa only [Matrix.trace_sub, positiveSpectralMass, negativeSpectralMass] using hh.symm

/-- The zero projection has zero contraction with the original matrix. -/
theorem contraction_zeroSpectralProjection {d : ℕ} (M : PDE.Mat d)
    (hM : M.IsHermitian) : matrixContraction (zeroSpectralProjection M) M = 0 := by
  unfold zeroSpectralProjection
  have hsub (A B : PDE.Mat d) : matrixContraction (A - B) M =
      matrixContraction A M - matrixContraction B M := by
    rw [sub_eq_add_neg, matrixContraction_add_left, matrixContraction_neg_left,
      sub_eq_add_neg]
  rw [hsub, hsub, contraction_positiveSpectralProjection M hM,
    contraction_negativeSpectralProjection M hM,
    matrixContraction_eq_trace_mul_of_isSymm _ _ hM.isSymm, one_mul,
    trace_eq_spectralMass_sub M hM]
  ring

/-- The literal source matrix solves the exact trace equation when the positive mass is nonzero. -/
theorem spectral_trace_solver {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus : ℝ) (hm : positiveSpectralMass M ≠ 0) :
    matrixContraction (spectralTraceMatrix M b cminus) M = b := by
  unfold spectralTraceMatrix
  rw [matrixContraction_add_left, matrixContraction_add_left,
    matrixContraction_smul_left, matrixContraction_smul_left,
    contraction_positiveSpectralProjection M hM,
    contraction_negativeSpectralProjection M hM, contraction_zeroSpectralProjection M hM]
  field_simp
  ring

/-- Scalar eigenvalue of the trace solver in each of the three spectral regions. -/
def weightedSpectralSelector (w cminus t : ℝ) : ℝ :=
  if 0 < t then w else if t < 0 then cminus else 1

/-- The negative projection is the functional calculus of the negative spectral indicator. -/
theorem negativeSpectralProjection_eq {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    negativeSpectralProjection M = cfc (fun t => positiveSpectralIndicator (-t)) M := by
  unfold negativeSpectralProjection positiveSpectralProjection
  symm
  exact cfc_comp_neg (p := IsSelfAdjoint) positiveSpectralIndicator M
    (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop) hM.isSelfAdjoint

/-- Functional-calculus expression for the literal weighted matrix. -/
theorem spectralTraceMatrix_eq_cfc {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus : ℝ) :
    spectralTraceMatrix M b cminus =
      cfc (weightedSpectralSelector
        ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus) M := by
  let w := (b + cminus * negativeSpectralMass M) / positiveSpectralMass M
  have hs : cfc (weightedSpectralSelector w cminus) M =
      cfc (fun t => w * positiveSpectralIndicator t +
        cminus * positiveSpectralIndicator (-t) +
        (1 - positiveSpectralIndicator t - positiveSpectralIndicator (-t))) M := by
    apply cfc_congr
    intro t _
    by_cases ht : 0 < t
    · simp [weightedSpectralSelector, positiveSpectralIndicator, ht, not_lt.mpr ht.le]
    · by_cases hn : t < 0
      · simp [weightedSpectralSelector, positiveSpectralIndicator, ht, hn]
      · simp [weightedSpectralSelector, positiveSpectralIndicator, ht, hn]
  rw [hs]
  rw [cfc_add (p := IsSelfAdjoint) M
    (fun t => w * positiveSpectralIndicator t + cminus * positiveSpectralIndicator (-t))
    (fun t => 1 - positiveSpectralIndicator t - positiveSpectralIndicator (-t))
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  rw [cfc_add (p := IsSelfAdjoint) M (fun t => w * positiveSpectralIndicator t)
    (fun t => cminus * positiveSpectralIndicator (-t))
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _)]
  rw [cfc_const_mul (p := IsSelfAdjoint) w positiveSpectralIndicator M
    (continuousOn_matrix_spectrum M _),
    cfc_const_mul (p := IsSelfAdjoint) cminus (fun t => positiveSpectralIndicator (-t)) M
    (continuousOn_matrix_spectrum M _)]
  rw [cfc_sub (p := IsSelfAdjoint) (fun t => 1 - positiveSpectralIndicator t)
    (fun t => positiveSpectralIndicator (-t)) M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _),
    cfc_sub (p := IsSelfAdjoint) (fun _ : ℝ => 1) positiveSpectralIndicator M
    (continuousOn_matrix_spectrum M _) (continuousOn_matrix_spectrum M _),
    cfc_const (p := IsSelfAdjoint) 1 M hM.isSelfAdjoint]
  simp only [map_one]
  rw [← negativeSpectralProjection_eq M hM]
  rfl

/-- The trace-solver spectrum lies between the minimum and maximum of its three weights. -/
theorem spectralTraceMatrix_bounds {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus : ℝ) :
    let w := (b + cminus * negativeSpectralMass M) / positiveSpectralMass M
    (min 1 (min w cminus)) • (1 : PDE.Mat d) ≤ spectralTraceMatrix M b cminus ∧
      spectralTraceMatrix M b cminus ≤ (max 1 (max w cminus)) • (1 : PDE.Mat d) := by
  dsimp only
  rw [spectralTraceMatrix_eq_cfc M hM]
  constructor
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply algebraMap_le_cfc _ _ M
      (hf := continuousOn_matrix_spectrum M _) (ha := hM.isSelfAdjoint)
    intro t _
    unfold weightedSpectralSelector
    split_ifs
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact min_le_left _ _
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply cfc_le_algebraMap _ _ M
      (hf := continuousOn_matrix_spectrum M _) (ha := hM.isSelfAdjoint)
    intro t _
    unfold weightedSpectralSelector
    split_ifs
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact le_max_left _ _

/-- All three pointwise weights are strictly positive under the source's sign conditions. -/
theorem spectralTraceMatrix_lower_pos {d : ℕ} (M : PDE.Mat d) (b cminus : ℝ)
    (hm : 0 < positiveSpectralMass M) (hc : 0 < cminus)
    (hb : 0 < b + cminus * negativeSpectralMass M) :
    0 < min 1 (min
      ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus) := by
  exact lt_min zero_lt_one (lt_min (div_pos hb hm) hc)

/-- The positive spectral mass of a continuous Hermitian field is continuous. -/
theorem continuous_positiveSpectralMass {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian) :
    Continuous (fun x => positiveSpectralMass (M x)) := by
  have hh : Continuous (fun x => cfc (max (0 : ℝ)) (M x)) :=
    Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (max (0 : ℝ))
      (by simp) hM (fun x => (hherm x).isSelfAdjoint) (by fun_prop)
  exact hh.matrix_trace

/-- The negative spectral mass of a continuous Hermitian field is continuous. -/
theorem continuous_negativeSpectralMass {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian) :
    Continuous (fun x => negativeSpectralMass (M x)) :=
  continuous_positiveSpectralMass (fun x => -M x) hM.neg (fun x => (hherm x).neg)

/-- Every entry of the source trace matrix is measurable for continuous input fields. -/
theorem measurable_spectralTraceMatrix {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian)
    (b : X → ℝ) (hb : Measurable b) (cminus : ℝ) (i k : Fin d) :
    Measurable (fun x => spectralTraceMatrix (M x) (b x) cminus i k) := by
  have hp := (continuous_positiveSpectralMass M hM hherm).measurable
  have hn := (continuous_negativeSpectralMass M hM hherm).measurable
  have hproj := (measurable_positiveSpectralProjection M hM hherm).eval_matrix (i := i) (j := k)
  have hneg := (measurable_negativeSpectralProjection M hM hherm).eval_matrix (i := i) (j := k)
  have hw : Measurable (fun x =>
      (b x + cminus * negativeSpectralMass (M x)) / positiveSpectralMass (M x)) :=
    (hb.add (measurable_const.mul hn)).div hp
  unfold spectralTraceMatrix zeroSpectralProjection
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((hw.mul hproj).add (measurable_const.mul hneg)).add
    ((measurable_const.sub hproj).sub hneg)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
