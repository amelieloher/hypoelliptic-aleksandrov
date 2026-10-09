module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCutoffJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralCompact

/-! # A uniform canonical spectral solver on the cutoff parameter compact set -/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The compact source region for the cutoff spectral weights. -/
def cutoffParameterSet (d : ℕ) (R : ℝ) : Set (PDE.Vec d × PDE.Vec d) :=
  {q | PDE.vecNormSq q.2 = 1 ∧ PDE.vecEuclideanNorm q.1 ≤ 2 * R}

/-- The actual cutoff parameter set is compact. -/
theorem isCompact_cutoffParameterSet (d : ℕ) (R : ℝ) :
    IsCompact (cutoffParameterSet d R) := by
  have hclosed : IsClosed (cutoffParameterSet d R) :=
    (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_snd) continuous_const).inter
      (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_fst) continuous_const)
  apply (isCompact_closedBall (0 : PDE.Vec d × PDE.Vec d) (max 1 (2 * R))).of_isClosed_subset
    hclosed
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have he : PDE.vecEuclideanNorm q.2 = 1 := by
    unfold PDE.vecEuclideanNorm
    rw [hq.1]
    norm_num
  exact max_le ((PDE.norm_le_vecEuclideanNorm _).trans (hq.2.trans (le_max_right _ _)))
    ((PDE.norm_le_vecEuclideanNorm _).trans (by simpa only [he] using le_max_left 1 (2 * R)))

/-- Joint finite bounds for the canonical spectral weights imply matrix bounds. -/
theorem spectralTraceMatrix_uniform_bounds {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian)
    (b cminus lower upper : ℝ)
    (hlo : lower ≤ (b + cminus * negativeSpectralMass M) / positiveSpectralMass M)
    (hhi : (b + cminus * negativeSpectralMass M) / positiveSpectralMass M ≤ upper) :
    min 1 (min lower cminus) • (1 : PDE.Mat d) ≤ spectralTraceMatrix M b cminus ∧
      spectralTraceMatrix M b cminus ≤ max 1 (max upper cminus) • (1 : PDE.Mat d) := by
  rw [spectralTraceMatrix_eq_cfc M hM]
  have hcont : ContinuousOn (weightedSpectralSelector
      ((b + cminus * negativeSpectralMass M) / positiveSpectralMass M) cminus)
      (spectrum ℝ M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  constructor
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply algebraMap_le_cfc _ _ M (ha := hM.isSelfAdjoint) (hf := hcont)
    intro t _
    unfold weightedSpectralSelector
    split_ifs
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans hlo
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact min_le_left _ _
  · rw [← Algebra.algebraMap_eq_smul_one]
    apply cfc_le_algebraMap _ _ M (ha := hM.isSelfAdjoint) (hf := hcont)
    intro t _
    unfold weightedSpectralSelector
    split_ifs
    · exact hhi.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact le_max_left _ _

/-- The actual cutoff has a measurable uniformly elliptic trace solver on its compact core. -/
theorem exists_cutoff_spectral_solver_on_compact (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R cminus lam Lam : ℝ,
      0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ 1 ≤ cminus ∧ 0 < lam ∧ lam ≤ Lam ∧
      (∀ i k, Measurable (fun q : PDE.Vec d × PDE.Vec d =>
        spectralTraceMatrix (cutoffMatrix alpha C₀ sigma R q.1 q.2)
          (ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) q.1 q.2) cminus i k)) ∧
      ∀ y e : PDE.Vec d, (y, e) ∈ cutoffParameterSet d R →
        matrixContraction
          (spectralTraceMatrix (cutoffMatrix alpha C₀ sigma R y e)
            (ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e) cminus)
          (cutoffMatrix alpha C₀ sigma R y e) =
            ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e ∧
        lam • (1 : PDE.Mat d) ≤
          spectralTraceMatrix (cutoffMatrix alpha C₀ sigma R y e)
            (ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e) cminus ∧
        spectralTraceMatrix (cutoffMatrix alpha C₀ sigma R y e)
          (ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e) cminus ≤
            Lam • (1 : PDE.Mat d) := by
  obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
    exists_cutoff_sign_parameters d hd alpha ha ha1
  have hR : 0 < R := lt_trans (by norm_num) hR2
  let K := cutoffParameterSet d R
  let M := fun q : PDE.Vec d × PDE.Vec d => cutoffMatrix alpha C₀ sigma R q.1 q.2
  let b := fun q : PDE.Vec d × PDE.Vec d =>
    ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) q.1 q.2
  have hM := continuous_cutoffMatrix (d := d) alpha C₀ sigma R hsigma hR
  have hherm : ∀ q, (M q).IsHermitian :=
    fun q => cutoffMatrix_isHermitian alpha C₀ sigma R hsigma hR q.1 q.2
  have hb := continuous_cutoffTransport (d := d) alpha C₀ sigma R hsigma hR
  have hmp : Continuous (fun q => positiveSpectralMass (M q)) :=
    continuous_positiveSpectralMass M hM hherm
  have hmn : Continuous (fun q => negativeSpectralMass (M q)) :=
    continuous_negativeSpectralMass M hM hherm
  have hmp_pos : ∀ q ∈ K, 0 < positiveSpectralMass (M q) := by
    intro q hq
    obtain ⟨w, hw⟩ := (hsign q.1 q.2 hq.1).1
    apply positiveSpectralMass_pos_of_direction (M q) (hherm q) w
    rwa [cutoffMatrix_quadratic alpha C₀ sigma R hsigma hR]
  have hmn0 : ∀ q ∈ K, 0 ≤ negativeSpectralMass (M q) :=
    fun q _ => positiveSpectralMass_nonneg (-(M q)) (hherm q).neg
  have hzeropos : ∀ q ∈ K, negativeSpectralMass (M q) = 0 → 0 < b q := by
    intro q hq hmzero
    rcases (hsign q.1 q.2 hq.1).2 with ⟨w, hw⟩ | hbpos
    · have hneg : 0 < negativeSpectralMass (M q) := by
        apply negativeSpectralMass_pos_of_direction (M q) (hherm q) w
        rwa [cutoffMatrix_quadratic alpha C₀ sigma R hsigma hR]
      rw [hmzero] at hneg
      exact hneg.false.elim
    · exact lt_of_lt_of_le zero_lt_one hbpos
  obtain ⟨cminus, hcminus, hnumpos⟩ := exists_spectral_weight_on_compact K
    (isCompact_cutoffParameterSet d R) b (fun q => negativeSpectralMass (M q))
    hb.continuousOn hmn.continuousOn hmn0 hzeropos
  let w := fun q => (b q + cminus * negativeSpectralMass (M q)) / positiveSpectralMass (M q)
  have hwcont : ContinuousOn w K :=
    (hb.continuousOn.add (continuousOn_const.mul hmn.continuousOn)).div hmp.continuousOn
      (fun q hq => (hmp_pos q hq).ne')
  obtain ⟨lower, upper, hlo, hlou, hweights⟩ := exists_positive_bounds_on_compact K
    (isCompact_cutoffParameterSet d R) w hwcont
    (fun q hq => div_pos (hnumpos q hq) (hmp_pos q hq))
  let lam := min 1 (min lower cminus)
  let Lam := max 1 (max upper cminus)
  have hlam : 0 < lam := lt_min zero_lt_one
    (lt_min hlo (lt_of_lt_of_le zero_lt_one hcminus))
  have hlamLam : lam ≤ Lam := (min_le_left _ _).trans (le_max_left _ _)
  refine ⟨C₀, sigma, R, cminus, lam, Lam, hC₀, hsigma, hR2, hcminus, hlam, hlamLam, ?_, ?_⟩
  · exact fun i k => measurable_spectralTraceMatrix M hM hherm b hb.measurable cminus i k
  · intro y e hye
    have hbounds := spectralTraceMatrix_uniform_bounds (M (y, e)) (hherm (y, e))
      (b (y, e)) cminus lower upper (hweights (y, e) hye).1 (hweights (y, e) hye).2
    exact ⟨spectral_trace_solver _ (hherm (y, e)) _ _ (hmp_pos (y, e) hye).ne', hbounds⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
