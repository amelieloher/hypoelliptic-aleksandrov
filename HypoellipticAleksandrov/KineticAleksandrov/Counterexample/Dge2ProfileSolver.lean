module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileNormalize

/-! # Global ellipticity and exact trace equation from compact gauge-shell weights -/

@[expose] public section

noncomputable section

open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The compact gauge shell supplies one global canonical spectral weight and ellipticity pair. -/
theorem exists_spectral_weights_of_homogeneous_profile {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hpos : ∀ q, q ≠ 0 → 0 < positiveSpectralMass (dvv H q))
    (hzero : ∀ q, q ≠ 0 → negativeSpectralMass (dvv H q) = 0 →
      0 < PDE.vecDot q.2 (dx H q)) :
    ∃ cminus lam Lam : ℝ, 1 ≤ cminus ∧ 0 < lam ∧ lam ≤ 1 ∧ 1 ≤ Lam ∧
      (∀ q, lam • (1 : PDE.Mat d) ≤ homogeneousSpectralMatrix H cminus q ∧
        homogeneousSpectralMatrix H cminus q ≤ Lam • (1 : PDE.Mat d)) ∧
      (∀ q, q ≠ 0 → matrixContraction (homogeneousSpectralMatrix H cminus q) (dvv H q) =
        PDE.vecDot q.2 (dx H q)) := by
  let K : Set (XV d) := {q | rho q = 1}
  let M := dvv H
  let b := fun q : XV d => PDE.vecDot q.2 (dx H q)
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hz
    have hh : rho q = 1 := hq
    simp [hz] at hh
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hherm : ∀ q, q ≠ 0 → (M q).IsHermitian :=
    fun q hq => dvv_isHermitian H q (hsmooth.contDiffAt (hopen.mem_nhds hq))
  have hMc : ContinuousOn M K := (continuousOn_dvv_off_origin H hsmooth).mono
    (fun q hq => hKnz q hq)
  have hbc : ContinuousOn b K := (continuousOn_transport_off_origin H hsmooth).mono
    (fun q hq => hKnz q hq)
  have hmp : ContinuousOn (fun q => positiveSpectralMass (M q)) K :=
    continuousOn_positiveSpectralMass M K hMc (fun q hq => hherm q (hKnz q hq))
  have hmn : ContinuousOn (fun q => negativeSpectralMass (M q)) K :=
    continuousOn_positiveSpectralMass (fun q => -M q) K hMc.neg
      (fun q hq => (hherm q (hKnz q hq)).neg)
  have hm0 : ∀ q ∈ K, 0 ≤ negativeSpectralMass (M q) :=
    fun q hq => positiveSpectralMass_nonneg (-M q) (hherm q (hKnz q hq)).neg
  obtain ⟨cminus, hcminus, hnum⟩ := exists_spectral_weight_on_compact K
    (isCompact_unitGaugeShell d) b (fun q => negativeSpectralMass (M q)) hbc hmn hm0
    (fun q hq => hzero q (hKnz q hq))
  let w := fun q => (b q + cminus * negativeSpectralMass (M q)) / positiveSpectralMass (M q)
  have hwc : ContinuousOn w K :=
    (hbc.add (continuousOn_const.mul hmn)).div hmp
      (fun q hq => (hpos q (hKnz q hq)).ne')
  obtain ⟨lower, upper, hlo, _, hweights⟩ := exists_positive_bounds_on_compact K
    (isCompact_unitGaugeShell d) w hwc
    (fun q hq => div_pos (hnum q hq) (hpos q (hKnz q hq)))
  let lam := min 1 (min lower cminus)
  let Lam := max 1 (max upper cminus)
  have hlam : 0 < lam := lt_min zero_lt_one
    (lt_min hlo (lt_of_lt_of_le zero_lt_one hcminus))
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hLam1 : 1 ≤ Lam := le_max_left _ _
  have hbound : ∀ q ∈ K, lam • (1 : PDE.Mat d) ≤ spectralTraceMatrix (M q) (b q) cminus ∧
      spectralTraceMatrix (M q) (b q) cminus ≤ Lam • (1 : PDE.Mat d) := by
    intro q hq
    exact spectralTraceMatrix_uniform_bounds (M q) (hherm q (hKnz q hq)) (b q) cminus
      lower upper (hweights q hq).1 (hweights q hq).2
  refine ⟨cminus, lam, Lam, hcminus, hlam, hlam1, hLam1, ?_, ?_⟩
  · intro q
    by_cases hq : q = 0
    · rw [homogeneousSpectralMatrix, ite_eq_left hq]
      simpa only [one_smul] using
        And.intro (scalar_identity_le (d := d) lam 1 hlam1)
          (scalar_identity_le (d := d) 1 Lam hLam1)
    · have hp : normalizeGauge q ∈ K := rho_normalizeGauge q hq
      rw [homogeneousSpectralMatrix, ite_eq_right hq, normalizedProfileMatrix,
        ite_eq_right hq, normalizedProfileTransport, ite_eq_right hq]
      exact hbound (normalizeGauge q) hp
  · intro q hq
    have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
    let p := normalizeGauge q
    have hpnz : p ≠ 0 := normalizeGauge_ne_zero q hq
    have hMscale := homogeneous_dvv alpha H hsmooth hhom (rho q) hr p hpnz
    have hbscale := homogeneous_transport alpha H hsmooth hhom (rho q) hr p hpnz
    rw [dilate_normalizeGauge q hq] at hMscale hbscale
    rw [homogeneousSpectralMatrix, ite_eq_right hq, normalizedProfileMatrix,
      ite_eq_right hq, normalizedProfileTransport, ite_eq_right hq, hMscale,
      matrixContraction_smul_right,
      spectral_trace_solver _ (hherm p hpnz) _ _ (hpos p hpnz).ne']
    exact hbscale.symm

/-- The geometric profile has a global measurable elliptic matrix solving its pointwise PDE. -/
theorem exists_geometricProfile_elliptic_solver (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R lam Lam : ℝ, ∃ A : XV d → PDE.Mat d,
      0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧ 0 < lam ∧ lam ≤ Lam ∧
      (∀ i k, Measurable (fun q => A q i k)) ∧
      (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧ A q ≤ Lam • (1 : PDE.Mat d)) ∧
      (∀ q, q ≠ 0 → matrixContraction (A q) (dvv (geometricProfile alpha C₀ sigma R) q) =
        PDE.vecDot q.2 (dx (geometricProfile alpha C₀ sigma R) q)) := by
  obtain ⟨C₀, sigma, R, hC₀, hsigma, hR2, hsign⟩ :=
    exists_geometricProfile_spectral_signs d hd alpha ha ha1
  have hR : 0 < R := lt_trans (by norm_num) hR2
  let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
  have hH := geometricProfile_smooth_off_origin (d := d) alpha C₀ sigma R hsigma hR
  have hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q :=
    fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
  obtain ⟨cminus, lam, Lam, _, hlam, hlam1, hLam1, hbounds, hsolve⟩ :=
    exists_spectral_weights_of_homogeneous_profile alpha H hH hhom
      (fun q hq => (hsign q hq).2.1) (fun q hq => (hsign q hq).2.2)
  refine ⟨C₀, sigma, R, lam, Lam, homogeneousSpectralMatrix H cminus,
    hC₀, hsigma, hR2, hlam, hlam1.trans hLam1, ?_, hbounds, hsolve⟩
  exact fun i k => measurable_homogeneousSpectralMatrix H hH cminus i k

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
