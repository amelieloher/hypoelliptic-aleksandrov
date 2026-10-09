module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsHomogeneous
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusionConsumers
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Borel homogeneous correctors on compact interior collars

The approximating coefficients, evolutions, sources and solutions are constructed
internally. Their smoothness and convergence follow from the weak and Green calculus.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA Filter
open scoped Topology ENNReal Matrix.Norms.Elementwise

/-- Compact-interior Borel solutions have actual smooth homogeneous correctors. -/
theorem exists_borel_homogeneous_correctors
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsBorelCoefficient A)
    (hs : IsSymmetricCoefficient A) (hlo : HasLowerEllipticityAE lam A)
    (hhi : HasUpperEllipticityAE Lam A)
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (U : KineticPoint d → ℝ) (hu : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (he : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
      forwardKineticOperator (ofTimeVelocityCoefficient A) U P = 0)
    (K₀ : Set (KineticPoint d)) (hK : IsCompact K₀)
    (hKU : K₀ ⊆ forwardCylinder Z₀ R hR) :
    ∃ (A_j : ℕ → CoefficientField d) (U_j : ℕ → KineticPoint d → ℝ)
      (O : Set (KineticPoint d)),
      IsOpen O ∧ K₀ ⊆ O ∧ closure O ⊆ forwardCylinder Z₀ R hR ∧
      (∀ j, IsSectionTwoCoefficient lam Lam (A_j j)) ∧
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
        (U_j j ∘ (KineticPoint.equivProd d).symm) ((KineticPoint.equivProd d) '' O)) ∧
      (∀ j, ∀ P ∈ O,
        forwardKineticOperator (ofTimeVelocityCoefficient (A_j j)) (U_j j) P = 0) ∧
      TendstoUniformlyOn U_j U atTop K₀ := by
  let D := forwardCylinder Z₀ R hR
  have hD : IsOpen D := isOpen_forwardCylinder Z₀ R hR
  obtain ⟨O, χ, hO, hKO, hOD, _, hχs, hχc, hχD, hχb, hχone⟩ :=
    exists_borelCorrector_cutoff hD hK hKU
  have hχ : Continuous χ := boundary_probe_continuous χ hχs
  obtain ⟨B, hB, hconv⟩ := borel_coefficient_approximation lam Lam hlam hLam A hA hs hlo hhi
  have hCoeff j : IsSectionTwoCoefficient lam Lam (B j) :=
    ⟨hlam, hLam, isSmoothFullKineticCoefficient_zIndependent (hB j).1,
      (hB j).2.1, (hB j).2.2.1, (hB j).2.2.2⟩
  have hEv := exists_terminalEvolution_of_classical hLE hH
  have hwhole := SectionTwo.taAssemblyEvolution_of_conclusion hEv d hd lam Lam hlam hLam
  choose S K hreal _ _ _ using (fun j => hwhole (B j) (hCoeff j))
  let T := Z₀.time + R ^ 2
  let J := fun j => borelCorrectedFunction (K j) T χ (B j) U
  have hDt : ∀ P ∈ D, P.time < T := fun P hP => hP.2.1
  have hOD' : O ⊆ D := subset_closure.trans hOD
  have hJ j := borelCorrectedFunction_smooth_homogeneous hH (B j) (hCoeff j) (hB j).1
    (S j) (K j) (hreal j) T D O hD hO hOD' hDt U hu χ hχ hχc hχD
    (fun P hP => hχone P (subset_closure hP))
  let p := 2 * (d : ℝ) + 2
  have hp : 2 * (d : ℝ) + 1 < p := by dsimp [p]; linarith
  have hp0 : 0 < p := by dsimp [p]; positivity
  obtain ⟨hmem, hnorm⟩ := borelCorrectorSource_norm_tendsto hlam hLam A hA hlo hhi
    B hB hconv hD U hu he χ hχ hχc hχD hχb hp0
  obtain ⟨C, _, hbound⟩ := borelCorrectorPotential_uniform_bound hH hLE hd lam Lam p
    hlam hLam hp
  let e := fun j => C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
    (eLpNorm (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) volume).toReal
  have he0 : Tendsto e atTop (𝓝 0) := by
    simpa only [mul_zero] using hnorm.const_mul (C * R ^ (2 - (4 * (d : ℝ) + 2) / p))
  refine ⟨B, J, O, hO, hKO, hOD, hCoeff, fun j => (hJ j).1, fun j => (hJ j).2, ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp he0).2 ε hε] with j hj
  intro P hP
  have hFc := borelCorrectorSource_continuous_compact hD χ hχ hχc hχD (B j) (hB j).1 U hu
  have hFs : tsupport (borelCorrectorSource χ (B j) U) ⊆ D :=
    tsupport_mul_subset_left.trans hχD
  have hb := hbound (B j) (hCoeff j) (S j) (K j) (hreal j) Z₀ R hR
    (borelCorrectorSource χ (B j) U) hFc.1 hFc.2 hFs (hmem j) P (hKU hP)
  have hd : dist (U P) (J j P) =
      |borelCorrectorPotential (K j) T (borelCorrectorSource χ (B j) U) P| := by
    rw [Real.dist_eq]
    dsimp only [J, borelCorrectedFunction]
    rw [show U P - (U P + borelCorrectorPotential (K j) T
      (borelCorrectorSource χ (B j) U) P) =
      -borelCorrectorPotential (K j) T (borelCorrectorSource χ (B j) U) P by ring, abs_neg]
  rw [hd]
  exact hb.trans_lt hj

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
