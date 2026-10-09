module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityPotential
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTests
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsInterpolation
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole

/-!
# Deriving unit-time occupation density from the exact whole-space source estimate

The conditional premise is the complete whole-space estimate, including its
ball comparison clause. Absolute continuity and all density norm bounds are derived here.
The constant precedes the coefficient field, realization, kernel, and initial measure.
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal

variable {d : ℕ}

/-- The exact whole-space bound implies the occupation-duality conclusion.
This derivation is conditional on the stated bound. -/
theorem occupation_duality_of_whole_space_bound
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (_hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (hWhole :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (F : TimeVelocity d → ℝ) (_hF0 : ∀ q, 0 ≤ F q)
        (_hFs : ContDiff ℝ (⊤ : ℕ∞) F) (_hFc : HasCompactSupport F)
        (_hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ),
        let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
        let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
        (∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ (vStar : PDE.Vec d) (R : ℝ),
          0 < R → R ^ 2 = max 1 (4 * d * Lam) →
          ∃ V : TimeVelocity d → ℝ,
            IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
              (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
              (fun _ => 0) (fun _ => 0) V ∧
            (∀ q ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
              W q ≤ V q + H *
                ((∑ i, (q.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - q.1)) / R ^ 2) ∧
            (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2) ∧
        H ≤ C * parabolicLpNorm d F
    ) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal := by
  obtain ⟨C₀, hC₀, hWhole⟩ := hWhole
  refine ⟨fun _ => 2 * (C₀ + 1), fun _ _ _ => by positivity, ?_⟩
  intro B hB S K hreal hP ρ _
  let M := (ρ univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have htest : ∀ F : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ → (∀ q, 0 ≤ F q) →
      (∫ q, F q ∂unitOccupationMeasure K ρ) ≤ (C₀ * M) *
        (eLpNorm F (ENNReal.ofReal
          ((((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1)))
          (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal := by
    intro F hFs hFc hFsupp hF0
    let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
    have hwhole := (hWhole B hB S K hreal hP F hF0 hFs hFc hFsupp).2
    have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
    have hb (v : PDE.Vec d) : W (0, v) ≤ C₀ * parabolicLpNorm d F :=
      (le_csSup hpot.2.1 ⟨(0, v), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩).trans hwhole
    have hn (v : PDE.Vec d) : ‖W (0, v)‖ ≤ C₀ * parabolicLpNorm d F := by
      rw [Real.norm_of_nonneg (hpot.1 (0, v))]
      exact hb v
    rw [integral_unitOccupationMeasure_eq_potential K ρ F hFs hFc]
    have hi := norm_integral_le_of_norm_le_const (μ := ρ)
      (Filter.Eventually.of_forall hn)
    have hle : (∫ v, W (0, v) ∂ρ) ≤ (C₀ * parabolicLpNorm d F) * M :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, measureReal_def] using hi)
    rw [parabolicLpNorm_eq_slab hd F hFsupp] at hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hle
  obtain ⟨_hac, g, hgm, hg0, hgi, hgr, hgrn, hgmass, hgpair⟩ :=
    exists_density_of_smooth_tests volume (unitOccupationMeasure K ρ)
      (isOpen_Ioo.prod isOpen_univ) (unitOccupationMeasure_compl_slab K ρ)
      (occupation_endpoint_gt_one hd) (mul_nonneg hC₀ hM) htest
  have h1 : MemLp g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) :=
    memLp_one_iff_integrable.2 hgi
  have hnormMass : (eLpNorm g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal =
      (unitOccupationMeasure K ρ univ).toReal := by
    have he := PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
      (p := 1) zero_lt_one (by simpa using h1)
    simp only [ENNReal.ofReal_one, Real.rpow_one] at he
    have heq : (fun q => ‖g q‖) = g := by
      funext q
      exact Real.norm_of_nonneg (hg0 q)
    rw [heq, hgmass] at he
    exact he
  have h1n : (eLpNorm g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤ M := by
    rw [hnormMass]
    exact ENNReal.toReal_mono (measure_ne_top ρ univ) (unitOccupationMeasure_mass_le K ρ)
  refine ⟨g, ⟨hgm, hg0, ?_⟩, ?_⟩
  · intro φ
    obtain ⟨A, _hA, hφA⟩ := φ.exists_bound
    exact (hgpair φ).trans (integral_unitOccupationMeasure K ρ φ φ.measurable ⟨A, hφA⟩)
  · intro γ hγ hγr
    have hA : 0 ≤ (C₀ + 1) * M := mul_nonneg (by positivity) hM
    have h1A : (eLpNorm g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤
        (C₀ + 1) * M := h1n.trans (by nlinarith)
    have hrA : (eLpNorm g (ENNReal.ofReal (((d : ℝ) + 1) / d))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤ (C₀ + 1) * M :=
      hgrn.trans (by nlinarith)
    obtain ⟨hgγ, hgγn⟩ := memLp_intermediate_of_bounds (occupation_endpoint_gt_one hd)
      hγ hγr hA h1 hgr h1A hrA
    refine ⟨hgγ, ?_⟩
    change (eLpNorm g (ENNReal.ofReal γ)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤ (2 * (C₀ + 1)) * M
    simpa only [mul_assoc] using hgγn

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
