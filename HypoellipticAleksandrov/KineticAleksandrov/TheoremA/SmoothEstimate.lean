module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateEllipticity
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource

/-! # Uniform smooth time--velocity Aleksandrov estimate from the Green density bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Set MeasureTheory SectionTwo Green Parabolic
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.Elementwise
variable {d : ℕ}

/-- The localized smooth estimate, with its constant fixed before all coefficient and PDE data. -/
theorem smooth_estimate_of_slabFourierBounds (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hH : HormanderHypoellipticityStatement)
    (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ)
    (hevolution : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : CoefficientField d),
      IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (u f : KineticPoint d → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R),
      u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
        C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hgreen⟩ := green_density_bound_of_slabFourierBounds hd lam Lam p
    hlam hLam hp hbounds
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 < p := by linarith
  let q := p / (p - 1)
  have hq : 1 < q := by
    dsimp only [q]
    rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hqp : q / (q - 1) = p := by
    apply (div_eq_iff (by linarith : q - 1 ≠ 0)).mpr
    dsimp only [q]
    field_simp [sub_ne_zero.mpr hp1.ne']
    ring
  refine ⟨C + 1, by positivity, ?_⟩
  intro A hAs hsym hloAE hhiAE P₀ R hR u f hcont hreg hf hLp hsub P hP
  obtain ⟨hlo, hhi⟩ := ellipticity_of_smooth_ae hAs hloAE hhiAE
  let B := kineticReflectedCoefficient A
  have hBs := isSmoothCoefficient_kineticReflectedCoefficient A hAs
  have hBsym := isSymmetricCoefficient_kineticReflectedCoefficient A hsym
  have hBlo : HasLowerEllipticity lam B := fun t v => hlo (-t) v
  have hBhi : HasUpperEllipticity Lam B := fun t v => hhi (-t) v
  obtain ⟨S, K, hreal⟩ := hevolution B
    ⟨hlam, hLam, isSmoothFullKineticCoefficient_zIndependent hBs, hBsym, hBlo, hBhi⟩
  let Z₀ := kineticReflection P₀
  let Q := forwardCylinder Z₀ R hR
  let Γ := cylinderGreenMeasure K Z₀ R hR
  let U := u ∘ kineticReflection
  let g₀ := (fun P => max (f P) 0) ∘ kineticReflection
  let α := 2 - (4 * (d : ℝ) + 2) / p
  have hRp : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have hKpos : 0 < (C + 1) * R ^ α := mul_pos (by positivity) hRp
  have hAc : ContinuousOn (fun P : KineticPoint d =>
      (ofTimeVelocityCoefficient B) P.time P.position P.velocity) Q :=
    (hBs.continuous.comp (continuous_time.prodMk continuous_velocity)).continuousOn
  have hApos : ∀ P ∈ Q,
      ((ofTimeVelocityCoefficient B) P.time P.position P.velocity).PosSemidef :=
    fun P _ => (posDef_of_loewner_lower hlam (hBlo P.time P.velocity)).posSemidef
  have hpotential := green_potentials hH hlam hLam B hBs hBsym hBlo hBhi S K hreal Z₀ R hR
  have hdensity : ∀ P ∈ Q, ∃ G : KineticPoint d → ℝ, Measurable G ∧
      (∀ z, 0 ≤ G z) ∧ Γ P = (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal q) (volume.restrict Q)).toReal ≤ (C + 1) * R ^ α ∧
      MemLp G (ENNReal.ofReal q) (volume.restrict Q) := by
    intro P hP
    have ht := ((mem_forwardCylinder_iff Z₀ P R hR).1 hP).2.1
    let GP := greenMeasure K P.time (ENNReal.ofReal (remainingTime Z₀ P R))
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
    have hGP := greenMeasure_spec K P.time _
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
    obtain ⟨G, hG, hden, hnorm, hscale⟩ := hgreen P₀ R hR A hAs hsym hlo hhi S K hreal P hP
      GP hGP
    have hnorm' : eLpNorm G (ENNReal.ofReal q) (volume.restrict Q) ≤
        ENNReal.ofReal (C * R ^ α) := hnorm.trans (ENNReal.ofReal_le_ofReal hscale)
    have hden' : Γ P = (volume.restrict Q).withDensity G := by
      dsimp only [Γ, cylinderGreenMeasure]
      rw [dite_eq_left ht]
      convert hden using 1
      rfl
    obtain ⟨F, hFm, hFn, hFd, hFN, hFLp⟩ := real_density_of_eLpNorm_bound
      (volume.restrict Q) (Γ P) G hG hden' q (C * R ^ α) (lt_trans zero_lt_one hq)
      (mul_nonneg hC hRp.le) hnorm'
    refine ⟨F, hFm, hFn, hFd, hFN.trans ?_, hFLp⟩
    exact mul_le_mul_of_nonneg_right (by linarith) hRp.le
  have hmp := measurePreserving_reflection_forward P₀ R hR
  have hUc : ContinuousOn U (closure Q) := by
    have hc := hcont.comp (continuous_kineticReflection d).continuousOn
      (fun x hx => hx : MapsTo kineticReflection
        (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _)
    simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using hc
  have hUr : IsKineticC112On U Q := by
    simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
      isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
  have hgLp : MemLp g₀ (ENNReal.ofReal (q / (q - 1))) (volume.restrict Q) := by
    rw [hqp]
    exact hLp.comp_measurePreserving hmp
  have hUs : ∀ᵐ P ∂volume.restrict Q,
      -g₀ P ≤ forwardKineticOperator (ofTimeVelocityCoefficient B) U P := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
    rw [reflectedKineticOperator_reflection]
    exact neg_le_neg (hP.trans (le_max_left _ _))
  have hbound := kinetic_abp_abstract_of_continuous Z₀ R hR (ofTimeVelocityCoefficient B)
    hAc hApos q hq ((C + 1) * R ^ α) hKpos Γ hpotential hdensity U g₀ hUc hUr
    (fun P _ => le_max_right _ _) hgLp hUs
  have hPr : kineticReflection P ∈ closure Q := by
    rw [← preimage_closure_backwardCylinder_reflection P₀ R hR]
    change kineticReflection (kineticReflection P) ∈ closure (backwardCylinder P₀ R)
    rw [kineticReflection_involutive P]
    exact hP
  have hresult := hbound (kineticReflection P) hPr
  have hnorm : eLpNorm ({P | 0 < U P}.indicator g₀) (ENNReal.ofReal p)
      (volume.restrict Q) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) := by
    have hset : MeasurableSet (backwardCylinder P₀ R ∩ {P | 0 < u P}) :=
      (hreg.continuousOn.isOpen_inter_preimage (isOpen_backwardCylinder P₀ R hR)
        isOpen_Ioi).measurableSet
    have hEq : (backwardCylinder P₀ R ∩ {P | 0 < u P}).indicator
        (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
        {P | 0 < u P}.indicator (fun P => max (f P) 0) := by
      filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet]
        with P hP
      simp only [indicator, mem_inter_iff, hP, true_and]
    have hL := (hLp.indicator hset).ae_eq hEq
    have hfun : {P | 0 < U P}.indicator g₀ =
        ({P | 0 < u P}.indicator (fun P => max (f P) 0)) ∘ kineticReflection := rfl
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hL.aestronglyMeasurable hmp
  rw [hqp, hnorm, boundarySup_reflection P₀ R hR u] at hresult
  simpa only [U, Function.comp_apply, kineticReflection_involutive P] using hresult

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
