module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly.Density
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly.Evolution
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly.GreenPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly.Reflection
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly

/-!
# The smooth full-coefficient estimate from the Green density

For a smooth symmetric coefficient
`A(t,x,v)` with everywhere Loewner bounds, the localized Aleksandrov estimate with constant
`C(d,λ,p)` fixed before `Λ` and all data follows from the Green density estimate (the
premise `hgreen`, the conclusion of the Green density theorem at the exponent `q = p/(p-1)`)
and the abstract ABP estimate, after reflection `Ã(s,X,v) = A(-s,-X,v)`.

The theorem is conditional (distinct name `..._of_greenDensity`); `hgreen` is discharged by the
Green density theorem, and `hqstar`, `q ≤ q_*`, is its exponent range (equivalently
`p ≥ p_*`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- The smooth full-coefficient localized estimate from the Green density.  `hgreen` is the
conclusion of the Green density theorem at the exponent
`q = p/(p-1)`; its constant is fixed before `Λ`. -/
theorem smooth_estimate_fullCoefficient_of_greenDensity
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p q : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 < p) (hqp : q = p / (p - 1))
    (hqstar : q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2))
    (hgreen : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Lam : ℝ), lam ≤ Lam →
        q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) →
      ∀ (B : FullKineticCoefficient d),
        IsSmoothFullKineticCoefficient B →
        IsSymmetricFullKineticCoefficient B →
        HasEverywhereLoewnerBounds lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ B (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (p : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
        (T : ℝ), 0 < T →
      ∀ (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d)),
        IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ →
        ∃ G : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ≥0∞,
          Measurable G ∧
          Γ = ((elapsedVolume (ENNReal.ofReal T)).prod
            (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
          eLpNorm G (ENNReal.ofReal q) ((elapsedVolume (ENNReal.ofReal T)).prod
            (volume : Measure (EvolutionAmbientState d))) ≤
            ENNReal.ofReal (C * T ^ ((1 - 2 * (d : ℝ) * (q - 1)) / q))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : FullKineticCoefficient d),
        IsSmoothFullKineticCoefficient A →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ P : KineticPoint d, lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P ∧
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)), backwardOperator A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  subst hqp
  obtain ⟨C, hC, hgreen⟩ := hgreen
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p - 1 := by linarith
  -- `q ≤ q_*` forces `p > 2d + 1`
  have hpd : 2 * (d : ℝ) + 1 < p := by
    have h1 : p / (p - 1) - 1 = 1 / (p - 1) := by field_simp; ring
    have h2 : 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) ≤ 3 / (128 * (d : ℝ) ^ 2) := by
      have hd2 : 0 < (d : ℝ) ^ 2 := pow_pos (by linarith) 2
      have hL2 : 0 < Lam ^ 2 := pow_pos (by linarith) 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : lam ^ 2 ≤ Lam ^ 2 := pow_le_pow_left₀ hlam.le hLam 2
      nlinarith [mul_nonneg hd2.le (sub_nonneg.2 this)]
    have h3 : 1 / (p - 1) ≤ 3 / (128 * (d : ℝ) ^ 2) := by linarith
    rw [div_le_div_iff₀ hp0 (by positivity)] at h3
    nlinarith
  have hq : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ hp0]
    linarith
  have hqp' : (p / (p - 1)) / (p / (p - 1) - 1) = p := by
    apply (div_eq_iff (by linarith : p / (p - 1) - 1 ≠ 0)).mpr
    field_simp [sub_ne_zero.mpr hp.ne']
    ring
  refine ⟨C + 1, by linarith, ?_⟩
  intro P₀ R hR A hAs hsym hbd f u _hfm hcont hreg hsub hLp P hP
  let Ã := reflectedCoefficient A
  have hÃs : IsSmoothFullKineticCoefficient Ã := isSmooth_reflectedCoefficient hAs
  have hBs : IsSmoothFullKineticCoefficient (swapCoefficient Ã) :=
    isSmooth_sectionTwoCoefficient hAs
  have hBsym : IsSymmetricFullKineticCoefficient (swapCoefficient Ã) :=
    isSymmetric_sectionTwoCoefficient hsym
  have hBell : HasEverywhereLoewnerBounds lam Lam (swapCoefficient Ã) :=
    hasEverywhereLoewnerBounds_sectionTwoCoefficient hbd
  obtain ⟨S, K, hreal⟩ := exists_realization hd hlam hLam hBs hBsym hBell
  have hH : HormanderHypoellipticityStatement := hormanderHypoellipticityStatement_holds
  let Z₀ := kineticReflection P₀
  let Q := forwardCylinder Z₀ R hR
  let Γ := cylinderGreenMeasure K Z₀ R hR
  let U := u ∘ kineticReflection
  let g₀ := (fun P => max (f P) 0) ∘ kineticReflection
  let α := 2 - (4 * (d : ℝ) + 2) / p
  have hRp : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have hKpos : 0 < (C + 1) * R ^ α := mul_pos (by linarith) hRp
  have hAc : ContinuousOn (fun P : KineticPoint d => Ã P.time P.position P.velocity) Q := by
    have hc : Continuous (fun q : ℝ × (PDE.Vec d × PDE.Vec d) => Ã q.1 q.2.1 q.2.2) :=
      continuous_pi fun i => continuous_pi fun j => (hÃs i j).continuous
    exact (hc.comp (continuous_time.prodMk
      (continuous_position.prodMk continuous_velocity))).continuousOn
  have hApos : ∀ P ∈ Q, (Ã P.time P.position P.velocity).PosSemidef := fun P _ =>
    (posDef_of_loewner_lower hlam (hbd ⟨-P.time, -P.position, P.velocity⟩).1).posSemidef
  have hpotential : ∀ g : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd d).symm z)) →
      HasCompactSupport g → tsupport g ⊆ Q → (∀ P, 0 ≤ g P) →
      IsKineticC112On (fun P => ∫ z, g z ∂Γ P) Q ∧
      (∀ P ∈ Q, 0 ≤ ∫ z, g z ∂Γ P) ∧
      (∀ P ∈ Q, forwardKineticOperator Ã (fun P => ∫ z, g z ∂Γ P) P = -g P) :=
    fun g hgs hgc hgQ hg0 =>
      green_potentials_full hH hlam Ã hBs hBsym hBell S K hreal Z₀ R hR g hgs hgc hgQ hg0
  have hdensity := cylinder_density_of_greenDensity p C hpd hC K
    (fun σ₀ pt T hT Γ' hΓ' => hgreen Lam hLam hqstar _ hBs hBsym hBell S K hreal σ₀ pt T hT
      Γ' hΓ') Z₀ R hR
  have hdensity' : ∀ P ∈ Q, ∃ G : KineticPoint d → ℝ, Measurable G ∧
      (∀ z, 0 ≤ G z) ∧ Γ P = (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal (p / (p - 1))) (volume.restrict Q)).toReal ≤
        (C + 1) * R ^ α ∧
      MemLp G (ENNReal.ofReal (p / (p - 1))) (volume.restrict Q) := hdensity
  have hmp := measurePreserving_reflection_forward P₀ R hR
  have hUc : ContinuousOn U (closure Q) := by
    have hc := hcont.comp (continuous_kineticReflection d).continuousOn
      (fun x hx => hx : MapsTo kineticReflection
        (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _)
    simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using hc
  have hUr : IsKineticC112On U Q := by
    simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
      isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
  have hgLp : MemLp g₀ (ENNReal.ofReal ((p / (p - 1)) / (p / (p - 1) - 1)))
      (volume.restrict Q) := by
    rw [hqp']
    exact hLp.comp_measurePreserving hmp
  have hUs : ∀ᵐ P ∂volume.restrict Q, -g₀ P ≤ forwardKineticOperator Ã U P := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
    rw [reflectedOperator_reflection]
    exact neg_le_neg (hP.trans (le_max_left _ _))
  have hbound := kinetic_abp_abstract_of_continuous Z₀ R hR Ã hAc hApos (p / (p - 1)) hq
    ((C + 1) * R ^ α) hKpos Γ hpotential hdensity' U g₀ hUc hUr
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
  rw [hqp', hnorm, boundarySup_reflection P₀ R hR u] at hresult
  simpa only [U, Function.comp_apply, kineticReflection_involutive P] using hresult

end HypoellipticAleksandrov.KineticAleksandrov
