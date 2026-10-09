module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Section 2 realization and whole-space API

Literal realization predicates, their consequences, and case-W geometry.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

open MeasureTheory Set
open HypoellipticAleksandrov.Parabolic
open scoped ENNReal MatrixOrder ProbabilityTheory

/-- Case W is the whole diffused-coordinate space. -/
def wholeSpace (d : ℕ) : Set (PDE.Vec d) := Set.univ

/-- Case W has identity transport. -/
def identityDrift (d : ℕ) : PDE.Vec d → PDE.Vec d := id

/-- The literal Section 2 smooth, symmetric, elliptic coefficient premises. -/
def IsSectionTwoCoefficient {d : ℕ} (lam Lam : ℝ) (B : CoefficientField d) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    IsSmoothFullKineticCoefficient (zIndependentCoefficient B) ∧
    IsSymmetricCoefficient B ∧ HasLowerEllipticity lam B ∧ HasUpperEllipticity Lam B

/-- The two source transport bounds, using explicit Euclidean geometry. -/
def HasTransportBounds {d : ℕ} (m L_b : ℝ) (b : PDE.Vec d → PDE.Vec d) : Prop :=
  HasEuclideanLipschitzDrift L_b b ∧ HasUnitDirectionDriftCoercivity m b

/-- The literal transported operator, with KineticPoint read as (sigma,v,z). -/
abbrev lop {d : ℕ} (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (u : KineticPoint d → ℝ) (q : KineticPoint d) : ℝ :=
  transportedForwardOperatorOfTimeDiffusedCoefficient B b u q

/-- A supplied family's exact classical-data and integral-representation clauses.

These are source characterizations, not additional hypotheses on the source theorem.
-/
def RealizesTerminalEvolution {d : ℕ} (Ω : Set (PDE.Vec d))
    (γ : ℝ → PDE.Vec d) (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ) : Prop :=
  (∀ τ (F : BoundedBorel (EvolutionAmbientState d)),
    IsSmoothCompactTerminalDatum Ω γ τ F →
    ∃ u : KineticPoint d → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ σ (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ),
        u ⟨σ, p.1.1, p.1.2⟩ = S σ τ hστ (terminalStateDatum F) p) ∧
      (∀ v, IsClassicalTerminalSolution Ω γ B b τ F v →
        EqOn v u (evolutionPastClosedCylinder Ω γ τ))) ∧
  (∀ σ τ (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
      (f : BoundedBorel (EvolutionState Ω γ τ)),
    S σ τ hστ f p = ∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p) ∧
  K.HasEndpoint hΩ ∧ K.HasComposition hΩ

/-- Affine coordinates (sigma,v,z), with the source transport shift. -/
def scaledPoint {d : ℕ} (σ₀ : ℝ) (v₀ z₀ : PDE.Vec d)
    (b : PDE.Vec d → PDE.Vec d) (r : {r : ℝ // 0 < r}) (q : KineticPoint d) : KineticPoint d :=
  ⟨σ₀ + r.1 ^ 2 * q.time, v₀ + r.1 • q.position,
    z₀ + (r.1 ^ 2 * q.time) • b v₀ + r.1 ^ 3 • q.velocity⟩

/-- Rescaled diffused domain, without a default outside the domain. -/
def scaledDomain {d : ℕ} (D : Set (PDE.Vec d)) (v₀ : PDE.Vec d) (r : {r : ℝ // 0 < r}) :
    Set (PDE.Vec d) := {Y | v₀ + r.1 • Y ∈ D}

/-- Literal rescaled coefficient. -/
def scaledCoefficient {d : ℕ} (B : CoefficientField d) (σ₀ : ℝ)
    (v₀ : PDE.Vec d) (r : {r : ℝ // 0 < r}) : CoefficientField d :=
  fun τ Y => B (σ₀ + r.1 ^ 2 * τ) (v₀ + r.1 • Y)

/-- Literal rescaled transport; source carrier includes only positive radii. -/
def scaledDrift {d : ℕ} (b : PDE.Vec d → PDE.Vec d) (v₀ : PDE.Vec d)
    (r : {r : ℝ // 0 < r}) : PDE.Vec d → PDE.Vec d :=
  fun Y => r.1⁻¹ • (b (v₀ + r.1 • Y) - b v₀)

/-- Identity transport has the source constants m=L_b=1. -/
theorem identityDrift_bounds (d : ℕ) : HasTransportBounds 1 1 (identityDrift d) := by
  constructor
  · intro y y'
    simp only [identityDrift, id_eq, one_mul, le_refl]
  · intro y ξ hξ
    change 1 ≤ PDE.vecDot ξ ((fderiv ℝ id y) ξ)
    rw [fderiv_id, ContinuousLinearMap.id_apply]
    change 1 ≤ PDE.vecNormSq ξ
    rw [← PDE.vecEuclideanNorm_sq, hξ]
    norm_num

/-- The Section 2 coefficient predicates supply the hypotheses of the full-coefficient statements.
-/
theorem sectionTwoCoefficient_fullBounds {d : ℕ} (lam Lam : ℝ)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B) :
    IsSmoothFullKineticCoefficient (zIndependentCoefficient B) ∧
      IsSymmetricFullKineticCoefficient (zIndependentCoefficient B) ∧
      HasEverywhereLoewnerBounds lam Lam (zIndependentCoefficient B) := by
  rcases hB with ⟨hpos, hle, hsmooth, hsymm, hlower, hupper⟩
  exact ⟨hsmooth, fun σ y z => hsymm σ y,
    fun σ y z => ⟨hlower σ y, hupper σ y⟩⟩

/-- Positive dilation leaves the whole-space diffused domain unchanged. -/
theorem scaledDomain_wholeSpace {d : ℕ} (v₀ : PDE.Vec d)
    (r : {r : ℝ // 0 < r}) : scaledDomain (wholeSpace d) v₀ r = wholeSpace d := by
  rfl

/-- Positive dilation and transport subtraction preserve identity drift. -/
theorem scaledDrift_identity {d : ℕ} (v₀ : PDE.Vec d)
    (r : {r : ℝ // 0 < r}) : scaledDrift (identityDrift d) v₀ r = identityDrift d := by
  funext Y
  simp only [scaledDrift, identityDrift, id_eq, add_sub_cancel_left,
    smul_smul, inv_mul_cancel₀ (ne_of_gt r.2), one_smul]


/-- Whole space discharges the source admissibility premise. -/
theorem wholeSpace_admissible (d : ℕ) : IsAdmissibleEvolutionDomain (wholeSpace d) :=
  Or.inl rfl

/-- The stationary whole-space curve discharges the piecewise smoothness premise. -/
theorem zeroCurve_piecewiseC1 (d : ℕ) :
    IsContinuousPiecewiseC1 (fun _ : ℝ => (0 : PDE.Vec d)) := by
  refine ⟨continuous_const, ?_⟩
  intro a b hab
  refine ⟨0, ![a, b], ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    exact contDiff_const.contDiffOn

/-- Identity transport is smooth, rather than requiring analyticity. -/
theorem identityDrift_smooth (d : ℕ) : IsSmoothDrift (identityDrift d) := contDiff_id

/-- The stationary case W has the literal whole-space fiber. -/
theorem movingDomain_wholeSpace (d : ℕ) (σ : ℝ) :
    movingDomain (wholeSpace d) (fun _ => 0) σ = univ := by
  simp [movingDomain, wholeSpace, PDE.translateSet]

/-- Remove only the whole-space membership proof, preserving the Euclidean carrier. -/
def wholeSpacePositionEquiv (d : ℕ) (σ : ℝ) :
    EvolutionPosition (wholeSpace d) (fun _ => 0) σ ≃ᵐ PDE.Vec d where
  toFun := Subtype.val
  invFun := fun y => ⟨y, by simp [movingDomain, wholeSpace, PDE.translateSet]⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := measurable_subtype_coe
  measurable_invFun := measurable_id.subtype_mk

/-- Every ordered whole-space point gives a valid query; there is no default query. -/
def wholeSpaceQuery {d : ℕ} (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d) :
    EvolutionQuery (wholeSpace d) (fun _ => 0) :=
  ⟨(σ, (τ, (v, z))), hστ, by simp [evolutionStateSet, movingDomain,
    wholeSpace, PDE.translateSet]⟩

/-- Affine coefficient rescaling preserves the original ellipticity constants. -/
theorem scaledCoefficient_sectionTwo {d : ℕ} (lam Lam : ℝ) (B : CoefficientField d)
    (hB : IsSectionTwoCoefficient lam Lam B) (σ₀ : ℝ) (v₀ : PDE.Vec d)
    (r : {r : ℝ // 0 < r}) :
    IsSectionTwoCoefficient lam Lam (scaledCoefficient B σ₀ v₀ r) := by
  rcases hB with ⟨hpos, hle, hsmooth, hsymm, hlower, hupper⟩
  refine ⟨hpos, hle, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (hsmooth i j).comp (by
      fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
          (σ₀ + r.1 ^ 2 * q.1, (v₀ + r.1 • q.2.1, q.2.2))))
  · intro σ y
    exact hsymm _ _
  · intro σ y
    exact hlower _ _
  · intro σ y
    exact hupper _ _

/-- Exact translation clause of the terminal evolution statement, after z independence.
Only use this clause for z-independent coefficients; general coefficients do not supply it.
-/
def IsTranslationCovariantEvolution {d : ℕ} (Ω : Set (PDE.Vec d))
    (γ : ℝ → PDE.Vec d) (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ) : Prop :=
  ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec d) (p : EvolutionState Ω γ σ),
    Measure.map (evolutionStateShift Ω γ τ h) (K.fiberKernel hΩ σ τ hστ p) =
      K.fiberKernel hΩ σ τ hστ (evolutionStateShift Ω γ σ h p)

/-- Exact domain-monotonicity implication, including its entire primed antecedent. -/
def IsDomainMonotoneEvolution {d : ℕ} (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (K : MovingFiberKernel Ω γ) : Prop :=
(∀ (Ω' : Set (PDE.Vec d)) (γ' : ℝ → PDE.Vec d)
            (hΩ' : IsAdmissibleEvolutionDomain Ω')
            (hγ' : IsContinuousPiecewiseC1 γ')
            (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆
              movingDomain Ω γ σ)
            (P' : TerminalOperatorFamily Ω' γ')
            (K' : MovingFiberKernel Ω' γ'),
          ((∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState d)),
              IsSmoothCompactTerminalDatum Ω' γ' τ F →
                ∃ u : KineticPoint d → ℝ,
                  IsClassicalTerminalSolution Ω' γ' B b τ F u ∧
                  (∀ (σ : ℝ) (hστ : σ ≤ τ)
                      (p : EvolutionState Ω' γ' σ),
                    u ⟨σ, p.1.1, p.1.2⟩ =
                      P' σ τ hστ (terminalStateDatum F) p) ∧
                  (∀ v : KineticPoint d → ℝ,
                    IsClassicalTerminalSolution Ω' γ' B b τ F v →
                      EqOn v u (evolutionPastClosedCylinder Ω' γ' τ)))) ∧
           (∀ (σ : ℝ),
             P' σ σ le_rfl =
               (LinearMap.id :
                 BoundedBorel (EvolutionState Ω' γ' σ) →ₗ[ℝ]
                   BoundedBorel (EvolutionState Ω' γ' σ))) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
               (f : BoundedBorel (EvolutionState Ω' γ' τ)),
             0 ≤ f → 0 ≤ P' σ τ hστ f) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
             P' σ τ hστ (1 : BoundedBorel (EvolutionState Ω' γ' τ)) ≤
               (1 : BoundedBorel (EvolutionState Ω' γ' σ))) ∧
           (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
             P' σ τ (hσr.trans hrτ) =
               (P' σ r hσr).comp (P' r τ hrτ)) ∧
           (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
               (p : EvolutionState Ω' γ' σ)
               (f : BoundedBorel (EvolutionState Ω' γ' τ)),
             P' σ τ hστ f p =
               ∫ q, f q ∂(K'.fiberKernel
                 (measurableSet_of_isAdmissibleEvolutionDomain hΩ')
                 σ τ hστ p)) ∧
           MovingFiberKernel.HasEndpoint K'
             (measurableSet_of_isAdmissibleEvolutionDomain hΩ') ∧
           MovingFiberKernel.HasComposition K'
             (measurableSet_of_isAdmissibleEvolutionDomain hΩ') →
          MovingFiberKernel.IsZeroExtensionDominatedBy K' K hsub)

/-- Exact parabolic clause, retaining one shared Q and every requirement of the terminal evolution
statement. -/
def HasParabolicMarginalBundle {d : ℕ} (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d)
    (K : MovingFiberKernel Ω γ) : Prop :=
(∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec d),
              B σ y z = B σ y z'),
          ∃ Q : ParabolicOperatorFamily Ω γ,
            (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
                (y : EvolutionPosition Ω γ σ) (z : PDE.Vec d),
              parabolicMarginalKernel K
                  hΩ
                  σ τ hστ y =
                K.fiberFirstMarginal
                  hΩ
                  σ τ hστ (evolutionStateOfPosition Ω γ σ y z)) ∧
            (∀ (σ : ℝ),
              Q σ σ le_rfl =
                (LinearMap.id :
                  BoundedBorel (EvolutionPosition Ω γ σ) →ₗ[ℝ]
                    BoundedBorel (EvolutionPosition Ω γ σ))) ∧
            (∀ (σ : ℝ) (τ : ℝ) (hστ : σ ≤ τ)
                (f : BoundedBorel (EvolutionPosition Ω γ τ)),
              0 ≤ f → 0 ≤ Q σ τ hστ f) ∧
            (∀ (σ τ : ℝ) (hστ : σ ≤ τ),
              Q σ τ hστ (1 : BoundedBorel (EvolutionPosition Ω γ τ)) ≤
                (1 : BoundedBorel (EvolutionPosition Ω γ σ))) ∧
            (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
              Q σ τ (hσr.trans hrτ) =
                (Q σ r hσr).comp (Q r τ hrτ)) ∧
            (∀ (σ τ : ℝ) (hστ : σ ≤ τ)
                (y : EvolutionPosition Ω γ σ)
                (f : BoundedBorel (EvolutionPosition Ω γ τ)),
              Q σ τ hστ f y =
                ∫ y', f y' ∂(parabolicMarginalKernel K
                  hΩ
                  σ τ hστ y)) ∧
            (∀ (E : Set (PDE.Vec d)) (hE : MeasurableSet E),
              Measurable (fun q : ParabolicEvolutionQuery Ω γ =>
                parabolicMarginalAmbientMeasure K
                  hΩ q E)) ∧
            (∀ (σ : ℝ),
              parabolicMarginalKernel K
                hΩ
                σ σ le_rfl =
                (ProbabilityTheory.Kernel.id :
                  ProbabilityTheory.Kernel
                    (EvolutionPosition Ω γ σ) (EvolutionPosition Ω γ σ))) ∧
            (∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
              parabolicMarginalKernel K
                  hΩ
                  σ τ (hσr.trans hrτ) =
                parabolicMarginalKernel K
                  hΩ
                  r τ hrτ ∘ₖ
                parabolicMarginalKernel K
                  hΩ
                  σ r hσr) ∧
            (∀ (τ : ℝ) (F : BoundedBorel (PDE.Vec d)),
              ParabolicProbe.IsSmoothCompactScalarTerminalDatum
                  Ω γ τ F →
                ∃ V : TimeVelocity d → ℝ,
                  ParabolicProbe.IsClassicalScalarTerminalSolution
                    Ω γ B τ F V ∧
                  (∀ (σ : ℝ) (hστ : σ ≤ τ)
                      (y : EvolutionPosition Ω γ σ),
                    V (σ, y.1) =
                      Q σ τ hστ (terminalPositionDatum F) y) ∧
                  (∀ W : TimeVelocity d → ℝ,
                    ParabolicProbe.IsClassicalScalarTerminalSolution
                      Ω γ B τ F W →
                      EqOn W V
                        (ParabolicProbe.scalarPastClosedCylinder Ω γ τ))))

/-- A bounded Borel function is integrable against every finite measure. -/
theorem boundedBorel_integrable {α : Type*} [MeasurableSpace α]
    (f : BoundedBorel α) (μ : Measure α) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C, hC, hbound⟩ := f.exists_bound
  exact Integrable.mono' (integrable_const C) f.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))

/-- Realization implies positivity on every bounded Borel datum. -/
theorem realizes_positive {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (h : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (f : BoundedBorel (EvolutionState Ω γ τ))
    (hf : 0 ≤ f) : 0 ≤ S σ τ hστ f := by
  change ∀ p, 0 ≤ S σ τ hστ f p
  intro p
  rw [h.2.1 σ τ hστ p f]
  exact integral_nonneg (fun q => hf q)

/-- Realization implies the source sub-Markov contraction. -/
theorem realizes_contraction {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (h : RealizesTerminalEvolution Ω γ hΩ B b S K) (σ τ : ℝ) (hστ : σ ≤ τ) :
    S σ τ hστ (1 : BoundedBorel (EvolutionState Ω γ τ)) ≤
      (1 : BoundedBorel (EvolutionState Ω γ σ)) := by
  change ∀ p, S σ τ hστ 1 p ≤ 1
  intro p
  rw [h.2.1 σ τ hστ p 1]
  simp only [BoundedBorel.one_apply, integral_const, smul_eq_mul, mul_one, measureReal_def]
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top (K.fiberKernel_mass_le_one hΩ σ τ hστ p)

/-- Realization implies the same shared operator family's composition law. -/
theorem realizes_composition {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (h : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    S σ τ (hσr.trans hrτ) = (S σ r hσr).comp (S r τ hrτ) := by
  have : ProbabilityTheory.IsFiniteKernel (K.fiberKernel hΩ σ r hσr) :=
    ⟨1, by norm_num, K.fiberKernel_mass_le_one hΩ σ r hσr⟩
  have : ProbabilityTheory.IsFiniteKernel (K.fiberKernel hΩ r τ hrτ) :=
    ⟨1, by norm_num, K.fiberKernel_mass_le_one hΩ r τ hrτ⟩
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  rw [h.2.1 σ τ (hσr.trans hrτ) p f, h.2.2.2 σ r τ hσr hrτ]
  rw [ProbabilityTheory.Kernel.integral_comp (boundedBorel_integrable f _)]
  change _ = S σ r hσr (S r τ hrτ f) p
  rw [h.2.1 σ r hσr p (S r τ hrτ f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => (h.2.1 r τ hrτ q f).symm)

/-- Realization implies the endpoint operator identity needed by monotonicity. -/
theorem realizes_endpoint {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (hΩ : MeasurableSet Ω) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (h : RealizesTerminalEvolution Ω γ hΩ B b S K) (σ : ℝ) :
    S σ σ le_rfl = (LinearMap.id : BoundedBorel (EvolutionState Ω γ σ) →ₗ[ℝ]
      BoundedBorel (EvolutionState Ω γ σ)) := by
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  rw [h.2.1 σ σ le_rfl p f, h.2.2.1 σ]
  simp only [ProbabilityTheory.Kernel.id_apply, integral_dirac, LinearMap.id_apply]

/-- The exact monotonicity clause applies to any supplied primed realization. -/
theorem domainMonotone_of_realizes {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (K : MovingFiberKernel Ω γ) (hmono : IsDomainMonotoneEvolution Ω γ B b K)
    (Ω' : Set (PDE.Vec d)) (γ' : ℝ → PDE.Vec d)
    (hΩ' : IsAdmissibleEvolutionDomain Ω') (hγ' : IsContinuousPiecewiseC1 γ')
    (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆ movingDomain Ω γ σ)
    (S' : TerminalOperatorFamily Ω' γ') (K' : MovingFiberKernel Ω' γ')
    (h' : RealizesTerminalEvolution Ω' γ'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') B b S' K') :
    MovingFiberKernel.IsZeroExtensionDominatedBy K' K hsub := by
  let hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ'
  exact hmono Ω' γ' hΩ' hγ' hsub S' K'
    ⟨h'.1, realizes_endpoint hΩm B b S' K' h',
      fun σ τ hστ f hf => realizes_positive hΩm B b S' K' h' σ τ hστ f hf,
      realizes_contraction hΩm B b S' K' h',
      realizes_composition hΩm B b S' K' h', h'.2.1, h'.2.2.1, h'.2.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
