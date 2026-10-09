module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-!
# Parabolic scaling for the common terminal minorant (companion paper, Lemma 3.6)

The scalar parabolic marginal of the rescaled problem on `B₄(0)` is the affine image of the
marginal of the original problem on `B_{4ρ}(v₀)`.  The proof uses only the scalar clause of
`HasParabolicMarginalBundle`: a classical scalar terminal solution composed with the affine map
`(s, y) ↦ (T + ρ² s, v₀ + ρ y)` is a classical scalar terminal solution of the rescaled
problem, so the supplied uniqueness identifies the two, and smooth compactly supported tests
determine the marginal measures.  No existence or regularity premise is added.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Scaling (sliceHessian_affine)
open scoped ENNReal Topology

/-- The source normalized coefficient `B(T + ρ² s, v₀ + ρ y)`. -/
def normalizedParabolicCoefficient {d : ℕ} (B : CoefficientField d)
    (T ρ : ℝ) (v0 : PDE.Vec d) : CoefficientField d :=
  fun s y => B (T + ρ ^ 2 * s) (v0 + ρ • y)

/-- The spatial affine map `y ↦ v₀ + ρ y` of the parabolic scaling. -/
def parabolicAffine {d : ℕ} (v0 : PDE.Vec d) (ρ : ℝ) (y : PDE.Vec d) : PDE.Vec d :=
  v0 + ρ • y

/-- The normalized coefficient is the Section 2 affine coefficient rescaling. -/
theorem normalizedParabolicCoefficient_eq_scaledCoefficient {d : ℕ}
    (B : CoefficientField d) (T : ℝ) (v0 : PDE.Vec d) (ρ : ℝ) (hρ : 0 < ρ) :
    normalizedParabolicCoefficient B T ρ v0 = scaledCoefficient B T v0 ⟨ρ, hρ⟩ := rfl

/-- The normalized coefficients have the same ellipticity constants. -/
theorem normalizedParabolicCoefficient_sectionTwo {d : ℕ} (lam Lam : ℝ)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (T : ℝ) (v0 : PDE.Vec d) (ρ : ℝ) (hρ : 0 < ρ) :
    IsSectionTwoCoefficient lam Lam (normalizedParabolicCoefficient B T ρ v0) :=
  scaledCoefficient_sectionTwo lam Lam B hB T v0 ⟨ρ, hρ⟩

/-! ### Scalar affine calculus -/

/-- The affine change of scalar parabolic variables `(s, y) ↦ (α + a s, c + e y)`. -/
def scalarAffine {d : ℕ} (α a : ℝ) (c : PDE.Vec d) (e : ℝ) (z : TimeVelocity d) :
    TimeVelocity d :=
  (α + a * z.1, c + e • z.2)

theorem contDiff_scalarAffine {d : ℕ} (α a : ℝ) (c : PDE.Vec d) (e : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarAffine α a c e) := by
  unfold scalarAffine
  fun_prop

/-- Time derivative under an affine change of variables. -/
theorem scalarTimeDerivative_comp_scalarAffine {d : ℕ} {V : TimeVelocity d → ℝ}
    {α a : ℝ} {c : PDE.Vec d} {e : ℝ} {z : TimeVelocity d}
    (hV : DifferentiableAt ℝ (fun r : ℝ => V (r, c + e • z.2)) (α + a * z.1)) :
    scalarTimeDerivative (fun p => V (scalarAffine α a c e p)) z =
      a * scalarTimeDerivative V (scalarAffine α a c e z) := by
  unfold scalarTimeDerivative scalarAffine
  have h1 : HasDerivAt (fun r : ℝ => α + a * r) a z.1 := by
    simpa using ((hasDerivAt_id z.1).const_mul a).const_add α
  have h2 := hV.hasDerivAt.comp z.1 h1
  have h3 := h2.deriv
  simp only [Function.comp_def] at h3
  simp only [h3]
  ring

/-- Spatial Hessian under an affine change of variables. -/
theorem scalarSpatialHessian_comp_scalarAffine {d : ℕ} {V : TimeVelocity d → ℝ}
    {α a : ℝ} {c : PDE.Vec d} {e : ℝ} {z : TimeVelocity d}
    (hV : ContDiffAt ℝ 2 (fun y : PDE.Vec d => V (α + a * z.1, y)) (c + e • z.2)) :
    scalarSpatialHessian (fun p => V (scalarAffine α a c e p)) z =
      e ^ 2 • scalarSpatialHessian V (scalarAffine α a c e z) := by
  exact sliceHessian_affine (g := fun y : PDE.Vec d => V (α + a * z.1, y)) hV


/-! ### Geometry of the stationary scalar cylinders -/

/-- The stationary curve does not move the domain. -/
@[simp]
theorem movingDomain_stationary {d : ℕ} (Ω : Set (PDE.Vec d)) (σ : ℝ) :
    movingDomain Ω stationary σ = Ω := by
  ext y
  simp [movingDomain, stationary, PDE.translateSet]

@[simp]
theorem mem_scalarPastClosedCylinder_stationary {d : ℕ} {Ω : Set (PDE.Vec d)} {τ : ℝ}
    {p : TimeVelocity d} :
    p ∈ ParabolicProbe.scalarPastClosedCylinder Ω stationary τ ↔
      p.1 ≤ τ ∧ p.2 ∈ closure Ω := by
  simp [ParabolicProbe.scalarPastClosedCylinder]

@[simp]
theorem mem_scalarPastOpenCylinder_stationary {d : ℕ} {Ω : Set (PDE.Vec d)} {τ : ℝ}
    {p : TimeVelocity d} :
    p ∈ ParabolicProbe.scalarPastOpenCylinder Ω stationary τ ↔ p.1 < τ ∧ p.2 ∈ Ω := by
  simp [ParabolicProbe.scalarPastOpenCylinder]

@[simp]
theorem mem_scalarTerminalClosure_stationary {d : ℕ} {Ω : Set (PDE.Vec d)} {τ : ℝ}
    {p : TimeVelocity d} :
    p ∈ ParabolicProbe.scalarTerminalClosure Ω stationary τ ↔ p.1 = τ ∧ p.2 ∈ closure Ω := by
  simp [ParabolicProbe.scalarTerminalClosure]

@[simp]
theorem mem_scalarLateralFrontier_stationary {d : ℕ} {Ω : Set (PDE.Vec d)} {τ : ℝ}
    {p : TimeVelocity d} :
    p ∈ ParabolicProbe.scalarLateralFrontier Ω stationary τ ↔
      p.1 ≤ τ ∧ p.2 ∈ frontier Ω := by
  simp [ParabolicProbe.scalarLateralFrontier]

/-- The stationary open past cylinder of an open domain is open. -/
theorem isOpen_scalarPastOpenCylinder_stationary {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (τ : ℝ) :
    IsOpen (ParabolicProbe.scalarPastOpenCylinder Ω stationary τ) := by
  have : ParabolicProbe.scalarPastOpenCylinder Ω stationary τ =
      {p : TimeVelocity d | p.1 < τ} ∩ {p | p.2 ∈ Ω} := by
    ext p; simp
  rw [this]
  exact (isOpen_lt continuous_fst continuous_const).inter (hΩ.preimage continuous_snd)

/-- The spatial parabolic scaling is a homeomorphism for `ρ > 0`. -/
def parabolicAffineHomeo {d : ℕ} (v0 : PDE.Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    PDE.Vec d ≃ₜ PDE.Vec d :=
  (Homeomorph.smulOfNeZero ρ hρ.ne').trans (Homeomorph.addLeft v0)

theorem parabolicAffineHomeo_apply {d : ℕ} (v0 : PDE.Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    ⇑(parabolicAffineHomeo v0 hρ) = parabolicAffine v0 ρ := rfl

theorem contDiff_parabolicAffine {d : ℕ} (v0 : PDE.Vec d) (ρ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (parabolicAffine v0 ρ) := by
  unfold parabolicAffine
  fun_prop

theorem continuous_parabolicAffine {d : ℕ} (v0 : PDE.Vec d) (ρ : ℝ) :
    Continuous (parabolicAffine v0 ρ) :=
  (contDiff_parabolicAffine v0 ρ).continuous

/-- The preimage of the big ball under the scaling is the normalized ball. -/
theorem parabolicAffine_preimage_ball {d : ℕ} (v0 : PDE.Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    parabolicAffine v0 ρ ⁻¹' PDE.euclideanBall v0 (4 * ρ) = PDE.euclideanBall 0 4 := by
  ext y
  change PDE.euclideanSqDist (v0 + ρ • y) v0 < (4 * ρ) ^ 2 ↔ PDE.euclideanSqDist y 0 < 4 ^ 2
  rw [add_comm, PDE.euclideanSqDist_affine_center]
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  constructor <;> intro h <;> nlinarith

/-- Closures commute with the scaling preimage. -/
theorem parabolicAffine_preimage_closure {d : ℕ} (v0 : PDE.Vec d) {ρ : ℝ} (hρ : 0 < ρ)
    (S : Set (PDE.Vec d)) :
    parabolicAffine v0 ρ ⁻¹' closure S = closure (parabolicAffine v0 ρ ⁻¹' S) :=
  (parabolicAffineHomeo v0 hρ).preimage_closure S

/-- Frontiers commute with the scaling preimage. -/
theorem parabolicAffine_preimage_frontier {d : ℕ} (v0 : PDE.Vec d) {ρ : ℝ} (hρ : 0 < ρ)
    (S : Set (PDE.Vec d)) :
    parabolicAffine v0 ρ ⁻¹' frontier S = frontier (parabolicAffine v0 ρ ⁻¹' S) :=
  (parabolicAffineHomeo v0 hρ).preimage_frontier S


/-! ### The scalar marginal measures -/

/-- Every scalar marginal measure is finite (indeed sub-Markov). -/
instance isFiniteMeasure_P {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (q : ParabolicEvolutionQuery Ω γ) :
    IsFiniteMeasure (P K hΩ q) := by
  refine ⟨?_⟩
  unfold P parabolicMarginalAmbientMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
    parabolicMarginalKernel_apply, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ q.1.2.1),
    Measure.map_apply (MovingFiberKernel.measurable_firstPosition Ω γ q.1.2.1)
      MeasurableSet.univ, preimage_univ]
  exact lt_of_le_of_lt (K.fiberKernel_mass_le_one hΩ _ _ _ _) ENNReal.one_lt_top

/-- The scalar marginal measure of a stationary problem gives no mass outside `Ω`. -/
theorem P_compl_eq_zero_stationary {d : ℕ} {Ω : Set (PDE.Vec d)}
    (K : MovingFiberKernel Ω stationary) (hΩ : MeasurableSet Ω)
    (q : ParabolicEvolutionQuery Ω stationary) : P K hΩ q Ωᶜ = 0 := by
  unfold P parabolicMarginalAmbientMeasure
  rw [Measure.map_apply measurable_subtype_coe hΩ.compl]
  have : ((↑) : EvolutionPosition Ω stationary q.1.2.1 → PDE.Vec d) ⁻¹' Ωᶜ = ∅ := by
    ext y
    have hy := y.2
    simp only [movingDomain_stationary] at hy
    simp [hy]
  rw [this, measure_empty]

/-- A smooth compactly supported function as a bounded Borel function. -/
def smoothTestBorel {d : ℕ} (φ : PDE.Vec d → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : BoundedBorel (PDE.Vec d) :=
  ⟨φ, hφ.measurable, by
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hc
    exact ⟨max C 0, le_max_right _ _, fun y => by
      simpa only [Real.norm_eq_abs] using (hC y).trans (le_max_left _ _)⟩⟩

@[simp]
theorem smoothTestBorel_apply {d : ℕ} (φ : PDE.Vec d → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (y : PDE.Vec d) : smoothTestBorel φ hφ hc y = φ y := rfl

/-- **Scalar probe.**  The supplied parabolic marginal bundle gives, for every smooth compactly
supported test supported in `Ω`, a classical scalar terminal solution, unique on the closed
past cylinder, whose values are the integrals of the test against the marginal measures. -/
theorem exists_scalar_probe {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : MeasurableSet Ω)
    (B : CoefficientField d) (K : MovingFiberKernel Ω stationary)
    (hpar : HasParabolicMarginalBundle Ω stationary hΩ (zIndependentCoefficient B) K)
    (φ : PDE.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ω) (τ : ℝ) :
    ∃ V : TimeVelocity d → ℝ,
      ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
        (zIndependentCoefficient B) τ (smoothTestBorel φ hφ.continuous hc) V ∧
      (∀ W : TimeVelocity d → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
          (zIndependentCoefficient B) τ (smoothTestBorel φ hφ.continuous hc) W →
        EqOn W V (ParabolicProbe.scalarPastClosedCylinder Ω stationary τ)) ∧
      ∀ (σ : ℝ) (hστ : σ ≤ τ) (y : PDE.Vec d) (hy : y ∈ movingDomain Ω stationary σ),
        V (σ, y) = ∫ x, φ x ∂(P K hΩ (scalarQuery σ τ hστ y hy)) := by
  obtain ⟨Q, -, -, -, -, -, hrepr, -, -, -, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  obtain ⟨V, hV, hVQ, huniq⟩ := hsolve τ (smoothTestBorel φ hφ.continuous hc)
    ⟨hφ, hc, by
      have h : tsupport φ ⊆ movingDomain Ω stationary τ := by
        simpa only [movingDomain_stationary] using hsupp
      exact h⟩
  refine ⟨V, hV, huniq, fun σ hστ y hy => ?_⟩
  rw [hVQ σ hστ ⟨y, hy⟩, hrepr σ τ hστ ⟨y, hy⟩ _]
  unfold P parabolicMarginalAmbientMeasure
  rw [integral_map measurable_subtype_coe.aemeasurable hφ.continuous.aestronglyMeasurable]
  rfl


/-! ### Scaled solutions -/

/-- The affine change of variables of the minorant scaling. -/
abbrev minorantAffine {d : ℕ} (T ρ : ℝ) (v0 : PDE.Vec d) : TimeVelocity d → TimeVelocity d :=
  scalarAffine T (ρ ^ 2) v0 ρ

private theorem matrixContraction_smul_right {d : ℕ} (A H : PDE.Mat d) (c : ℝ) :
    matrixContraction A (c • H) = c * matrixContraction A H := by
  simp only [matrixContraction, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The scalar parabolic operator of the rescaled problem is `ρ²` times the original one. -/
theorem scalarParabolicOperator_comp_minorantAffine {d : ℕ} (B : CoefficientField d)
    (T ρ : ℝ) (v0 : PDE.Vec d) {V : TimeVelocity d → ℝ} {p : TimeVelocity d}
    (htime : DifferentiableAt ℝ (fun r : ℝ => V (r, (minorantAffine T ρ v0 p).2))
      (minorantAffine T ρ v0 p).1)
    (hspace : ContDiffAt ℝ 2 (fun y : PDE.Vec d => V ((minorantAffine T ρ v0 p).1, y))
      (minorantAffine T ρ v0 p).2) :
    scalarParabolicOperator
        (fun σ y => zIndependentCoefficient (normalizedParabolicCoefficient B T ρ v0) σ y 0) 0
        (fun p => V (minorantAffine T ρ v0 p)) p =
      ρ ^ 2 * scalarParabolicOperator (fun σ y => zIndependentCoefficient B σ y 0) 0
        V (minorantAffine T ρ v0 p) := by
  have hgrad : PDE.vecDot ((0 : ℝ → PDE.Vec d → PDE.Vec d) p.1 p.2)
      (scalarSpatialGradient (fun p => V (minorantAffine T ρ v0 p)) p) = 0 := by
    simp [PDE.vecDot]
  have hgrad' : PDE.vecDot ((0 : ℝ → PDE.Vec d → PDE.Vec d)
      (minorantAffine T ρ v0 p).1 (minorantAffine T ρ v0 p).2)
      (scalarSpatialGradient V (minorantAffine T ρ v0 p)) = 0 := by
    simp [PDE.vecDot]
  rw [scalarParabolicOperator_apply, scalarParabolicOperator_apply, hgrad, hgrad',
    scalarTimeDerivative_comp_scalarAffine htime, scalarSpatialHessian_comp_scalarAffine hspace,
    matrixContraction_smul_right]
  simp only [zIndependentCoefficient, normalizedParabolicCoefficient, minorantAffine,
    scalarAffine]
  ring

/-- **Scaled solutions.**  Composing a classical scalar terminal solution with the parabolic
scaling gives a classical scalar terminal solution of the rescaled problem. -/
theorem isClassicalScalarTerminalSolution_comp_minorantAffine {d : ℕ}
    {Ω Ω' : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (B : CoefficientField d) (T : ℝ)
    (v0 : PDE.Vec d) {ρ : ℝ} (hρ : 0 < ρ) (hΩ' : Ω' = parabolicAffine v0 ρ ⁻¹' Ω)
    (τ' : ℝ) (F F' : BoundedBorel (PDE.Vec d))
    (hF' : ∀ y, F' y = F (parabolicAffine v0 ρ y)) {V : TimeVelocity d → ℝ}
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary
      (zIndependentCoefficient B) (T + ρ ^ 2 * τ') F V) :
    ParabolicProbe.IsClassicalScalarTerminalSolution Ω' stationary
      (zIndependentCoefficient (normalizedParabolicCoefficient B T ρ v0)) τ' F'
      (fun p => V (minorantAffine T ρ v0 p)) := by
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have hAff := contDiff_scalarAffine T (ρ ^ 2) v0 ρ
  have hcl : closure Ω' = parabolicAffine v0 ρ ⁻¹' closure Ω := by
    rw [hΩ', parabolicAffine_preimage_closure v0 hρ]
  have hfr : frontier Ω' = parabolicAffine v0 ρ ⁻¹' frontier Ω := by
    rw [hΩ', parabolicAffine_preimage_frontier v0 hρ]
  have hmapClosed : MapsTo (minorantAffine T ρ v0)
      (ParabolicProbe.scalarPastClosedCylinder Ω' stationary τ')
      (ParabolicProbe.scalarPastClosedCylinder Ω stationary (T + ρ ^ 2 * τ')) := by
    intro p hp
    rw [mem_scalarPastClosedCylinder_stationary] at hp ⊢
    refine ⟨?_, ?_⟩
    · change T + ρ ^ 2 * p.1 ≤ T + ρ ^ 2 * τ'
      nlinarith [hp.1]
    · have := hp.2
      rw [hcl] at this
      exact this
  have hmapOpen : MapsTo (minorantAffine T ρ v0)
      (ParabolicProbe.scalarPastOpenCylinder Ω' stationary τ')
      (ParabolicProbe.scalarPastOpenCylinder Ω stationary (T + ρ ^ 2 * τ')) := by
    intro p hp
    rw [mem_scalarPastOpenCylinder_stationary] at hp ⊢
    refine ⟨?_, ?_⟩
    · change T + ρ ^ 2 * p.1 < T + ρ ^ 2 * τ'
      nlinarith [hp.1]
    · have := hp.2
      rw [hΩ'] at this
      exact this
  have hmapTerm : MapsTo (minorantAffine T ρ v0)
      (ParabolicProbe.scalarTerminalClosure Ω' stationary τ')
      (ParabolicProbe.scalarTerminalClosure Ω stationary (T + ρ ^ 2 * τ')) := by
    intro p hp
    rw [mem_scalarTerminalClosure_stationary] at hp ⊢
    refine ⟨?_, ?_⟩
    · change T + ρ ^ 2 * p.1 = T + ρ ^ 2 * τ'
      rw [hp.1]
    · have := hp.2
      rw [hcl] at this
      exact this
  have hmapLat : MapsTo (minorantAffine T ρ v0)
      (ParabolicProbe.scalarLateralFrontier Ω' stationary τ')
      (ParabolicProbe.scalarLateralFrontier Ω stationary (T + ρ ^ 2 * τ')) := by
    intro p hp
    rw [mem_scalarLateralFrontier_stationary] at hp ⊢
    refine ⟨?_, ?_⟩
    · change T + ρ ^ 2 * p.1 ≤ T + ρ ^ 2 * τ'
      nlinarith [hp.1]
    · have := hp.2
      rw [hfr] at this
      exact this
  obtain ⟨⟨C, hC0, hC⟩, hcont, hsmooth, heq, hterm, hlat⟩ := hV
  refine ⟨⟨C, hC0, fun p hp => hC _ (hmapClosed hp)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcont.comp hAff.continuous.continuousOn hmapClosed
  · exact hsmooth.comp hAff.contDiffOn hmapOpen
  · intro p hp
    have hopen := isOpen_scalarPastOpenCylinder_stationary hΩ (T + ρ ^ 2 * τ')
    have hp' := hmapOpen hp
    have hc12 := isScalarC12On_of_isOpen_contDiffOn_two hopen
      (hsmooth.of_le (by norm_num))
    rw [scalarParabolicOperator_comp_minorantAffine B T ρ v0
      (hc12.timeSlice_differentiableAt hp') (hc12.spatialSlice_contDiffAt hp'), heq _ hp', mul_zero]
  · intro p hp
    rw [hF' p.2]
    exact hterm _ (hmapTerm hp)
  · intro p hp
    exact hlat _ (hmapLat hp)


/-! ### The scaling theorem -/

/-- **Parabolic scaling of the common minorant** (companion paper, Lemma 3.6).  The
scalar marginal of the rescaled problem on `B₄(0)` is carried by the affine map
`y ↦ v₀ + ρ y` to the scalar marginal of the original problem on `B_{4ρ}(v₀)`. -/
theorem parabolic_minorant_scaling {d : ℕ} (lam Lam : ℝ) (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (v0 : PDE.Vec d) (ρ T : ℝ) (hρ : 0 < ρ)
    (S : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * ρ)) stationary)
    (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary)
    (S' : TerminalOperatorFamily (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary)
    (K' : MovingFiberKernel (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
      (zIndependentCoefficient B) b S K)
    (hpar : HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
      (zIndependentCoefficient B) K)
    (hreal' : RealizesTerminalEvolution (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
      (PDE.isOpen_euclideanBall 0 4).measurableSet
      (zIndependentCoefficient (normalizedParabolicCoefficient B T ρ v0)) id S' K')
    (hpar' : HasParabolicMarginalBundle (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary
      (PDE.isOpen_euclideanBall 0 4).measurableSet
      (zIndependentCoefficient (normalizedParabolicCoefficient B T ρ v0)) K')
    (q : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary)
    (q' : ParabolicEvolutionQuery (PDE.euclideanBall (0 : PDE.Vec d) 4) stationary)
    (hq : q.1.1 = T + ρ ^ 2 * q'.1.1)
    (hτ : q.1.2.1 = T + ρ ^ 2 * q'.1.2.1)
    (hv : q.1.2.2 = parabolicAffine v0 ρ q'.1.2.2) :
    Measure.map (parabolicAffine v0 ρ)
      (P K' (PDE.isOpen_euclideanBall 0 4).measurableSet q') =
        P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet q := by
  have _ := And.intro hB (And.intro hreal hreal')  -- source premises, not needed by the proof
  have hΩo := PDE.isOpen_euclideanBall v0 (4 * ρ)
  have hΩo' := PDE.isOpen_euclideanBall (0 : PDE.Vec d) 4
  rcases q with ⟨⟨σ, τ, y⟩, hστ, hy⟩
  rcases q' with ⟨⟨σ', τ', y'⟩, hστ', hy'⟩
  dsimp only at hq hτ hv
  subst hq hτ hv
  refine measure_eq_of_smooth_integral_eq hΩo ?_ ?_ ?_
  · rw [Measure.map_apply (continuous_parabolicAffine v0 ρ).measurable
      hΩo.measurableSet.compl, preimage_compl, parabolicAffine_preimage_ball v0 hρ]
    exact P_compl_eq_zero_stationary K' _ _
  · exact P_compl_eq_zero_stationary K _ _
  · intro φ hφ hc hsupp _
    rw [integral_map (continuous_parabolicAffine v0 ρ).aemeasurable
      hφ.continuous.aestronglyMeasurable]
    obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩo.measurableSet B K hpar φ hφ hc hsupp
      (T + ρ ^ 2 * τ')
    have hφ' : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ (parabolicAffine v0 ρ x)) :=
      hφ.comp (contDiff_parabolicAffine v0 ρ)
    have hc' : HasCompactSupport (fun x => φ (parabolicAffine v0 ρ x)) :=
      hc.comp_homeomorph (parabolicAffineHomeo v0 hρ)
    have hsupp' : tsupport (fun x => φ (parabolicAffine v0 ρ x)) ⊆
        PDE.euclideanBall (0 : PDE.Vec d) 4 := by
      have h1 : tsupport (fun x => φ (parabolicAffine v0 ρ x)) =
          parabolicAffine v0 ρ ⁻¹' tsupport φ := by
        unfold tsupport
        rw [parabolicAffine_preimage_closure v0 hρ]
        congr 1
      rw [h1, ← parabolicAffine_preimage_ball v0 hρ]
      exact preimage_mono hsupp
    obtain ⟨V', hV', huniq', hV'eval⟩ := exists_scalar_probe hΩo'.measurableSet
      (normalizedParabolicCoefficient B T ρ v0) K' hpar' _ hφ' hc' hsupp' τ'
    have hW := isClassicalScalarTerminalSolution_comp_minorantAffine hΩo B T v0 hρ
      (parabolicAffine_preimage_ball v0 hρ).symm τ' (smoothTestBorel φ hφ.continuous hc)
      (smoothTestBorel _ hφ'.continuous hc') (fun x => rfl) hV
    have hy'' : y' ∈ PDE.euclideanBall (0 : PDE.Vec d) 4 := by
      simpa only [movingDomain_stationary] using hy'
    have hcl : ((σ', y') : TimeVelocity d) ∈
        ParabolicProbe.scalarPastClosedCylinder (PDE.euclideanBall (0 : PDE.Vec d) 4)
          stationary τ' := by
      rw [mem_scalarPastClosedCylinder_stationary]
      exact ⟨hστ', subset_closure hy''⟩
    have e1 := hVeval (T + ρ ^ 2 * σ') hστ (parabolicAffine v0 ρ y') hy
    have e2 := hV'eval σ' hστ' y' hy'
    have e3 : V' (σ', y') = V (T + ρ ^ 2 * σ', parabolicAffine v0 ρ y') :=
      (huniq' _ hW hcl).symm
    exact e2.symm.trans (e3.trans e1)

end HypoellipticAleksandrov.KineticAleksandrov.Decay
