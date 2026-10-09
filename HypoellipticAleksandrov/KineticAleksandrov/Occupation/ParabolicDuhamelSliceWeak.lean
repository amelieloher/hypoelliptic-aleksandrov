module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelLayer
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSlice

/-!
# Cut-off weak identity for one source slice

For one source time `r`, let `V` be the classical solution of `P₀ V = 0` in the open cylinder
`{s < r, v ∈ Ω_s}`.  Testing the transported adjoint against `Θ((r - σ)/h) ψ`, whose support lies
in the open cylinder, gives the cut-off weak identity
`∫ u Θ_h Lop^*ψ + ∫ u h⁻¹ Θ'_h ψ = 0` for the bounded Borel extension `u` of `V`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/-- The transported adjoint of a smooth test is smooth. -/
theorem contDiff_transportedAdjoint {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedAdjoint B b ψ) := by
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE d).contDiff
  have hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) :=
    fun i j => (hA i j).mul hψ
  have hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : EvolutionVec d =>
      fderiv ℝ (fun w : EvolutionVec d =>
        B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) := fun i j => contDiff_fderiv_apply (hF i j) _
  unfold transportedAdjoint
  refine (((contDiff_fderiv_apply hψ _).neg).add ?_).sub ?_
  · exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_fderiv_apply (hG i j) _
  · refine ContDiff.sum fun l _ => ?_
    exact ((contDiff_pi.1 hb l).comp (diffusedCoord d).contDiff).mul
      (contDiff_fderiv_apply hψ _)

/-- The transported adjoint of a compactly supported test is compactly supported. -/
theorem hasCompactSupport_transportedAdjoint {B : FullKineticCoefficient d}
    {b : PDE.Vec d → PDE.Vec d} {ψ : EvolutionVec d → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (transportedAdjoint B b ψ) :=
  HasCompactSupport.intro hc fun _ hx => transportedAdjoint_eq_zero_of_notMem_tsupport ψ hx

/-- The cutoff in the source-time variable. -/
def sliceCutoff (r h t : ℝ) : ℝ := layerStep ((r - t) / h)

theorem contDiff_sliceCutoff (r h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (sliceCutoff r h) :=
  contDiff_layerStep.comp ((contDiff_const.sub contDiff_id).div_const h)

theorem deriv_sliceCutoff (r h t : ℝ) :
    deriv (sliceCutoff r h) t = -(h⁻¹ * layerKernel ((r - t) / h)) := by
  have h1 : HasDerivAt (fun t : ℝ => (r - t) / h) (-h⁻¹) t := by
    have := ((hasDerivAt_id t).const_sub r).div_const h
    simpa [div_eq_mul_inv] using this
  have h2 := (hasDerivAt_layerStep ((r - t) / h)).comp t h1
  have : deriv (sliceCutoff r h) t = layerKernel ((r - t) / h) * -h⁻¹ := h2.deriv
  rw [this]
  ring

/-- Where the cutoff is nonzero, the time is below `r - h`. -/
theorem lt_of_sliceCutoff_ne_zero {r h t : ℝ} (hh : 0 < h) (hne : sliceCutoff r h t ≠ 0) :
    t < r - h := by
  by_contra hlt
  apply hne
  apply layerStep_of_le
  rw [div_le_iff₀ hh]
  linarith [not_lt.1 hlt]

theorem sliceCutoff_nonneg (r h t : ℝ) : 0 ≤ sliceCutoff r h t :=
  Real.smoothTransition.nonneg _

theorem sliceCutoff_le_one (r h t : ℝ) : sliceCutoff r h t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- **Cut-off weak identity for one source slice.** -/
theorem slice_cutoff_identity {B' : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B'))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (TimeVelocity d)} (hD : IsOpen D) {V u : TimeVelocity d → ℝ}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V D)
    (hVeq : ∀ p ∈ D, scalarParabolicOperator B' (fun _ _ => 0) V p = 0)
    (huV : ∀ p ∈ D, u p = V p) (hum : Measurable u) (C : ℝ) (hub : ∀ p, |u p| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (r : ℝ) (hψD : ∀ x ∈ tsupport ψ, Evolution.timeCoord d x < r →
      evolutionToTimeVelocity d x ∈ D)
    (h : ℝ) (hh : 0 < h) :
    (∫ x, u (evolutionToTimeVelocity d x) *
        (layerStep ((r - Evolution.timeCoord d x) / h) *
          transportedAdjoint (zIndependentCoefficient B') b ψ x)) +
      ∫ x, u (evolutionToTimeVelocity d x) *
        (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) = 0 := by
  set Qp := evolutionToTimeVelocity d with hQp
  set Ladj := transportedAdjoint (zIndependentCoefficient B') b with hLadj
  have hQc : Continuous Qp := Qp.continuous
  have hU : IsOpen (Qp ⁻¹' D) := hD.preimage hQc
  have hχ := contDiff_sliceCutoff r h
  let φ : EvolutionVec d → ℝ := fun x => sliceCutoff r h (Evolution.timeCoord d x) * ψ x
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp (Evolution.timeCoord d).contDiff).mul hψ
  have hφc : HasCompactSupport φ := hc.mul_left
  have hφsub : tsupport φ ⊆ Qp ⁻¹' D := by
    intro x hx
    have h1 : x ∈ tsupport ψ := tsupport_mul_subset_right hx
    have h2 : tsupport φ ⊆ {x | Evolution.timeCoord d x ≤ r - h} := by
      apply closure_minimal
      · intro y hy
        have hy1 : sliceCutoff r h (Evolution.timeCoord d y) ≠ 0 := left_ne_zero_of_mul hy
        exact (lt_of_sliceCutoff_ne_zero hh hy1).le
      · exact isClosed_le (Evolution.timeCoord d).continuous continuous_const
    exact hψD x h1 (by have := h2 hx; simp only [mem_ofPred_eq] at this; linarith)
  have key := integral_transportedAdjoint_zIndep hB hb hD hV hφs hφc hφsub
  have hR : (∫ x in Qp ⁻¹' D, scalarParabolicOperator B' (fun _ _ => 0) V (Qp x) * φ x) = 0 := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun _ => (0 : ℝ))]
    · simp
    · intro x hx
      simp only [hVeq _ hx, zero_mul]
  rw [hR] at key
  have hL : (∫ x in Qp ⁻¹' D, V (Qp x) * Ladj φ x) = ∫ x, u (Qp x) * Ladj φ x := by
    rw [setIntegral_congr_fun hU.measurableSet (g := fun x => u (Qp x) * Ladj φ x)]
    · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have : x ∉ tsupport φ := fun h' => hx (hφsub h')
      rw [hLadj, transportedAdjoint_eq_zero_of_notMem_tsupport φ this, mul_zero]
    · intro x hx
      simp only [huV _ hx]
  rw [hL] at key
  have hexp : ∀ x, Ladj φ x = sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x +
      h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x := by
    intro x
    simp only [hLadj, φ]
    rw [transportedAdjoint_cutoff_mul hB hχ hψ x, deriv_sliceCutoff]
    ring
  simp_rw [hexp, mul_add] at key
  have hLc : Continuous (Ladj ψ) := (contDiff_transportedAdjoint hB hb hψ).continuous
  have hLcs : HasCompactSupport (Ladj ψ) := hasCompactSupport_transportedAdjoint hc
  have hmeasu : Measurable (fun x => u (Qp x)) := hum.comp hQc.measurable
  have hbd : ∀ᵐ x ∂(volume : Measure (EvolutionVec d)), ‖u (Qp x)‖ ≤ C :=
    Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hub (Qp x)
  have i1 : Integrable (fun x => u (Qp x) * (sliceCutoff r h (Evolution.timeCoord d x) *
      Ladj ψ x)) := by
    have : Integrable (fun x => sliceCutoff r h (Evolution.timeCoord d x) * Ladj ψ x) :=
      ((hχ.continuous.comp (Evolution.timeCoord d).continuous).mul hLc
        ).integrable_of_hasCompactSupport hLcs.mul_left
    exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
  have i2 : Integrable (fun x => u (Qp x) * (h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h)
      * ψ x)) := by
    have hk : Continuous (fun x : EvolutionVec d =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      (continuous_const.mul (continuous_layerKernel.comp
        ((continuous_const.sub (Evolution.timeCoord d).continuous).div_const h))).mul hψ.continuous
    have : Integrable (fun x : EvolutionVec d =>
        h⁻¹ * layerKernel ((r - Evolution.timeCoord d x) / h) * ψ x) :=
      hk.integrable_of_hasCompactSupport hc.mul_left
    exact this.bdd_mul hmeasu.aestronglyMeasurable hbd
  exact (integral_add i1 i2).symm.trans key

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
