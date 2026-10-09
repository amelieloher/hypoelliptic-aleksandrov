module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationProduct

/-! # The cutoff transport speed in the actual free-transport frame -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Parabolic
open scoped Topology

/-- The multiplier on the literal time-position carrier. -/
def localPositionMultiplier {d : ℕ} (Z₀ : KineticPoint d) (χ : PDE.Vec d → ℝ)
    (z : TimeVelocity d) : ℝ := χ (z.2 - Z₀.position - (z.1 - Z₀.time) • Z₀.velocity)

/-- The free-transport defect is the cutoff differential applied to relative velocity. -/
def localCutoffTransport {d : ℕ} (Z₀ : KineticPoint d) (χ : PDE.Vec d → ℝ)
    (P : KineticPoint d) : ℝ :=
  fderiv ℝ χ (relativePosition Z₀ P) (P.velocity - Z₀.velocity)

/-- The time-position multiplier is globally smooth. -/
theorem contDiff_localPositionMultiplier {d : ℕ} (Z₀ : KineticPoint d)
    {χ : PDE.Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞) (localPositionMultiplier Z₀ χ) :=
  hχ.comp ((contDiff_snd.sub contDiff_const).sub
    ((contDiff_fst.sub contDiff_const).smul contDiff_const))

/-- The cutoff transport defect is continuous on the full physical carrier. -/
theorem continuous_localCutoffTransport {d : ℕ} (Z₀ : KineticPoint d)
    {χ : PDE.Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (localCutoffTransport Z₀ χ) := by
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  exact ((hχ.continuous_fderiv (by simp)).comp hrel).clm_apply
    (continuous_velocity.sub continuous_const)

/-- Outside the cutoff support there is no transport defect. -/
theorem localCutoffTransport_zero {d : ℕ} (Z₀ P : KineticPoint d)
    (χ : PDE.Vec d → ℝ) (hx : relativePosition Z₀ P ∉ tsupport χ) :
    localCutoffTransport Z₀ χ P = 0 := by
  rw [localCutoffTransport, fderiv_of_notMem_tsupport ℝ hx, zero_apply]

/-- The two coordinate transport terms equal the differential on relative velocity. -/
theorem localPositionMultiplier_transport {d : ℕ} (Z₀ P : KineticPoint d)
    {χ : PDE.Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    scalarTimeDerivative (localPositionMultiplier Z₀ χ) (P.time, P.position) +
      PDE.vecDot P.velocity
        (scalarSpatialGradient (localPositionMultiplier Z₀ χ) (P.time, P.position)) =
      localCutoffTransport Z₀ χ P := by
  have hd := hχ.differentiable (by norm_num)
  have ht : HasDerivAt
      (fun t : ℝ => P.position - Z₀.position - (t - Z₀.time) • Z₀.velocity)
      (-Z₀.velocity) P.time := by
    convert (hasDerivAt_const P.time (P.position - Z₀.position)).sub
      (((hasDerivAt_id P.time).sub_const Z₀.time).smul_const Z₀.velocity) using 1
    · funext t
      rfl
    · simp only [zero_sub, one_smul]
  have htime := (hd (relativePosition Z₀ P)).hasFDerivAt.comp_hasDerivAt P.time ht
  have hspace := (hd (relativePosition Z₀ P)).hasFDerivAt.comp P.position
    (((hasFDerivAt_id P.position).sub_const Z₀.position).sub_const
      ((P.time - Z₀.time) • Z₀.velocity))
  have hte : scalarTimeDerivative (localPositionMultiplier Z₀ χ) (P.time, P.position) =
      fderiv ℝ χ (relativePosition Z₀ P) (-Z₀.velocity) := htime.deriv
  have hxe : scalarSpatialGradient (localPositionMultiplier Z₀ χ) (P.time, P.position) =
      PDE.classicalGradient χ (relativePosition Z₀ P) := by
    ext i
    change fderiv ℝ (fun x => χ (x - Z₀.position -
      (P.time - Z₀.time) • Z₀.velocity)) P.position (PDE.basisVec i) = _
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, PDE.classicalGradient_apply] using
      congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L (PDE.basisVec i)) hspace.fderiv
  rw [hte, hxe, PDE.vecDot_comm]
  change fderiv ℝ χ (relativePosition Z₀ P) (-Z₀.velocity) +
    PDE.vecDot (fun i => fderiv ℝ χ (relativePosition Z₀ P) (PDE.basisVec i))
      P.velocity = _
  rw [← PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues]
  simp only [localCutoffTransport, map_neg, map_sub]
  ring

/-- The exact local cutoff residual, at a point where the original solution is classical. -/
theorem localCutoffSolution_operator {d : ℕ} (Z₀ : KineticPoint d)
    (A : FullKineticCoefficient d) {χ : PDE.Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (hu : IsKineticC112On u D) {P : KineticPoint d} (hP : P ∈ D) :
    forwardKineticOperator A (localCutoffSolution Z₀ χ u) P =
      localPositionCutoff Z₀ χ P * forwardKineticOperator A u P +
        localCutoffTransport Z₀ χ P * u P := by
  have h := forward_operator_position_multiplier A (localPositionMultiplier Z₀ χ)
    (contDiff_localPositionMultiplier Z₀ hχ) hu hP
  rw [localPositionMultiplier_transport Z₀ P hχ] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
