module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesData
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesPairing

/-! # The boundary data as a continuous uniformly bounded L-infinity family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory Parabolic
open scoped ENNReal BoundedContinuousFunction

/-- The uniformly continuous compact data in centered exit coordinates. -/
theorem uniformContinuous_spatialBoundaryData {d : ℕ}
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hH : Continuous H)
    (hc : HasCompactSupport H) (P : KineticPoint d) (v₀ : PDE.Vec d) :
    UniformContinuous (H ∘ spatialBoundaryCoordinates P v₀) :=
  (hc.uniformContinuous_of_continuous hH).comp
    (uniformContinuous_spatialBoundaryCoordinates P v₀)

/-- The actual centered boundary data viewed in L-infinity of the exit-data marginal. -/
def spatialBoundaryLpData {d : ℕ}
    (μ : Measure (TimeVelocity d)) [IsFiniteMeasure μ]
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hH : Continuous H)
    (hc : HasCompactSupport H) (M : ℝ) (hb : ∀ q, ‖H q‖ ≤ M)
    (P : KineticPoint d) (v₀ : PDE.Vec d) (x : PDE.Vec d) : Lp ℝ ∞ μ :=
  BoundedContinuousFunction.toLp ∞ μ ℝ
    (spatialDataCurry (H ∘ spatialBoundaryCoordinates P v₀)
      (uniformContinuous_spatialBoundaryData H hH hc P v₀) M
      (fun _ => hb _) x)

/-- The centered L-infinity data are a continuous function of spatial displacement. -/
theorem continuous_spatialBoundaryLpData {d : ℕ}
    (μ : Measure (TimeVelocity d)) [IsFiniteMeasure μ]
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hH : Continuous H)
    (hc : HasCompactSupport H) (M : ℝ) (hb : ∀ q, ‖H q‖ ≤ M)
    (P : KineticPoint d) (v₀ : PDE.Vec d) :
    Continuous (spatialBoundaryLpData μ H hH hc M hb P v₀) :=
  (BoundedContinuousFunction.toLp ∞ μ ℝ).continuous.comp
    (continuous_spatialDataCurry _ (uniformContinuous_spatialBoundaryData H hH hc P v₀)
      M (fun _ => hb _))

/-- The data family is bounded by the local solution oscillation. -/
theorem spatialBoundaryLpData_norm_le {d : ℕ}
    (μ : Measure (TimeVelocity d)) [IsFiniteMeasure μ]
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hH : Continuous H)
    (hc : HasCompactSupport H) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, ‖H q‖ ≤ M)
    (P : KineticPoint d) (v₀ : PDE.Vec d) (x : PDE.Vec d) :
    ‖spatialBoundaryLpData μ H hH hc M hb P v₀ x‖ ≤ M :=
  (spatialData_toLp_norm_le μ _).trans
    (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM _)

/-- The data family has the literal centered boundary representative almost everywhere. -/
theorem spatialBoundaryLpData_coe {d : ℕ}
    (μ : Measure (TimeVelocity d)) [IsFiniteMeasure μ]
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hH : Continuous H)
    (hc : HasCompactSupport H) (M : ℝ) (hb : ∀ q, ‖H q‖ ≤ M)
    (P : KineticPoint d) (v₀ : PDE.Vec d) (x : PDE.Vec d) :
    (spatialBoundaryLpData μ H hH hc M hb P v₀ x : TimeVelocity d → ℝ) =ᵐ[μ]
      fun z => H (spatialBoundaryCoordinates P v₀ (x, z)) :=
  BoundedContinuousFunction.coeFn_toLp ∞ μ ℝ _

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
