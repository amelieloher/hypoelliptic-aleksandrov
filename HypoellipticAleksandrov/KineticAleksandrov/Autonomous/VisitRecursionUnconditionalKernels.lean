module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursion
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBorel

/-! # Actual physical union kernels for alternating visits

Both kernels vanish outside the smaller open spacetime strip. Strict lower-time
support is retained when converting to the existing valid-pole carrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical

/-- The actual open spacetime carrier of an alternating visit. -/
def visitPoleSet (H : FiniteIntervalUnion) (s T : ℝ) : Set Point :=
  {p | s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier}

/-- The visit pole carrier is measurable in physical coordinates. -/
theorem measurableSet_visitPoleSet (H : FiniteIntervalUnion) (s T : ℝ) :
    MeasurableSet (visitPoleSet H s T) := by
  unfold visitPoleSet
  exact (isOpen_lt continuous_const continuous_time).measurableSet.inter
    ((isOpen_lt continuous_time continuous_const).measurableSet.inter
      (H.isOpen_carrier.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))

/-- A visit pole is a union pole; its strict lower-time condition is kept in the source type. -/
def visitPoleInclusion (H : FiniteIntervalUnion) (s T : ℝ)
    (p : visitPoleSet H s T) : FiniteUnionPole H (T : WithTop ℝ) :=
  ⟨p.1, WithTop.coe_lt_coe.mpr p.2.2.1, p.2.2.2⟩

/-- The physical inclusion preserves measurability. -/
theorem measurable_visitPoleInclusion (H : FiniteIntervalUnion) (s T : ℝ) :
    Measurable (visitPoleInclusion H s T) := measurable_subtype_coe.subtype_mk

/-- Extend a Borel measure family by zero outside its measurable physical pole carrier. -/
def visitExtendKernel (D : Set Point) (hD : MeasurableSet D)
    (f : D → Measure Point) (hf : Measurable f) : Kernel Point Point where
  toFun := fun p => if hp : p ∈ D then f ⟨p, hp⟩ else 0
  measurable' := Measurable.dite hf measurable_const hD

/-- Actual finite-union Green kernel, with zero extension beyond the open visit carrier. -/
def visitUnionGreenKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) :
    Kernel Point Point :=
  visitExtendKernel (visitPoleSet H s T) (measurableSet_visitPoleSet H s T)
    (fun p => finiteUnionGreen hH hLE hlam hLam A H T (visitPoleInclusion H s T p))
    ((finiteUnionGreen_measurable hH hLE hlam hLam A H T).comp
      (measurable_visitPoleInclusion H s T))

/-- Actual finite-union exit kernel, with zero extension beyond the open visit carrier. -/
def visitUnionExitKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) :
    Kernel Point Point :=
  visitExtendKernel (visitPoleSet H s T) (measurableSet_visitPoleSet H s T)
    (fun p => finiteUnionExit hH hLE hlam hLam A H T (visitPoleInclusion H s T p))
    ((finiteUnionExit_measurable hH hLE hlam hLam A H T).comp
      (measurable_visitPoleInclusion H s T))

/-- Uniform finiteness of the actual zero-extended exit kernel. -/
instance visitUnionExitKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) :
    IsFiniteKernel (visitUnionExitKernel hH hLE hlam hLam A H s T) := by
  refine ⟨1, by simp only [ENNReal.one_lt_top], ?_⟩
  intro p
  change (if hp : p ∈ visitPoleSet H s T then
    finiteUnionExit hH hLE hlam hLam A H T
      (visitPoleInclusion H s T ⟨p, hp⟩) else 0) univ ≤ 1
  split
  · simp only [measure_univ, le_refl]
  · exact zero_le

/-- The actual union Green measure has the same finite-time mass bound as its component. -/
theorem visitUnionGreen_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (p : FiniteUnionPole H (T : WithTop ℝ)) :
    finiteUnionGreen hH hLE hlam hLam A H T p univ ≤ ENNReal.ofReal (T - p.1.time) :=
  stripGreen_finite_time_mass hH hLE hlam hLam A _ T (finiteUnionComponentPole H T p)

/-- Every physical Green-kernel mass is bounded by the common strip time length. -/
theorem visitUnionGreenKernel_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) (p : Point) :
    visitUnionGreenKernel hH hLE hlam hLam A H s T p univ ≤
      ENNReal.ofReal (T - s) := by
  change (if hp : p ∈ visitPoleSet H s T then
    finiteUnionGreen hH hLE hlam hLam A H T
      (visitPoleInclusion H s T ⟨p, hp⟩) else 0) univ ≤ ENNReal.ofReal (T - s)
  split
  · rename_i hp
    apply (visitUnionGreen_mass_le hH hLE hlam hLam A H T
      (visitPoleInclusion H s T ⟨p, hp⟩)).trans
    apply ENNReal.ofReal_le_ofReal
    exact sub_le_sub_left hp.1.le T
  · exact zero_le

/-- The strict physical lower time gives a uniform finite bound on the Green kernel. -/
instance visitUnionGreenKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) :
    IsFiniteKernel (visitUnionGreenKernel hH hLE hlam hLam A H s T) :=
  ⟨ENNReal.ofReal (T - s), ENNReal.ofReal_lt_top,
    visitUnionGreenKernel_mass_le hH hLE hlam hLam A H s T⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
