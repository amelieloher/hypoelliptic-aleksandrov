module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures

/-! # Actual internal-exit restart measure and its restored starting-strip support -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Include a smaller-union pole into the larger union at the identical physical point. -/
def finiteUnionNestedPoleInclusion (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (T : WithTop ℝ)
    (e : FiniteUnionPole H1 T) : FiniteUnionPole H2 T :=
  ⟨e.1, e.2.1, hsub e.2.2⟩

/-- The pole inclusion is Borel; it does not alter time, position or velocity. -/
theorem measurable_finiteUnionNestedPoleInclusion (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (T : WithTop ℝ) :
    Measurable (finiteUnionNestedPoleInclusion H1 H2 hsub T) :=
  measurable_subtype_coe.subtype_mk

/-- The internal restart measure is precisely the actual smaller exit restricted to Sigma. -/
def finiteUnionRestartMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) : Measure Point :=
  (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
    (finiteUnionInternalExit H1 H2 sMinus T)

/-- Internal restart measures of finite sources are finite. -/
instance finiteUnionRestartMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu) := by
  unfold finiteUnionRestartMeasure
  infer_instance

/-- The source-supported smaller exit splits exactly into outer exits and actual restarts. -/
theorem finiteUnionExitMixture_boundary_split
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ)))
    (hnu : ∀ᵐ e ∂nu, sMinus < e.1.time) :
    finiteUnionExitMixture hH hLE hlam hLam A H1 T nu =
      (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
        (finiteUnionExitSet H2 sMinus T) +
      finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu := by
  let μ := finiteUnionExitMixture hH hLE hlam hLam A H1 T nu
  have hm : ∀ᵐ p ∂μ, p ∈ finiteUnionExitSet H1 sMinus T := by
    rw [ae_iff]
    exact finiteUnionExitMixture_compl_exit hH hLE hlam hLam A H1 sMinus T nu hnu
  have heq : (finiteUnionExitSet H2 sMinus T)ᶜ =ᵐ[μ]
      finiteUnionInternalExit H1 H2 sMinus T := by
    filter_upwards [hm] with p hp
    apply propext
    constructor
    · intro hn
      have hs := (congrArg (fun S : Set Point => p ∈ S)
        (finiteUnionExitSet_nested_split H1 H2 hsub sMinus T)).mp hp
      rcases hs with hs | hs
      · exact False.elim (hn hs.2)
      · exact hs
    · intro hs hn
      exact Set.disjoint_left.mp
        (finiteUnionExitSet_disjoint_internal H1 H2 sMinus T) hn hs
  have hs := μ.restrict_add_restrict_compl
    (measurableSet_finiteUnionExitSet H2 sMinus T)
  rw [Measure.restrict_congr_set heq] at hs
  exact hs.symm

/-- Every restart occurs strictly after the common lower time and inside the larger velocity set. -/
theorem finiteUnionRestartMeasure_ae_valid
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    ∀ᵐ p ∂finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu,
      sMinus < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H2.carrier := by
  unfold finiteUnionRestartMeasure
  filter_upwards [ae_restrict_mem
    (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)] with p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
