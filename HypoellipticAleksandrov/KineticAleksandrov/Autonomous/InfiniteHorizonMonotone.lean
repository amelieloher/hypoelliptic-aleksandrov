module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen

/-! # Actual domain monotonicity at finite and infinite horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual finite Green measure increases when the velocity interval is enlarged. -/
theorem stripGreen_domain_mono_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (T : ℝ) (e : StripPole H1 (T : WithTop ℝ)) :
    stripGreen hH hLE hlam hLam A H1 T e ≤
      stripGreen hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T e) := by
  have h := nestedIntervalGreen_identity hH hLE hlam hLam A H1 H2 hsub
    (e.1.time - 1) T e (by linarith)
  apply Measure.le_iff.mpr
  intro B _
  have hh := congrArg (fun μ : Measure Point => μ B) h
  exact hh.symm ▸ le_add_right le_rfl

/-- Domain monotonicity survives the genuine increasing-limit construction of infinite Green. -/
theorem stripGreen_domain_mono_infinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (e : StripPole H1 ⊤) :
    stripGreen hH hLE hlam hLam A H1 ⊤ e ≤
      stripGreen hH hLE hlam hLam A H2 ⊤ (nestedPoleInclusion H1 H2 hsub ⊤ e) := by
  rw [stripGreen_infinite_eq_iSup hH hLE hlam hLam A H1 e]
  apply iSup_le
  intro T
  apply iSup_le
  intro ht
  have h := stripGreen_domain_mono_finite hH hLE hlam hLam A H1 H2 hsub T
    (stripPoleFinite H1 e T ht)
  have hfinite : nestedPoleInclusion H1 H2 hsub T (stripPoleFinite H1 e T ht) =
      stripPoleFinite H2 (nestedPoleInclusion H1 H2 hsub ⊤ e) T ht := by
    apply Subtype.ext
    rfl
  have hinc := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H2
    (nestedPoleInclusion H1 H2 hsub ⊤ e) T ht
  have heq := congrArg (stripGreen hH hLE hlam hLam A H2 T) hfinite
  exact h.trans (heq ▸ hinc.symm ▸ Measure.restrict_le_self)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
