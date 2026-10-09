module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMonotone

/-! # Joint domain and horizon monotonicity for the actual Green family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Enlarge the velocity carrier and terminal horizon without changing the physical pole. -/
def stripEnlargePole (H1 H2 : Interval) (hsub : H1.carrier ⊆ H2.carrier)
    (T1 T2 : WithTop ℝ) (hT : T1 ≤ T2) (e : StripPole H1 T1) : StripPole H2 T2 :=
  ⟨e.1, e.2.1.trans_le hT, hsub e.2.2⟩

/-- The actual Green measure increases jointly with its domain and terminal horizon. -/
theorem stripGreen_mono
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (T1 T2 : WithTop ℝ) (hT : T1 ≤ T2)
    (e : StripPole H1 T1) :
    stripGreen hH hLE hlam hLam A H1 T1 e ≤
      stripGreen hH hLE hlam hLam A H2 T2 (stripEnlargePole H1 H2 hsub T1 T2 hT e) := by
  let ei : StripPole H1 ⊤ := ⟨e.1, WithTop.coe_lt_top _, e.2.2⟩
  have hd := stripGreen_domain_mono_infinite hH hLE hlam hLam A H1 H2 hsub ei
  cases T1 with
  | top =>
    have he : T2 = ⊤ := top_le_iff.mp hT
    subst T2
    exact hd
  | coe t1 =>
    have ht1 : e.1.time < t1 := WithTop.coe_lt_coe.mp e.2.1
    have h1 := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H1 ei t1 ht1
    have hp1 : stripPoleFinite H1 ei t1 ht1 = e := Subtype.ext rfl
    have h1' := (congrArg (stripGreen hH hLE hlam hLam A H1 t1) hp1).symm.trans h1
    apply h1' ▸ le_trans (Measure.restrict_mono_measure hd _)
    cases T2 with
    | top => exact Measure.restrict_le_self
    | coe t2 =>
      have ht12 : t1 ≤ t2 := WithTop.coe_le_coe.mp hT
      have ht2 : e.1.time < t2 := ht1.trans_le ht12
      have h2 := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H2
        (nestedPoleInclusion H1 H2 hsub ⊤ ei) t2 ht2
      have hp2 : stripPoleFinite H2 (nestedPoleInclusion H1 H2 hsub ⊤ ei) t2 ht2 =
          stripEnlargePole H1 H2 hsub t1 t2 hT e := Subtype.ext rfl
      have h2' :=
        (congrArg (stripGreen hH hLE hlam hLam A H2 t2) hp2).symm.trans h2
      exact h2'.symm ▸ Measure.restrict_mono_set _ (fun p hp => hp.trans_le ht12)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
