module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonOrder

/-! # A stopped terminal cap and earlier restart exits do not overlap -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Terminal occupation at `b` and any earlier exit subset together are bounded by the
actual stopped exit at `b`. The later recursion horizon `T` remains unchanged. -/
theorem enlarged_stripExit_cap_and_early_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (b T : ℝ) (hb : e.1.time < b) (hBT : b ≤ T)
    (B : Set Point) (hB : MeasurableSet B) (hsub : B ⊆ {p | p.time < b}) :
    (stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)).restrict
      {p | p.time = b} +
    (stripExit hH hLE hlam hLam A H T
      (stripPoleFinite H e T (hb.trans_le hBT))).restrict B ≤
        stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb) := by
  let E := stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)
  have hpre : MeasurableSet {p : Point | p.time < b} :=
    (isOpen_lt continuous_time continuous_const).measurableSet
  have he := stripExit_horizon_consistency hH hLE hlam hLam A H e
    T b (hb.trans_le hBT) hb b hBT le_rfl
  have heB := congrArg (fun rho : Measure Point => rho.restrict B) he
  simp only [Measure.restrict_restrict hB, inter_eq_left.mpr hsub] at heB
  rw [heB]
  have hd : Disjoint {p : Point | p.time = b} {p | p.time < b} := by
    apply Set.disjoint_left.mpr
    intro p hp ht
    exact (ne_of_lt ht) hp
  calc
    _ ≤ E.restrict {p | p.time = b} + E.restrict {p | p.time < b} :=
      add_le_add le_rfl (Measure.restrict_mono_set E hsub)
    _ = E.restrict ({p | p.time = b} ∪ {p | p.time < b}) :=
      (Measure.restrict_union hd hpre).symm
    _ ≤ E := Measure.restrict_le_self

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
