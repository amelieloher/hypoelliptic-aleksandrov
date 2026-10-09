module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalRestart

/-! # Exact terminal, outer-lateral and internal-lateral interval exit splitting -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The literal interval exit boundary is Borel in physical coordinates. -/
theorem measurableSet_nestedIntervalExit (H : Interval) (sMinus T : ℝ) :
    MeasurableSet (reconstructionExit H sMinus T) := by
  have hv : Measurable (fun p : Point => p.velocity 0) :=
    ((continuous_apply 0).comp continuous_velocity).measurable
  exact ((measurableSet_eq_fun continuous_time.measurable measurable_const).inter
    (measurableSet_Icc.preimage hv)).union
    ((measurableSet_lt measurable_const continuous_time.measurable).inter
      ((measurableSet_lt continuous_time.measurable measurable_const).inter
        ((measurableSet_eq_fun hv measurable_const).union
          (measurableSet_eq_fun hv measurable_const))))

/-- On a smaller interval exit, being outside the larger exit is exactly being internal. -/
theorem nestedIntervalExit_compl_iff_internal (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ) (p : Point)
    (hp : p ∈ reconstructionExit H1 sMinus T) :
    p ∉ reconstructionExit H2 sMinus T ↔ p ∈ nestedIntervalInternalExit H1 H2 sMinus T := by
  have hc := nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T (Or.inr hp)
  constructor
  · intro hn
    rcases hp with hp | hp
    · exact False.elim (hn (Or.inl ⟨hp.1, hc.2⟩))
    · refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
      change H2.lo < p.velocity 0 ∧ p.velocity 0 < H2.hi
      have hl : p.velocity 0 ≠ H2.lo := fun hl => hn (Or.inr ⟨hp.1, hp.2.1, Or.inl hl⟩)
      have hh : p.velocity 0 ≠ H2.hi := fun hh => hn (Or.inr ⟨hp.1, hp.2.1, Or.inr hh⟩)
      exact ⟨lt_of_le_of_ne hc.2.1 hl.symm, lt_of_le_of_ne hc.2.2 hh⟩
  · intro hs hn
    rcases hn with hn | hn
    · exact (ne_of_lt hs.2.1) hn.1
    · rcases hn.2.2 with hv | hv
      · exact (ne_of_gt hs.2.2.2.1) hv
      · exact (ne_of_lt hs.2.2.2.2) hv

/-- With strict open-strip pole support the actual smaller exit splits into outer and internal
  exits. -/
theorem nestedIntervalExit_boundary_split
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    stripExit hH hLE hlam hLam A H1 T e =
      (stripExit hH hLE hlam hLam A H1 T e).restrict (reconstructionExit H2 sMinus T) +
      (stripExit hH hLE hlam hLam A H1 T e).restrict
        (nestedIntervalInternalExit H1 H2 sMinus T) := by
  let μ := stripExit hH hLE hlam hLam A H1 T e
  have hm : ∀ᵐ p ∂μ, p ∈ reconstructionExit H1 sMinus T := by
    rw [ae_iff]
    exact (strip_exit_probability hH hLE hlam hLam A H1 sMinus T e he.le).2.1
  have heq : (reconstructionExit H2 sMinus T)ᶜ =ᵐ[μ]
      nestedIntervalInternalExit H1 H2 sMinus T := by
    filter_upwards [hm] with p hp
    exact propext (nestedIntervalExit_compl_iff_internal H1 H2 hsub sMinus T p hp)
  have hs := μ.restrict_add_restrict_compl (measurableSet_nestedIntervalExit H2 sMinus T)
  rw [Measure.restrict_congr_set heq] at hs
  exact hs.symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
