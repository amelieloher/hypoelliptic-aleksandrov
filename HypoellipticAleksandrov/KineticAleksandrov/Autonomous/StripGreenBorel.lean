module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenHorizon

/-! # Borel dependence of the actual Green measure on its physical pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo
open scoped ENNReal ProbabilityTheory

private def infinitePoleQuery (H : Interval) (q : StripPole H ⊤ × ElapsedTime ⊤) :
    EvolutionQuery (intervalDomain H) (fun _ => 0) :=
  ⟨(q.1.1.time, (q.1.1.time + q.2.1, (q.1.1.velocity, q.1.1.position))),
    le_add_of_nonneg_right q.2.2.1.le, (stripPoleState H ⊤ q.1).2⟩

private theorem measurable_infinitePoleQuery (H : Interval) :
    Measurable (infinitePoleQuery H) := by
  have ht : Measurable (fun q : StripPole H ⊤ × ElapsedTime ⊤ => q.1.1.time) :=
    (continuous_time.measurable.comp measurable_subtype_coe).comp measurable_fst
  have hv : Measurable (fun q : StripPole H ⊤ × ElapsedTime ⊤ => q.1.1.velocity) :=
    (continuous_velocity.measurable.comp measurable_subtype_coe).comp measurable_fst
  have hx : Measurable (fun q : StripPole H ⊤ × ElapsedTime ⊤ => q.1.1.position) :=
    (continuous_position.measurable.comp measurable_subtype_coe).comp measurable_fst
  have hτ : Measurable (fun q : StripPole H ⊤ × ElapsedTime ⊤ => q.2.1) :=
    measurable_subtype_coe.comp measurable_snd
  apply Measurable.subtype_mk
  exact ht.prodMk ((ht.add hτ).prodMk (hv.prodMk hx))

/-- Set evaluations of the infinite-horizon measure are Borel in the actual valid pole. -/
theorem stripGreenOfKernel_infinite_measurable_apply (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (E : Set Point)
    (hE : MeasurableSet E) :
    Measurable (fun e : StripPole H ⊤ => stripGreenOfKernel H K ⊤ e E) := by
  let κ := K.master.comap (infinitePoleQuery H) (measurable_infinitePoleQuery H)
  have : ProbabilityTheory.IsFiniteKernel κ := by dsimp [κ]; infer_instance
  have ht : Measurable (fun q : (StripPole H ⊤ × ElapsedTime ⊤) × EvolutionAmbientState 1 =>
      q.1.1.1.time + q.1.2.1) :=
    ((continuous_time.measurable.comp measurable_subtype_coe).comp measurable_fst.fst).add
      (measurable_subtype_coe.comp measurable_fst.snd)
  have hp : Measurable (fun q : (StripPole H ⊤ × ElapsedTime ⊤) × EvolutionAmbientState 1 =>
      elapsedPhysicalPoint q.1.1.1.time (q.1.2, q.2)) :=
    (KineticPoint.measurable_equivProd_symm 1).comp
      (ht.prodMk (measurable_snd.snd.prodMk measurable_snd.fst))
  have hi0 : Measurable (fun q : StripPole H ⊤ × ElapsedTime ⊤ =>
      ∫⁻ w, E.indicator 1 (elapsedPhysicalPoint q.1.1.time (q.2, w)) ∂κ q) :=
    ((measurable_one.indicator hE).comp hp).lintegral_kernel_prod_right' (κ := κ)
  have hi : Measurable (fun e : StripPole H ⊤ =>
      ∫⁻ τ, ∫⁻ w, E.indicator 1 (elapsedPhysicalPoint e.1.time (τ, w))
        ∂κ (e, τ) ∂elapsedVolume ⊤) := hi0.lintegral_prod_right
  have he : (fun e : StripPole H ⊤ => stripGreenOfKernel H K ⊤ e E) =
      fun e => ∫⁻ τ, ∫⁻ w, E.indicator 1 (elapsedPhysicalPoint e.1.time (τ, w))
        ∂κ (e, τ) ∂elapsedVolume ⊤ := by
    funext e
    rw [← lintegral_indicator_one hE]
    exact stripGreenOfKernel_spec H K ⊤ e _ (measurable_one.indicator hE)
  rw [he]
  exact hi

/-- Every admitted terminal horizon gives Borel pole dependence, without invalid query branches. -/
theorem stripGreenOfKernel_measurable_apply (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : WithTop ℝ)
    (E : Set Point) (hE : MeasurableSet E) :
    Measurable (fun e : StripPole H T => stripGreenOfKernel H K T e E) := by
  cases T with
  | top => exact stripGreenOfKernel_infinite_measurable_apply H K E hE
  | coe t =>
    have hm : Measurable (stripPoleInfinite H t) := measurable_subtype_coe.subtype_mk
    have hEt : MeasurableSet (E ∩ {p : Point | p.time < t}) :=
      hE.inter (isOpen_Iio.preimage continuous_time).measurableSet
    have hi := (stripGreenOfKernel_infinite_measurable_apply H K _ hEt).comp hm
    have he : (fun e : StripPole H (t : WithTop ℝ) => stripGreenOfKernel H K t e E) =
        fun e => stripGreenOfKernel H K ⊤ (stripPoleInfinite H t e)
          (E ∩ {p | p.time < t}) := by
      funext e
      rw [stripGreenOfKernel_horizonRestriction, Measure.restrict_apply hE]
    rw [he]
    exact hi

/-- The unique autonomous killed family has the source-required Borel pole dependence. -/
theorem stripGreen_measurable_apply
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (E : Set Point) (hE : MeasurableSet E) :
    Measurable (fun e : StripPole H T => stripGreen hH hLE hlam hLam A H T e E) :=
  stripGreenOfKernel_measurable_apply H _ T E hE

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
