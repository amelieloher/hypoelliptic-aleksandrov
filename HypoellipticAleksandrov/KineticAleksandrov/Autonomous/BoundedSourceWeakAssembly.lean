module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsQuadratic

/-! # Actual physical bounded-source potentials, weak forcing, and zero boundary limits

All source integrals use the unique killed Green measure. The only external hypotheses
of the canonical construction are the evolution inputs. No regularity of a Borel
source potential is asserted.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- Exchange physical position and velocity in a bounded Borel source. -/
def nativeStripSource (g : BoundedBorel Point) : BoundedBorel Point :=
  ⟨g ∘ sectionTwoPoint, g.measurable.comp (continuous_sectionTwoPoint 1).measurable, by
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun p => hg _⟩⟩

/-- The physical source potential is the actual Duhamel potential in native coordinates. -/
def stripSourcePotential (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  duhamelPotential K T (nativeStripSource g) (sectionTwoPoint p)

/-- Every valid physical pole has the actual signed bounded-source Green representation. -/
theorem stripSourcePotential_eq_green (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ)) :
    stripSourcePotential H K T g e.1 = stripPotentialOfKernel H K T g e := by
  have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
  have hh := duhamelPotential_eq_green_bounded H K T (nativeStripSource g)
    e.1.time heT (stripPoleState H T e)
    (greenMeasure K e.1.time _ (stripHorizon_pos H T e) _)
    (greenMeasure_spec K _ _ _ _)
  rw [stripPotentialOfKernel, stripGreenOfKernel,
    integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
      (show AEStronglyMeasurable (fun p : Point => g p) _ from
        g.measurable.aestronglyMeasurable)]
  exact hh

/-- Exchanging physical coordinates converts the actual source potential to native weak forcing. -/
theorem stripSourcePotential_weak {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (T : ℝ) (g : BoundedBorel Point) :
    IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
      (stripSourcePotential H E.2 T g ∘ sectionTwoPoint)
      (fun p => -nativeStripSource g p) := by
  have heq : (stripSourcePotential H E.2 T g ∘ sectionTwoPoint) =
      duhamelPotential E.2 T (nativeStripSource g) := by
    funext p
    change duhamelPotential E.2 T (nativeStripSource g)
      (sectionTwoPoint (sectionTwoPoint p)) = _
    rw [sectionTwoPoint_involutive p]
  rw [heq]
  exact strip_duhamel_weak A H E hE T (nativeStripSource g)

/-- The canonical autonomous bounded-source construction has weak forcing and the Green identity
on the same unique killed realization. Sources need only be bounded Borel. -/
theorem strip_bounded_source_weak
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ) (g : BoundedBorel Point) :
    let E := stripEvolution hH hLE hlam hLam A H
    IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
      (stripSourcePotential H E.2 T g ∘ sectionTwoPoint)
      (fun p => -nativeStripSource g p) ∧
    ∀ e : StripPole H (T : WithTop ℝ),
      stripSourcePotential H E.2 T g e.1 = ∫ p, g p ∂stripGreen hH hLE hlam hLam A H T e :=
  ⟨stripSourcePotential_weak A H _ (stripEvolution_spec hH hLE hlam hLam A H) T g,
    fun e => stripSourcePotential_eq_green H _ T g e⟩

/-- The actual bounded-source potential has zero terminal-time limit, uniformly in spatial data. -/
theorem stripSourcePotential_terminal_tendsto (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : ℕ → StripPole H (T : WithTop ℝ))
    (he : Tendsto (fun n => (e n).1.time) atTop (𝓝 T)) :
    Tendsto (fun n => stripSourcePotential H K T g (e n).1) atTop (𝓝 0) := by
  simpa only [stripSourcePotential_eq_green] using
    stripPotentialOfKernel_terminal_tendsto H K T g e he

/-- The actual potential has zero limit at either velocity face, uniformly in time and position. -/
theorem stripSourcePotential_velocityFace_tendsto
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (g : BoundedBorel Point)
    (e : ℕ → StripPole H (T : WithTop ℝ)) (v : ℝ) (hv : v = H.lo ∨ v = H.hi)
    (he : Tendsto (fun n => (e n).1.velocity 0) atTop (𝓝 v)) :
    Tendsto (fun n => stripSourcePotential H E.2 T g (e n).1) atTop (𝓝 0) := by
  simpa only [stripSourcePotential_eq_green] using
    stripPotentialOfRealization_velocityFace_tendsto hH hlam hLam A H E hE T g e v hv he

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
