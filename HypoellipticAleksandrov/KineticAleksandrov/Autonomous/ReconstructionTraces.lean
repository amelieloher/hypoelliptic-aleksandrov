module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionSource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly

/-! # Boundary values and sequential traces of the actual reconstruction candidate

The candidate is phi minus the actual bounded-source Green potential. Boundary
values and limits are proved directly; no interior smoothness is asserted here.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA
open scoped Topology

/-- The actual pointwise difference used in homogeneous reconstruction. -/
def stripReconstructionCandidate (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  phi p - stripSourcePotential H K T g p

/-- The actual candidate equals its prescribed terminal/lateral exit value. -/
theorem stripReconstructionCandidate_eqOn_exit (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (sMinus T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point) :
    EqOn (stripReconstructionCandidate H K T phi g) phi
      (reconstructionExit H sMinus T) := by
  intro p hp
  have hz : stripSourcePotential H K T g p = 0 := by
    rcases hp with ht | hv
    · exact duhamelPotential_eq_zero_of_terminal_le K T (nativeStripSource g)
        (sectionTwoPoint p) (by change T ≤ p.time; exact ht.1.ge)
    · apply duhamelPotential_eq_zero_of_not_mem K T (nativeStripSource g)
        (sectionTwoPoint p)
      change p.velocity ∉ movingDomain (intervalDomain H) (fun _ => 0) p.time
      rw [movingDomain, PDE.mem_translateSet_iff_sub_mem, sub_zero]
      rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
      change p.velocity 0 ∉ Set.Ioo H.lo H.hi
      rcases hv.2.2 with hl | hh
      · rw [hl]
        exact fun h => (lt_irrefl H.lo) h.1
      · rw [hh]
        exact fun h => (lt_irrefl H.hi) h.2
  change phi p - stripSourcePotential H K T g p = phi p
  rw [hz, sub_zero]

/-- Along poles tending to the terminal face the candidate has the prescribed limit. -/
theorem stripReconstructionCandidate_terminal_tendsto (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point)
    (e : ℕ → StripPole H (T : WithTop ℝ)) (L : ℝ)
    (ht : Tendsto (fun n => (e n).1.time) atTop (𝓝 T))
    (hphi : Tendsto (fun n => phi (e n).1) atTop (𝓝 L)) :
    Tendsto (fun n => stripReconstructionCandidate H K T phi g (e n).1)
      atTop (𝓝 L) := by
  simpa only [stripReconstructionCandidate, sub_zero] using
    hphi.sub (stripSourcePotential_terminal_tendsto H K T g e ht)

/-- At either velocity face the candidate has the prescribed limit. -/
theorem stripReconstructionCandidate_velocity_tendsto
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (phi : Point → ℝ) (g : BoundedBorel Point)
    (e : ℕ → StripPole H (T : WithTop ℝ)) (v L : ℝ) (hv : v = H.lo ∨ v = H.hi)
    (he : Tendsto (fun n => (e n).1.velocity 0) atTop (𝓝 v))
    (hphi : Tendsto (fun n => phi (e n).1) atTop (𝓝 L)) :
    Tendsto (fun n => stripReconstructionCandidate H E.2 T phi g (e n).1)
      atTop (𝓝 L) := by
  simpa only [stripReconstructionCandidate, sub_zero] using
    hphi.sub (stripSourcePotential_velocityFace_tendsto hH hlam hLam A H E hE T g e v hv he)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
