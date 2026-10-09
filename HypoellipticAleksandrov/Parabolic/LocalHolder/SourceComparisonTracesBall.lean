module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTraces
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBallBarrier

/-! # Continuous zero extensions of corrections on closed balls

Both uniform envelopes give continuity at the true boundary. A time collar includes
the lower closed face among the interior points of the constructed correction.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set
open scoped Topology

/-- The spatial barrier gives ambient continuity of the zero extension at lateral points. -/
theorem continuousAt_source_zeroExtension_lateral {d : ℕ}
    (a T : ℝ) (v₀ : PDE.Vec d) (r lam M : ℝ) (w : TimeVelocity d → ℝ)
    (hb : ∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
      |w z| ≤ sourceBallBarrier v₀ r lam M z.2)
    (p : TimeVelocity d) (hp : p.2 ∈ frontier (PDE.euclideanBall v₀ r)) :
    ContinuousAt (sourceInteriorZeroExtension a T (PDE.euclideanBall v₀ r) w) p := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  let U := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension a T Ω w
  have hpo : p.2 ∉ Ω := by
    rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq] at hp
    exact hp.2
  have hpW : W p = 0 := by
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hpo h.2)
  have hbW (z : TimeVelocity d) : ‖W z‖ ≤ |sourceBallBarrier v₀ r lam M z.2| := by
    by_cases hz : z ∈ U
    · rw [show W z = w z from piecewise_eq_of_mem U w (fun _ => 0) hz,
        Real.norm_eq_abs]
      exact (hb z hz).trans (le_abs_self _)
    · rw [show W z = 0 from piecewise_eq_of_notMem U w (fun _ => 0) hz, norm_zero]
      exact abs_nonneg _
  have hc : Continuous (fun z : TimeVelocity d => |sourceBallBarrier v₀ r lam M z.2|) :=
    ((contDiff_sourceBallBarrier v₀ r lam M).continuous.comp continuous_snd).abs
  have hz : Tendsto (fun z : TimeVelocity d => |sourceBallBarrier v₀ r lam M z.2|)
      (𝓝 p) (𝓝 0) := by
    simpa only [sourceBallBarrier_zero_frontier v₀ r lam M hp, abs_zero] using
      (hc.continuousAt (x := p)).tendsto
  change Tendsto W (𝓝 p) (𝓝 (W p))
  rw [hpW]
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) hbW hz)

/-- A time collar and both envelopes give continuity on the entire closed cylinder. -/
theorem continuousOn_source_zeroExtension_closed_ball {d : ℕ}
    (a₀ a T : ℝ) (ha : a₀ < a) (v₀ : PDE.Vec d) (r lam M : ℝ)
    (hM : 0 ≤ M) (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r)))
    (ht : ∀ z ∈ scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r),
      |w z| ≤ M * (T - z.1))
    (hs : ∀ z ∈ scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r),
      |w z| ≤ sourceBallBarrier v₀ r lam M z.2) :
    ContinuousOn (sourceInteriorZeroExtension a₀ T (PDE.euclideanBall v₀ r) w)
      (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r)) := by
  classical
  intro p hp
  by_cases hpt : p.1 = T
  · exact (continuousWithinAt_source_zeroExtension_terminal a₀ T M hM w ht p hpt).mono
      (prod_mono (Icc_subset_Icc ha.le le_rfl) (Subset.refl _))
  · by_cases hpy : p.2 ∈ PDE.euclideanBall v₀ r
    · let U := scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r)
      have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ r)
      have hpu : p ∈ U := ⟨⟨lt_of_lt_of_le ha hp.1.1,
        lt_of_le_of_ne hp.1.2 hpt⟩, hpy⟩
      have he : sourceInteriorZeroExtension a₀ T (PDE.euclideanBall v₀ r) w =ᶠ[𝓝 p] w := by
        filter_upwards [hU.mem_nhds hpu] with z hz
        exact piecewise_eq_of_mem U w (fun _ => 0) hz
      exact ((hw.continuousAt (hU.mem_nhds hpu)).congr_of_eventuallyEq he).continuousWithinAt
    · have hpf : p.2 ∈ frontier (PDE.euclideanBall v₀ r) := by
        rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq]
        exact ⟨hp.2, hpy⟩
      have hc := continuousAt_source_zeroExtension_lateral a₀ T v₀ r lam M w hs p hpf
      exact hc.continuousWithinAt

end HypoellipticAleksandrov.Parabolic.LocalHolder
