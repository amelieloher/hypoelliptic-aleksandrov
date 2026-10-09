module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFunctions
import Mathlib.Topology.MetricSpace.Thickening

/-! # The fixed full boundary is preserved by sufficiently small spatial kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter
open scoped Topology

/-- A single positive collar works for every flattening scale and every time. -/
theorem construction_exists_smoothing_collar {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (T S : ℝ)
    (hS : 0 < S) (hTS : T < S ^ 2)
    (hgeom : ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r mu R : ℝ) (phi : ContDiffBump (0 : XV d)),
      phi.rOut < delta → ∀ P : KineticPoint d,
      P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S →
      smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  let box : Set (XV d) := {q | PDE.vecNormSq q.1 < (S ^ 3) ^ 2 ∧
    PDE.vecNormSq q.2 < S ^ 2}
  have ho : IsOpen box :=
    (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp continuous_fst) continuous_const).inter
      (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp continuous_snd) continuous_const)
  have hsub : {q | profileFunction h q ≤ 1} ⊆ box := by
    intro q hq
    have hh := hgeom q hq
    have hx := PDE.vecEuclideanNorm_nonneg q.1
    have hv := PDE.vecEuclideanNorm_nonneg q.2
    have hs3 := pow_pos hS 3
    change PDE.vecNormSq q.1 < (S ^ 3) ^ 2 ∧ PDE.vecNormSq q.2 < S ^ 2
    rw [← PDE.vecEuclideanNorm_sq, ← PDE.vecEuclideanNorm_sq]
    constructor <;> nlinarith
  have hK := isCompact_profile_unit_sublevel ha h
  obtain ⟨delta, hd, hb⟩ := hK.exists_thickening_subset_open ho hsub
  refine ⟨delta, hd, ?_⟩
  intro r mu R phi hphi P hP
  have hfaces : P.time = T - S ^ 2 ∨
      P.velocity ∈ PDE.euclideanSphere 0 S ∨
      P.position ∈ PDE.euclideanSphere 0 (S ^ 3) := by
    simpa only [relativePosition, sub_zero, smul_zero,
      mem_union, mem_ofPred_eq, or_assoc] using hP.2
  rcases hfaces with ht | hv | hx
  · apply smoothedZeroExtendedProfile_eq_zero_of_time
    change P.time = T - S ^ 2 at ht
    linarith
  · apply smoothedZeroExtendedProfile_eq_zero_outside_thickening
    intro hq
    have hh := hb (Metric.thickening_mono hphi.le _ hq)
    have he : PDE.vecNormSq P.velocity = S ^ 2 := by
      simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, sub_zero, mem_ofPred_eq] using hv
    exact (ne_of_lt hh.2) he
  · apply smoothedZeroExtendedProfile_eq_zero_outside_thickening
    intro hq
    have hh := hb (Metric.thickening_mono hphi.le _ hq)
    have he : PDE.vecNormSq P.position = (S ^ 3) ^ 2 := by
      simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, sub_zero, mem_ofPred_eq] using hx
    exact (ne_of_lt hh.1) he

/-- Every sufficiently late concrete mollifier preserves the complete boundary. -/
theorem construction_smoothed_boundary_eventually {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (T S : ℝ)
    (hS : 0 < S) (hTS : T < S ^ 2)
    (hgeom : ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S)
    (r mu R : ℝ) :
    ∀ᶠ n in atTop, ∀ P : KineticPoint d,
      P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S →
      smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n) P = 0 := by
  obtain ⟨delta, hd, hb⟩ := construction_exists_smoothing_collar ha h T S hS hTS hgeom
  have hr := standardMollifierSequence_rOut_tendsto (G := XV d)
  filter_upwards [hr.eventually (Iio_mem_nhds hd)] with n hn
  exact hb r mu R (standardMollifierSequence n) hn

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
