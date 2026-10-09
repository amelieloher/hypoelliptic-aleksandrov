module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform Hessian signs on the fixed cutoff annulus

Compactness is applied to the actual differentiated interpolation, with the two
perturbation parameters tending to zero independently.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The velocity Hessian quadratic form of the rescaled interpolation. -/
def rescaledHessian {d : ℕ} (alpha sigma s t : ℝ) (e z w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun a => fderiv ℝ (rescaledCutoff alpha sigma s t e) a w) z w

/-- The fixed compact annulus and Euclidean unit direction parameter. -/
def cutoffAnnulus (d : ℕ) : Set (PDE.Vec d × PDE.Vec d) :=
  {q | PDE.vecNormSq q.1 = 1 ∧ 1 ≤ PDE.vecEuclideanNorm q.2 ∧
    PDE.vecEuclideanNorm q.2 ≤ 2}

/-- The fixed annulus is compact in the native product topology. -/
theorem isCompact_cutoffAnnulus (d : ℕ) : IsCompact (cutoffAnnulus d) := by
  have hclosed : IsClosed (cutoffAnnulus d) := by
    exact (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_fst) continuous_const).inter
      ((isClosed_le continuous_const (PDE.continuous_vecEuclideanNorm.comp continuous_snd)).inter
        (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_snd) continuous_const))
  apply (isCompact_closedBall (0 : PDE.Vec d × PDE.Vec d) 2).of_isClosed_subset hclosed
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have he : PDE.vecEuclideanNorm q.1 = 1 := by
    unfold PDE.vecEuclideanNorm
    rw [hq.1]
    norm_num
  exact max_le ((PDE.norm_le_vecEuclideanNorm _).trans (by linarith))
    ((PDE.norm_le_vecEuclideanNorm _).trans hq.2.2)

/-- The open regular region with positive and negative velocity Hessian directions. -/
def rescaledSignRegion (d : ℕ) (alpha sigma : ℝ) :
    Set ((PDE.Vec d × PDE.Vec d) × (ℝ × ℝ)) :=
  {q | q.1.2 ≠ 0 ∧ seedBase (q.2.2 * sigma) q.1.2 (q.2.2 • q.1.1) ≠ 0 ∧
    (∃ w, 0 < rescaledHessian alpha sigma q.2.1 q.2.2 q.1.1 q.1.2 w) ∧
    (∃ w, rescaledHessian alpha sigma q.2.1 q.2.2 q.1.1 q.1.2 w < 0)}

/-- Both strict Hessian signs persist locally in the regular parameter region. -/
theorem isOpen_rescaledSignRegion (d : ℕ) (alpha sigma : ℝ) :
    IsOpen (rescaledSignRegion d alpha sigma) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨hz, hb, ⟨wp, hp⟩, ⟨wn, hn⟩⟩ := hq
  have hc : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) =>
      ((p.2.1, p.2.2, p.1.1), p.1.2)) := by fun_prop
  have hpos := (continuousAt_rescaledCutoff_hessian alpha sigma
    ((q.2.1, q.2.2, q.1.1), q.1.2) hz hb wp wp).comp_of_eq hc.continuousAt rfl
  have hneg := (continuousAt_rescaledCutoff_hessian alpha sigma
    ((q.2.1, q.2.2, q.1.1), q.1.2) hz hb wn wn).comp_of_eq hc.continuousAt rfl
  have hbase : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) =>
      seedBase (p.2.2 * sigma) p.1.2 (p.2.2 • p.1.1)) := by
    unfold seedBase PDE.vecNormSq PDE.vecDot
    fun_prop
  have hvel : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) => p.1.2) := by
    fun_prop
  filter_upwards [hvel.continuousAt.eventually_ne hz, hbase.continuousAt.eventually_ne hb,
    hpos.eventually_const_lt hp, hneg.eventually_lt_const hn] with p hpz hpb hpp hpn
  exact ⟨hpz, hpb, ⟨wp, hpp⟩, ⟨wn, hpn⟩⟩

/-- At zero parameters the actual interpolation has the two radial Hessian signs. -/
theorem cutoffAnnulus_zero_signs (d : ℕ) (hd : 2 ≤ d) (alpha sigma : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    cutoffAnnulus d ×ˢ ({(0, 0)} : Set (ℝ × ℝ)) ⊆ rescaledSignRegion d alpha sigma := by
  rintro ⟨⟨e, z⟩, p⟩ ⟨hz, hp⟩
  have hp0 : p = (0, 0) := Set.mem_singleton_iff.mp hp
  subst p
  have hz0 : z ≠ 0 := by
    intro hzero
    have hh := hz.2.1
    simp [hzero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] at hh
    norm_num at hh
  have hbase : seedBase (0 * sigma) z ((0 : ℝ) • e) ≠ 0 := by
    simpa [seedBase] using PDE.vecNormSq_eq_zero_iff.not.mpr hz0
  have heq : rescaledCutoff alpha sigma 0 0 e = radialProfile alpha := by
    funext a
    exact rescaledCutoff_zero alpha sigma e a
  have hh (w : PDE.Vec d) : rescaledHessian alpha sigma 0 0 e z w =
      radialHessianForm alpha z w w := by
    unfold rescaledHessian
    rw [heq, radialProfile_hessian alpha z w w hz0]
  obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha z hz0
  change z ≠ 0 ∧ seedBase (0 * sigma) z ((0 : ℝ) • e) ≠ 0 ∧ _
  refine ⟨hz0, hbase, ⟨w, ?_⟩, ⟨z, ?_⟩⟩
  · rw [hh]
    exact hw
  · rw [hh]
    exact radialHessian_radial_neg alpha ha ha1 z hz0

/-- One open parameter neighborhood preserves both signs uniformly on the fixed annulus. -/
theorem exists_rescaled_sign_neighborhood (d : ℕ) (hd : 2 ≤ d) (alpha sigma : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧
      ∀ e z, (e, z) ∈ cutoffAnnulus d → ∀ p ∈ U,
        (∃ w, 0 < rescaledHessian alpha sigma p.1 p.2 e z w) ∧
        (∃ w, rescaledHessian alpha sigma p.1 p.2 e z w < 0) := by
  obtain ⟨_, U, _, hU, hK, hzero, hsub⟩ := generalized_tube_lemma
    (isCompact_cutoffAnnulus d) (isCompact_singleton (x := (0, 0)))
    (isOpen_rescaledSignRegion d alpha sigma)
    (cutoffAnnulus_zero_signs d hd alpha sigma ha ha1)
  refine ⟨U, hU, hzero (Set.mem_singleton _), ?_⟩
  intro e z hz p hp
  exact (hsub (a := ((e, z), p)) ⟨hK hz, hp⟩).2.2

/-- The source parameters enter the uniform sign neighborhood for every sufficiently large R. -/
theorem eventually_rescaled_annulus_signs (d : ℕ) (hd : 2 ≤ d) (alpha C₀ sigma : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ e z, (e, z) ∈ cutoffAnnulus d →
      (∃ w, 0 < rescaledHessian alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e z w) ∧
      (∃ w, rescaledHessian alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e z w < 0) := by
  obtain ⟨U, hU, hzero, hsign⟩ := exists_rescaled_sign_neighborhood d hd alpha sigma ha ha1
  have ht : Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hs : Filter.Tendsto (fun R : ℝ => C₀ / Real.rpow R alpha)
      Filter.atTop (nhds 0) := by
    have hh := (tendsto_rpow_neg_atTop ha).const_mul C₀
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    simp only [Real.rpow_eq_pow, Real.rpow_neg hR, div_eq_mul_inv]
  have hp := hs.prodMk_nhds ht
  filter_upwards [hp.eventually (hU.mem_nhds hzero)] with R hR
  intro e z hz
  exact hsign e z hz (C₀ / Real.rpow R alpha, R⁻¹) hR

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
