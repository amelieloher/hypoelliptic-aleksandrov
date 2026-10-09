module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothBoundary
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxBoundary
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBoundaryStability
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Uniformly convergent smooth boundary replacements

Uniform approximation of the prescribed data and the maximum principle produce an
actual continuous limit on the closed cylinder. Interior regularity is a separate step.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set Dirichlet KineticAleksandrov
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

/-- A pairwise metric bound by a vanishing scalar sequence gives the Cauchy property. -/
theorem cauchySeq_of_dist_le_vanishing_sum {E : Type*} [PseudoMetricSpace E]
    (u : ℕ → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n m, dist (u n) (u m) ≤ 2 * (ε n + ε m)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hε.eventually_lt_const (show 0 < δ / 4 by positivity))
  refine ⟨N, fun n hn m hm => ?_⟩
  have hnδ := hN n hn
  have hmδ := hN m hm
  exact lt_of_le_of_lt (hb n m) (by linarith)

/-- Continuous closed-cylinder data have a uniformly convergent sequence of smooth replacements. -/
theorem exists_uniform_smooth_boundary_replacements {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r))) :
    ∃ (f v : ℕ → TimeVelocity d → ℝ)
      (U : ℕ → C(scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r), ℝ))
      (V : C(scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r), ℝ)),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧
      (∀ n, ∀ z ∈ scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r),
        |f n z - w z| < 1 / ((n : ℝ) + 1)) ∧
      (∀ n, IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
        (fun y => f n (T, y)) (f n) (v n)) ∧
      (∀ n z, U n z = v n z) ∧ Tendsto U atTop (𝓝 V) ∧
      ∀ z : scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r),
        (z : TimeVelocity d) ∈ scalarParabolicTerminalLateralBoundary a T
        (PDE.euclideanBall v₀ r) → V z = w z := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  let K := scalarParabolicClosedCylinder a T Ω
  have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
  have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
  have hK : IsCompact K := isCompact_scalarParabolicClosedCylinder a T hΩb
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have happrox (n : ℕ) : ∃ f : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ z ∈ K, |f z - w z| < ε n := by
    obtain ⟨f, hf, _, _, hb⟩ := exists_smooth_compact_boundary_approx hK
      isOpen_univ (subset_univ _) w hw (hεpos n)
    exact ⟨f, hf, hb⟩
  choose f hf hfb using happrox
  have hvex (n : ℕ) := exists_smooth_backward_homogeneous_replacement hd v₀ r hr a T haT
    lam Lam hlam hLam A hA hlo hhi (f n) (hf n)
  choose v hv using hvex
  let U : ℕ → C(K, ℝ) := fun n =>
    ⟨fun z => v n z, continuousOn_iff_continuous_domRestrict.mp (hv n).1⟩
  have hdiff (n m : ℕ) : dist (U n) (U m) ≤ 2 * (ε n + ε m) := by
    rw [dist_eq_norm]
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro z
    change |v n z - v m z| ≤ _
    apply abs_homogeneous_solution_sub_le_boundary_error hΩ hΩb a T haT A
      hA.continuous (Occupation.posSemidef_of_lower_loewner hlam hlo)
      (fun y => f n (T, y)) (fun y => f m (T, y)) (f n) (f m) (v n) (v m)
      (hv n) (hv m) (ε n + ε m) (by positivity) ?_ ?_ z z.property
    · intro y hy
      have hz : (T, y) ∈ K := ⟨⟨haT.le, le_rfl⟩, hy⟩
      calc
        |f n (T, y) - f m (T, y)| ≤ |f n (T, y) - w (T, y)| +
            |f m (T, y) - w (T, y)| := by
              simpa only [abs_sub_comm (w (T, y)) (f m (T, y))] using
                abs_sub_le (f n (T, y)) (w (T, y)) (f m (T, y))
        _ ≤ ε n + ε m := add_le_add (hfb n _ hz).le (hfb m _ hz).le
    · intro z hz
      have hzK : z ∈ K := ⟨hz.1, frontier_subset_closure hz.2⟩
      calc
        |f n z - f m z| ≤ |f n z - w z| + |f m z - w z| := by
          simpa only [abs_sub_comm (w z) (f m z)] using abs_sub_le (f n z) (w z) (f m z)
        _ ≤ ε n + ε m := add_le_add (hfb n _ hzK).le (hfb m _ hzK).le
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_vanishing_sum U ε hε hdiff)
  refine ⟨f, v, U, V, hf, hfb, hv, fun _ _ => rfl, hV, ?_⟩
  intro z hz
  have hfz : Tendsto (fun n => f n z) atTop (𝓝 (w z)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => (show dist (f n z) (w z) < ε n by
        simpa only [Real.dist_eq] using hfb n z z.property).le) hε
  have hUz : ∀ n, U n z = f n z := by
    intro n
    change v n z = f n z
    rcases hz with hz | hz
    · have ht : z.val.1 = T := mem_singleton_iff.mp hz.1
      simpa only [← ht, Prod.mk.eta] using (hv n).2.2.2.1 z.val.2 hz.2
    · exact (hv n).2.2.2.2 z hz
  have hlim : Tendsto (fun n => U n z) atTop (𝓝 (V z)) :=
    ((continuous_eval_const z).tendsto V).comp hV
  have hlimw : Tendsto (fun n => U n z) atTop (𝓝 (w z)) := by
    simpa only [hUz] using hfz
  exact tendsto_nhds_unique hlim hlimw

end HypoellipticAleksandrov.Parabolic.LocalHolder
