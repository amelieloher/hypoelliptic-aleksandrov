module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Recovery of every spatial derivative from actual uniformly convergent solutions

All jets are extracted together in a countable product of compact function spaces.
The zeroth jet identifies the original limit, and uniform derivative convergence
identifies every higher jet as its actual derivative.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Metric
open scoped Topology ContDiff

/-- Compactness of all jets on a closed ball, with one common subsequence. -/
theorem corrector_all_jets_subsequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℕ → E → ℝ) (a : E) (r : ℝ)
    (hs : ∀ j, ∀ x ∈ closedBall a r, ContDiffAt ℝ (⊤ : ℕ∞) (f j) x)
    (M : ℕ → NNReal)
    (hb : ∀ j m, ∀ x ∈ closedBall a r, ‖iteratedFDeriv ℝ m (f j) x‖₊ ≤ M m) :
    ∃ (g : E → FormalMultilinearSeries ℝ E ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ m, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (f (φ j)))
        (fun x => g x m) atTop (closedBall a r) := by
  classical
  have hfinite : ∀ m : ℕ, FiniteDimensional ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin m => E) ℝ) := by
    intro m
    induction m with
    | zero => exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toLinearEquiv.finiteDimensional
    | succ m hm =>
      let : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ) := hm
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) ℝ).symm.toLinearEquiv.finiteDimensional
  let : ∀ m : ℕ, FiniteDimensional ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin m => E) ℝ) := hfinite
  let K := closedBall a r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall a r)
  let J := fun (m j : ℕ) => BoundedContinuousFunction.mkOfCompact
    (⟨fun x : K => iteratedFDeriv ℝ m (f j) x,
      continuousOn_iff_continuous_domRestrict.mp (fun x hx =>
        ((hs j x hx).differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).continuousAt.continuousWithinAt)⟩)
  have hLip m j : LipschitzWith (M (m + 1)) (J m j) := by
    have h := (convex_closedBall a r).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => (hs j x hx).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m))
      (fun x hx => show ‖fderiv ℝ (iteratedFDeriv ℝ m (f j)) x‖₊ ≤ M (m + 1) from
        by
          apply NNReal.coe_le_coe.mp
          change ‖fderiv ℝ (iteratedFDeriv ℝ m (f j)) x‖ ≤ (M (m + 1) : ℝ)
          rw [norm_fderiv_iteratedFDeriv]
          exact NNReal.coe_le_coe.mpr (hb j (m + 1) x hx))
    intro x y
    exact h x.property y.property
  have hc m : IsCompact (closure (range (J m))) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall 0 (M m))
      (isCompact_closedBall _ _) (range (J m))
    · rintro _ x ⟨j, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      change ‖iteratedFDeriv ℝ m (f j) x‖ ≤ (M m : ℝ)
      exact NNReal.coe_le_coe.mpr (hb j m x x.property)
    · apply (LipschitzWith.uniformEquicontinuous
        (fun q : range (J m) => (q.val : K → _)) (M (m + 1)) ?_).equicontinuous
      rintro ⟨_, j, rfl⟩
      exact hLip m j
  obtain ⟨G, _, φ, hφ, ht⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (x := fun j m => J m j) (fun j m => subset_closure (mem_range_self j))
  let g := fun x m => if hx : x ∈ K then G m ⟨x, hx⟩ else 0
  refine ⟨g, φ, hφ, fun m => ?_⟩
  have hm := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((continuous_apply m).tendsto G |>.comp ht)
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  convert hm using 1
  · rfl
  · funext x
    dsimp only [Function.comp_def, g]
    simp

/-- Uniform convergence plus bounds at every order recover smoothness and all jets. -/
theorem corrector_derivative_recovery
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℕ → E → ℝ) (u : E → ℝ) (a : E) (r : ℝ)
    (hs : ∀ j, ∀ x ∈ closedBall a r, ContDiffAt ℝ (⊤ : ℕ∞) (f j) x)
    (M : ℕ → NNReal)
    (hb : ∀ j m, ∀ x ∈ closedBall a r, ‖iteratedFDeriv ℝ m (f j) x‖₊ ≤ M m)
    (hu : TendstoUniformlyOn f u atTop (closedBall a r)) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (ball a r) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m,
        TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (f (φ j)))
          (iteratedFDeriv ℝ m u) atTop (ball a r) := by
  classical
  obtain ⟨g, φ, hφ, hg⟩ := corrector_all_jets_subsequence f a r hs M hb
  have hzero : ∀ x ∈ ball a r, (g x 0).curry0 = u x := by
    intro x hx
    change (continuousMultilinearCurryFin0 ℝ E ℝ) (g x 0) = u x
    have ht := (hg 0).tendsto_at (ball_subset_closedBall hx)
    have ht' := (hu.tendsto_at (ball_subset_closedBall hx)).comp hφ.tendsto_atTop
    have he := (continuousMultilinearCurryFin0 ℝ E ℝ).continuous.tendsto (g x 0)
    have hv := he.comp ht
    simpa only [Function.comp_def, iteratedFDeriv_zero_eq_comp,
      LinearIsometryEquiv.apply_symm_apply] using
      tendsto_nhds_unique hv ht'
  have hder : ∀ m x, x ∈ ball a r →
      HasFDerivAt (fun y => g y m) (g x (m + 1)).curryLeft x := by
    intro m x hx
    have hc := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => E) ℝ).isometry.uniformContinuous
    refine hasFDerivAt_of_tendstoUniformlyOn isOpen_ball
      (hc.comp_tendstoUniformlyOn ((hg (m + 1)).mono ball_subset_closedBall))
      (fun j y hy => ?_) (fun y hy => (hg m).tendsto_at (ball_subset_closedBall hy)) hx
    simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using
      ((hs (φ j) y (ball_subset_closedBall hy)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).hasFDerivAt
  have htaylor : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) u g (ball a r) :=
    (hasFTaylorSeriesUpToOn_top_iff' le_rfl).mpr
      ⟨hzero, fun m x hx => (hder m x hx).hasFDerivWithinAt⟩
  refine ⟨htaylor.contDiffOn, φ, hφ, fun m => ?_⟩
  have he : ∀ x ∈ ball a r, g x m = iteratedFDeriv ℝ m u x := by
    intro x hx
    rw [← iteratedFDerivWithin_of_isOpen m isOpen_ball hx]
    exact htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp)
      isOpen_ball.uniqueDiffOn hx
  exact ((hg m).mono ball_subset_closedBall).congr_right (fun _ hx => he _ hx)

/-- Derivative estimates with convergent amplitudes pass to the same smooth limit. -/
theorem corrector_derivative_estimates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℕ → E → ℝ) (u : E → ℝ) (a : E) (r : ℝ) (hr : 0 < r)
    (hs : ∀ j, ∀ x ∈ closedBall a r, ContDiffAt ℝ (⊤ : ℕ∞) (f j) x)
    (hu : TendstoUniformlyOn f u atTop (closedBall a r))
    (hc : ContinuousOn u (closedBall a r))
    (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m) (V : ℕ → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hV : Tendsto V atTop (𝓝 v))
    (hbound : ∀ j m, 1 ≤ m → ∀ x ∈ closedBall a r,
      ‖iteratedFDeriv ℝ m (f j) x‖ ≤ b m * V j) :
    ContDiffAt ℝ (⊤ : ℕ∞) u a ∧ ∀ m, 1 ≤ m →
      ‖iteratedFDeriv ℝ m u a‖ ≤ b m * v := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hc
  have htail : ∀ᶠ j in atTop, (∀ x ∈ closedBall a r, dist (u x) (f j x) < 1) ∧
      V j < v + 1 := ((Metric.tendstoUniformlyOn_iff.mp hu) 1 zero_lt_one).and
    ((tendsto_order.mp hV).2 (v + 1) (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let F := fun j => f (j + N)
  let M := fun m => if m = 0 then Real.toNNReal (max B 0 + 1)
    else Real.toNNReal (b m * (v + 1))
  have hF : TendstoUniformlyOn F u atTop (closedBall a r) :=
    by
      intro W hW
      exact (tendsto_add_atTop_nat N).eventually (hu W hW)
  have hFb : ∀ j m, ∀ x ∈ closedBall a r, ‖iteratedFDeriv ℝ m (F j) x‖₊ ≤ M m := by
    intro j m x hx
    apply NNReal.coe_le_coe.mp
    by_cases hm : m = 0
    · subst m
      have hh := (hN (j + N) (Nat.le_add_left N j)).1 x hx
      have hnorm := norm_le_norm_add_norm_sub (u x) (f (j + N) x)
      rw [dist_comm, dist_eq_norm] at hh
      dsimp only [M]
      rw [ite_eq_left rfl, Real.coe_toNNReal _ (by positivity)]
      change ‖iteratedFDeriv ℝ 0 (F j) x‖ ≤ max B 0 + 1
      rw [norm_iteratedFDeriv_zero]
      change ‖f (j + N) x‖ ≤ max B 0 + 1
      rw [norm_sub_rev] at hnorm
      linarith only [hnorm, hh, hB x hx, le_max_left B 0]
    · dsimp only [M]
      rw [ite_eq_right hm, Real.coe_toNNReal _ (mul_nonneg (hb m) (by linarith))]
      exact (hbound (j + N) m (Nat.one_le_iff_ne_zero.mpr hm) x hx).trans
        (mul_le_mul_of_nonneg_left (hN (j + N) (Nat.le_add_left N j)).2.le (hb m))
  obtain ⟨hsu, φ, hφ, hjet⟩ := corrector_derivative_recovery F u a r
    (fun j => hs (j + N)) M hFb hF
  have ha : a ∈ ball a r := mem_ball_self hr
  refine ⟨hsu.contDiffAt (isOpen_ball.mem_nhds ha), fun m hm => ?_⟩
  have hleft := ((hjet m).tendsto_at ha).norm
  have hright := ((hV.comp (tendsto_add_atTop_nat N)).comp hφ.tendsto_atTop).const_mul (b m)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun j =>
    hbound (φ j + N) m hm a (ball_subset_closedBall ha))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
