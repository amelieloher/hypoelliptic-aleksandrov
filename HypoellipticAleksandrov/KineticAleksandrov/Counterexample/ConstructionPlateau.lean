module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionSecond

/-! # The cutoff multiplier is locally one throughout the profile domain -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter
open scoped Topology

/-- The velocity cutoff can have a strict inner margin on the entire compact domain. -/
theorem construction_exists_strict_velocity_margin {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (R : ℝ)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) :
    ∃ m : ℝ, m < R ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m := by
  obtain ⟨m, hm, hb⟩ := construction_exists_velocity_margin ha h R hvel
  refine ⟨(m + R ^ 2) / 2, by linarith only [hm], ?_⟩
  intro q hq
  have hh := hb q hq
  linarith only [hh, hm]

/-- On the strict inner region the packed cutoff is locally constant one. -/
theorem constructionPackedCutoff_eventually_one {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (x : PDE.Vec (d + d)) (hx : PDE.vecNormSq (spatialCoordinateCLE d x).2 < m) :
    constructionPackedCutoff d m R =ᶠ[𝓝 x] (fun _ => 1) := by
  have hc := PDE.contDiff_vecNormSq.continuous.comp (spatialCoordinateCLE d).continuous.snd
  filter_upwards [hc.continuousAt.eventually (Iio_mem_nhds hx)] with y hy
  exact constructionVelocityCutoff_eq_one m R hm _ hy.le

/-- Both orders of cutoff derivatives vanish on the strict inner region. -/
theorem constructionPackedCutoff_jets_zero {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (x : PDE.Vec (d + d)) (hx : PDE.vecNormSq (spatialCoordinateCLE d x).2 < m) :
    fderiv ℝ (constructionPackedCutoff d m R) x = 0 ∧
      ∀ k, fderiv ℝ (fun y => fderiv ℝ (constructionPackedCutoff d m R) y (PDE.basisVec k))
        x = 0 := by
  have he := constructionPackedCutoff_eventually_one m R hm x hx
  have hfirst : fderiv ℝ (constructionPackedCutoff d m R) x = 0 := by
    rw [he.fderiv_eq]
    exact (hasFDerivAt_const (1 : ℝ) x).fderiv
  refine ⟨hfirst, ?_⟩
  intro k
  have hd : (fun y => fderiv ℝ (constructionPackedCutoff d m R) y (PDE.basisVec k)) =ᶠ[𝓝 x]
      (fun _ => 0) := by
    filter_upwards [he.eventually_nhds] with y hy
    have hy' : constructionPackedCutoff d m R =ᶠ[𝓝 y] (fun _ => 1) := hy
    rw [hy'.fderiv_eq, (hasFDerivAt_const (1 : ℝ) y).fderiv]
    rfl
  rw [hd.fderiv_eq]
  exact (hasFDerivAt_const (0 : ℝ) x).fderiv

/-- Throughout the profile domain the extended representatives equal the raw cutoff jets. -/
theorem construction_extended_jets_eq_raw_on_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ) (hm : m < R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (x : PDE.Vec (d + d)) (hx : profileFunction h (spatialCoordinateCLE d x) < 1) :
    (∀ i, constructionExtendedPackedGradient h r mu R m t x i =
      spatialPackedCutoffGradient h r mu R t x i) ∧
    (∀ i k, constructionExtendedPackedHessian h r mu R m t x i k =
      spatialPackedCutoffVelocityHessian h r mu R t x i k) := by
  have hv := hmargin _ hx.le
  have hval : constructionPackedCutoff d m R x = 1 :=
    constructionVelocityCutoff_eq_one m R hm _ hv.le
  obtain ⟨hfirst, hsecond⟩ := constructionPackedCutoff_jets_zero m R hm x hv
  constructor
  · intro i
    simp only [constructionExtendedPackedGradient, hval, hfirst, one_mul,
      _root_.zero_apply, mul_zero, add_zero]
  · intro i k
    simp only [constructionExtendedPackedHessian, hval, hfirst, hsecond, one_mul,
      _root_.zero_apply, mul_zero, zero_mul, add_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
