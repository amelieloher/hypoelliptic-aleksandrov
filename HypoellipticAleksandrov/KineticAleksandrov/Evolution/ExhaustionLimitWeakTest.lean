module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact-test passage for the actual exhaustion limit

The finite weak equation is obtained from the actual Dirichlet solution.
Integral convergence and locality of the adjoint pass it to the limit.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- Every smooth compact test supported in a fixed bounded inner cylinder satisfies
the regularized adjoint identity for the actual exhaustion limit. -/
theorem integral_regularizedAdjoint_innerBall_dirichlet_limit_eq_zero
    {n : ℕ} {lam Lam Lb m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k)
    (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop)
    (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k))
    (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|)
    (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2)
    (u : ℕ → TimeVelocity (n + n) → ℝ)
    (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k))
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ evolutionHomeomorph n ⁻¹'
      {p : KineticPoint n | α < p.time ∧ p.time < τ ∧
        p.position ∈ movingDomain (PDE.euclideanBall 0 (r0 - δ0)) Γ p.time ∧
        radialSq p < S0 ^ 2}) :
    (∫ p, limUnder atTop (fun k => straightenedPullback (g k) (u k) p) *
      regularizedAdjoint B b ε ψ ((evolutionHomeomorph n).symm p)) = 0 := by
  let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  let φ (p : KineticPoint n) := regularizedAdjoint B b ε ψ
    ((evolutionHomeomorph n).symm p)
  have hφ : Continuous φ := (contDiff_regularizedAdjoint hBs hbs hψ ε).continuous.comp
    (evolutionHomeomorph n).symm.continuous
  have hKs (x : EvolutionVec n) (hx : x ∈ tsupport ψ) :
      evolutionHomeomorph n x ∈ K := by
    have hp := hs hx
    exact ⟨⟨hp.1.le, hp.2.1.le, subset_closure hp.2.2.1⟩, hp.2.2.2.le⟩
  have hzeroK (p : KineticPoint n) (hp : p ∉ K) : φ p = 0 := by
    apply regularizedAdjoint_eq_zero_of_notMem_tsupport
    intro hx
    exact hp (by simpa using hKs _ hx)
  have hInt := tendsto_setIntegral_mul_innerBall_dirichlet (S0 := S0)
    hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu φ hφ
  have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
    hδ0 hδr β R hβlim hRlim g hclose
  have hIz : ∀ᶠ k : ℕ in atTop,
      (∫ p in K, straightenedPullback (g k) (u k) p * φ p) = 0 := by
    filter_upwards [hmem] with k hk
    let D : Set (KineticPoint n) := {p | a < p.time ∧ p.time < τ ∧
      spatialPack (p.position - g k p.time) p.velocity ∈
        openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k))}
    have hΩ : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec n) r0) :=
      Or.inr (Or.inl ⟨0, r0, by linarith, rfl⟩)
    have hw := weakRegularized_of_straightened_dirichlet
      (n := n) (hn := hn) (lam := lam) (Lam := Lam) (m := m) (L_b := Lb)
      (hlam := hlam) (hlamLam := hlamLam) (hm := hm) (hmLb := hmLb)
      (Ω := PDE.euclideanBall 0 r0) (γ := Γ) (B := B) (b := b)
      (hΩ := hΩ) (hγ := hΓ) (hB_smooth := hBs) (hB_symm := hBsym)
      (hB_ell := hB) (hb_smooth := hbs) (hb_lipschitz := hb) (hb_coercive := hbco)
      a τ (r0 - β k) (R k) (haα.trans hατ) hk.1 hk.2.1 (g k) (hg k)
      ε hε F (u k) (hu k)
    have hsD : tsupport ψ ⊆ evolutionHomeomorph n ⁻¹' D := by
      intro x hx
      have hp := hs hx
      exact ⟨haα.trans hp.1, hp.2.1, hk.2.2 _ (hKs x hx)⟩
    have hzeroD (p : KineticPoint n) (hp : p ∉ D) : φ p = 0 := by
      apply regularizedAdjoint_eq_zero_of_notMem_tsupport
      intro hx
      exact hp (by simpa using hsD hx)
    have he := hw.2 ψ hψ hc hsD
    have he' : (∫ p in D, straightenedPullback (g k) (u k) p * φ p) = 0 := by
      simpa only [straightenedPullback, straightenedPoint, φ, zero_mul, integral_zero]
        using he
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroK p hp, mul_zero])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroD p hp, mul_zero])] at he'
    exact he'
  have hlim0 : (∫ p in K, limUnder atTop
      (fun k => straightenedPullback (g k) (u k) p) * φ p) = 0 :=
    tendsto_nhds_unique hInt (tendsto_const_nhds.congr' (hIz.mono fun k hk => hk.symm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => by rw [hzeroK p hp, mul_zero])] at hlim0
  exact hlim0

end HypoellipticAleksandrov.KineticAleksandrov
