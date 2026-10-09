module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatchPoint
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryRegularity
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic

/-! # The nonlinear return estimate for nested-box suprema -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder Filter
open scoped Topology

/-- Passing to a smaller-box supremum preserves the nonlinear positive-patch estimate. -/
theorem return_holder_patch_solution (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
      ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
      1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
      ∀ zStar ∈ returnFutureRegion,
      0 < sSup (u '' returnBox v b) →
      c₀ * (b - a) ^ beta * sSup (u '' returnBox v a) ^ (1 + beta / alpha) *
        sSup (u '' returnBox v b) ^ (-beta / alpha) ≤ u zStar := by
  obtain ⟨alpha, beta, c₀, ha, ha1, hb, hc, hpoint⟩ :=
    return_holder_patch_point lam Lam hlam hLam hp6
  refine ⟨alpha, beta, c₀, ha, ha1, hb, hc, ?_⟩
  intro A u hu a b v habase hab hb1 hv zStar hstar hMb
  have hne : (u '' returnBox v a).Nonempty :=
    ⟨u (point 1 0 v), mem_image_of_mem u (returnBox_center v a (by linarith))⟩
  obtain ⟨M, hM⟩ := hu.1
  have hbounded : BddAbove (u '' returnBox v a) := ⟨M, by
    rintro _ ⟨q, hq, rfl⟩
    have hqref := returnBox_subset_reference v a hv (by linarith) hq
    exact (le_abs_self _).trans (hM q (by linarith [hqref.1.1]))⟩
  obtain ⟨f, _hmono, hlim, hf⟩ := exists_seq_tendsto_sSup hne hbounded
  let g : ℝ → ℝ := fun x => c₀ * (b - a) ^ beta * x ^ (1 + beta / alpha) *
    sSup (u '' returnBox v b) ^ (-beta / alpha)
  have hg : Continuous g :=
    ((Real.continuous_rpow_const (by positivity : 0 ≤ 1 + beta / alpha)).const_mul
      (c₀ * (b - a) ^ beta)).mul_const _
  have hseq : ∀ n, g (f n) ≤ u zStar := by
    intro n
    obtain ⟨z, hz, hzf⟩ := hf n
    rw [← hzf]
    exact hpoint A u hu a b v habase hab hb1 hv z zStar hz hstar hMb
  exact le_of_tendsto (hg.continuousAt.tendsto.comp hlim) (Eventually.of_forall hseq)

/-- The source nested-box estimate for the actual canonical reflected semigroup solution. -/
theorem return_holder_patch
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
      ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ a b : ℝ, 1 / 2 ≤ a → a < b → b ≤ 1 →
      ∀ s v : ℝ, 2 ≤ s → s ≤ 3 → |v| ≤ 1 →
      let u := reflectedSemigroupSolution hH hLE hlam hLam A F
      let Ma := sSup (u '' returnBox v a)
      let Mb := sSup (u '' returnBox v b)
      0 < Mb → c₀ * (b - a) ^ beta * Ma ^ (1 + beta / alpha) * Mb ^ (-beta / alpha) ≤
        u (point s 0 v) := by
  obtain ⟨alpha, beta, c₀, ha, ha1, hb, hc, hsol⟩ :=
    return_holder_patch_solution lam Lam hlam hLam hp6
  refine ⟨alpha, beta, c₀, ha, ha1, hb, hc, ?_⟩
  intro A F hF0 hF a b habase hab hb1 s v hs hs1 hv
  dsimp only
  intro hMb
  apply hsol (returnReflectedCoefficient A) _
    (reflectedSemigroupSolution_homogeneous hH hLE hlam hLam A F hF0 hF)
    a b v habase hab hb1 hv (point s 0 v) ?_ hMb
  exact ⟨⟨hs, hs1⟩, by simp [point, return_norm_one],
    by simpa only [point, return_norm_one] using hv.trans (by norm_num : (1 : ℝ) ≤ 2)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
