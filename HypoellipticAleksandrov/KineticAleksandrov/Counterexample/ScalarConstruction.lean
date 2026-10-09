module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarHessianScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
import Mathlib.Tactic

/-!
# Explicit scalar construction before weak assembly

The constructed source function and its native representative jets are supplied directly.
This theorem does not assert the outstanding weak-identity and jet-bound clauses of
`CounterProfileOneStatement`.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory

/-- The source scalar function, comparison, native equation, and homogeneous measurable jets. -/
theorem exists_scalar_classical_profile (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ Lam c C : ℝ, ∃ H : XV 1 → ℝ,
    ∃ gx gv : XV 1 → PDE.Vec 1, ∃ hess : XV 1 → PDE.Mat 1,
      1 < Lam ∧ 0 < c ∧ 0 < C ∧ Continuous H ∧ H 0 = 0 ∧
      (∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) ∧
      (∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
        H q ≤ C * Real.rpow (rho q) alpha) ∧
      Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
      (∀ᵐ q ∂volume, gx q = dx H q ∧ gv q = dv H q ∧ hess q = dvv H q) ∧
      (∀ᵐ q ∂volume, matrixContraction (scalarProfileCoefficient Lam q) (hess q) =
        PDE.vecDot q.2 (gx q)) ∧
      (∀ q : XV 1, q.1 0 ≠ 0 → ContDiffAt ℝ 2 H q) ∧
      (∀ r : ℝ, 0 < r → ∀ q,
        gx (dilate r q) = Real.rpow r (alpha - 3) • gx q ∧
        gv (dilate r q) = Real.rpow r (alpha - 1) • gv q ∧
        hess (dilate r q) = Real.rpow r (alpha - 2) • hess q) := by
  let gamma : ScalarGamma := ⟨alpha / 3, by constructor <;> linarith⟩
  have hga : 3 * gamma.1 = alpha := by dsimp only [gamma]; ring
  obtain ⟨Lam, hLam, hmatch⟩ := exists_matching_ratio gamma.1 gamma.2.1 gamma.2.2
  have hp : 0 < Lam := lt_trans zero_lt_one hLam
  obtain ⟨c, C, hc, hcC, hcomp⟩ := scalarProfile_comparison gamma Lam hp hmatch
  refine ⟨Lam, c, C, scalarProfile gamma Lam, scalarGx gamma Lam, scalarGv gamma Lam,
    scalarHess gamma Lam, hLam, hc, hc.trans_le hcC,
    scalarProfile_continuous gamma Lam hp hmatch, scalarProfile_zero gamma Lam, ?_, ?_,
    measurable_scalarGx gamma Lam, measurable_scalarGv gamma Lam,
    measurable_scalarHess gamma Lam, scalarJets_eq_ae gamma Lam,
    scalarJets_equation_ae gamma Lam hp, scalarProfile_contDiffAt_off_axis gamma Lam hp, ?_⟩
  · intro r hr q
    simpa only [hga] using scalarProfile_homogeneous gamma Lam r hr q
  · simpa only [hga] using hcomp
  · intro r hr q
    simpa only [hga] using And.intro (scalarGx_homogeneous gamma Lam r hp hr q)
      (And.intro (scalarGv_homogeneous gamma Lam r hp hr q)
        (scalarHess_homogeneous gamma Lam r hp hr q))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
