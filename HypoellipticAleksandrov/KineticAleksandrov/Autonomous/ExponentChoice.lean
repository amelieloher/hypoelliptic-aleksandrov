module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CriticalP
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierParameters
import Mathlib.Tactic

/-! # Choice of the autonomous barrier and conjugate density exponents -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- Choose the barrier degree before any coefficient, cylinder, or solution data. -/
theorem exists_autonomous_exponents (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ alpha : ℝ,
      bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
        (by simpa only [one_mul] using hLam)) - 2 < alpha ∧
      alpha < 1 ∧ alpha < p - 3 ∧
      1 < p / (p - 1) ∧ p / (p - 1) < (4 - (1 - alpha)) / (3 - (1 - alpha)) := by
  let ratio : {r : ℝ // 1 ≤ r} :=
    ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)⟩
  have hb := bellmanAdjointExponent_range ratio.1 ratio.2
  have hp' : 1 + bellmanAdjointExponent ratio.1 ratio.2 < p := hp
  have hinterval : bellmanAdjointExponent ratio.1 ratio.2 - 2 < min 1 (p - 3) :=
    lt_min (by linarith only [hb.2]) (by linarith only [hp'])
  obtain ⟨alpha, ha, hupper⟩ := exists_between hinterval
  have ha1 := (lt_min_iff.mp hupper).1
  have hap := (lt_min_iff.mp hupper).2
  have hapos : 0 < alpha := by linarith only [hb.1, ha]
  have hpm : 0 < p - 1 := by linarith only [hb.1, hp']
  have hden : 0 < 3 - (1 - alpha) := by linarith only [hapos]
  refine ⟨alpha, ha, ha1, hap, ?_, ?_⟩
  · exact (one_lt_div hpm).2 (by linarith)
  · apply (div_lt_div_iff₀ hpm hden).2
    nlinarith only [hap]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
