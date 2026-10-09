module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalMass
import Mathlib.Tactic

/-! # Canonical enlarged-strip finiteness and uniform total visit count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- An explicit ellipticity-only constant for the enlarged-strip visit count. -/
def enlargedVisitMassConstant (lam Lam : ℝ) : ℝ :=
  9 / 5 + 16 / 5 * (128 * Lam / lam * Real.sqrt (2 * Lam))

/-- The explicit counting constant is positive under the source ellipticity assumptions. -/
theorem enlargedVisitMassConstant_pos {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) : 0 < enlargedVisitMassConstant lam Lam := by
  have hLp : 0 < Lam := hlam.trans_le hLam
  unfold enlargedVisitMassConstant
  positivity

/-- Full-space occupation and terminal domination give the source uniform mass bound.
The two premises are exactly the enlarged-recursion conclusions assigned to AU-14a. -/
theorem enlargedVisitStarts_mass_le_of_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T : ℝ)
    (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hOccupation : ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
          enlargedFullSpaceOccupation hH hLE hlam hLam A P T)
    (hTerminal : ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
      enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
        enlargedFullSpaceTerminal hH hLE hlam hLam A P b) :
    enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P univ ≤
      ENNReal.ofReal (enlargedVisitMassConstant lam Lam * (1 + R / c.r)) := by
  have hPT : P.time < P.time + T := by linarith
  have hLn : 0 ≤ Lam := hlam.le.trans hLam
  have hr := c.positive
  have hsqrt : Real.sqrt T ≤ R := by
    have h := Real.sqrt_le_sqrt hTR
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hR] at h
    exact h
  have hscale : (64 * c.r / lam) * Real.sqrt (2 * Lam * T) ≤
      (64 * c.r / lam) * (Real.sqrt (2 * Lam) * R) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Lam)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) (by positivity)
  apply visit_sum_mass_le_of_partial_mass_le
  intro N
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  have hm := enlargedQuadratic_partial_mass_bound hH hLE hlam hLam A c J
    P.time (P.time + T) P le_rfl hPT hJ N
  have he := enlarged_terminal_partial_mass_le_one_of_domination
    hH hLE hlam hLam A c J T P hT N
      (hTerminal N (P.time + T) (by linarith) le_rfl)
  have ho := (enlargedActivePiece_partial_capacity_of_domination
    hH hLE hlam hLam A c J T P hT hbar N (hOccupation N)).trans hscale
  have hnum := hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity))
    (mul_le_mul_of_nonneg_left ho (by positivity : 0 ≤ 2 * Lam)))
  have heq : 2 * Lam * ((64 * c.r / lam) * (Real.sqrt (2 * Lam) * R)) =
      (128 * Lam / lam * Real.sqrt (2 * Lam)) * R * c.r := by ring
  rw [mul_one, heq] at hnum
  have hbound := enlarged_mass_arithmetic hr hR.le
    (by positivity : 0 ≤ 128 * Lam / lam * Real.sqrt (2 * Lam)) hnum
  rw [← visit_partial_real_mass mu N univ MeasurableSet.univ] at hbound
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) ?_).mpr hbound
  exact mul_nonneg (enlargedVisitMassConstant_pos hlam hLam).le (by positivity)

/-- Uniform canonical mass bounds imply finiteness of the entire enlarged count. -/
theorem enlargedVisitStarts_isFiniteMeasure_of_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (R T : ℝ)
    (P : Point) (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (hOccupation : ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
          enlargedFullSpaceOccupation hH hLE hlam hLam A P T)
    (hTerminal : ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
      enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
        enlargedFullSpaceTerminal hH hLE hlam hLam A P b) :
    IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P) :=
  ⟨(enlargedVisitStarts_mass_le_of_domination hH hLE hlam hLam A c J R T P
    hR hT hTR hbar hJ hOccupation hTerminal).trans_lt ENNReal.ofReal_lt_top⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
