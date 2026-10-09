module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsTerminal
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Terminal Green identity for C² tests

Uniform smooth approximation is applied only to the terminal datum. The test's
actual C² operator stays fixed, so no convergence of coefficient derivatives is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory Filter
open scoped Topology

/-- A bounded C² test with uniformly continuous terminal datum obeys the exact actual
Green identity. Smoothness of the terminal datum is discharged by uniform approximation. -/
theorem fullspace_green_terminal_c2
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (f : Point → ℝ) (hf : ContDiff ℝ 2 (f ∘ evolutionHomeomorph 1))
    (Cf M : ℝ) (hM : 0 ≤ M) (hfb : ∀ p, |f p| ≤ Cf)
    (hLf : ∀ p, |transportedForwardOperator (evolutionCoefficient A.a)
      (identityDrift 1) f p| ≤ M)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : UniformContinuous F)
    (hFt : ∀ p, p.time = T → f p = F (p.position, p.velocity))
    (p : Point) (hp : p.time < T) :
    duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) f q)) p =
      f p - ∫ x, F x ∂E.2.master
        (wholeSpaceQuery p.time T hp.le p.position p.velocity) := by
  let ε := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hεp (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose G hGs hGa using fun n => hF.exists_contDiff_dist_le (hεp n)
  obtain ⟨C, hC, hCb⟩ := F.exists_bound
  have hGb (n : ℕ) (x : EvolutionAmbientState 1) : |G n x| ≤ C + 1 := by
    have hh := hGa n x
    rw [Real.dist_eq] at hh
    calc
      |G n x| ≤ |G n x - F x| + |F x| := by
        simpa only [sub_add_cancel] using abs_add_le (G n x - F x) (F x)
      _ ≤ ε n + C := add_le_add hh.le (hCb x)
      _ ≤ C + 1 := by linarith only [hε1 n]
  let Fn (n : ℕ) : BoundedBorel (EvolutionAmbientState 1) :=
    ⟨G n, (hGs n).continuous.measurable,
      ⟨C + 1, by linarith only [hC], hGb n⟩⟩
  let μ := E.2.master (wholeSpaceQuery p.time T hp.le p.position p.velocity)
  have : IsFiniteMeasure μ := ⟨(E.2.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  have hGl (x : EvolutionAmbientState 1) : Tendsto (fun n => G n x) atTop (𝓝 (F x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hεlim
    rw [Real.norm_eq_abs]
    simpa only [Real.dist_eq] using (hGa n x).le
  have hIl : Tendsto (fun n => ∫ x, Fn n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C + 1)
      (fun n => (Fn n).measurable.aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]; exact hGb n x)
    · exact Eventually.of_forall hGl
  let V := duhamelPotential E.2 T
    ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
      (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
        (identityDrift 1) f q)) p
  have herr (n : ℕ) : |V - (f p - ∫ x, Fn n x ∂μ)| ≤ ε n := by
    apply fullspace_green_terminal_error_smooth_datum hH hlam hLam A E hE T f hf
      Cf M hM hfb hLf (Fn n) (hGs n) (ε n) ?_ p hp
    intro q hq
    rw [hFt q hq, abs_sub_comm]
    exact (hGa n _).le
  have hh : |V - (f p - ∫ x, F x ∂μ)| ≤ 0 :=
    le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub
      (tendsto_const_nhds.sub hIl)).abs) hεlim herr
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
