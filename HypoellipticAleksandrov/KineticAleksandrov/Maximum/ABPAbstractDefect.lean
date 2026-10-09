module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Comparison
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Restrict

/-! # The source defect and the smooth positive-set cutoff -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set MeasureTheory

/-- The source cutoff vanishes below half the positive threshold and equals one above it. -/
def abpPositiveCutoff (ε : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((2 * s - ε) / ε)

/-- Smoothness and the exact range and threshold properties of the cutoff. -/
theorem abpPositiveCutoff_spec {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (abpPositiveCutoff ε) ∧
      (∀ s, 0 ≤ abpPositiveCutoff ε s ∧ abpPositiveCutoff ε s ≤ 1) ∧
      (∀ s, s ≤ ε / 2 → abpPositiveCutoff ε s = 0) ∧
      (∀ s, ε ≤ s → abpPositiveCutoff ε s = 1) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (2 * s - ε) / ε) := by fun_prop
  refine ⟨Real.smoothTransition.contDiff.comp hc,?_,?_,?_⟩
  · intro s
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · intro s hs
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hε.le
    linarith only [hs]
  · intro s hs
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hε]
    linarith only [hs]

/-- Contraction of two continuous matrix fields is continuous in the native matrix API. -/
theorem continuousOn_matrixContraction {E : Type*} [TopologicalSpace E] {d : ℕ}
    {D : Set E} {A H : E → PDE.Mat d}
    (hA : ContinuousOn A D) (hH : ContinuousOn H D) :
    ContinuousOn (fun P => HypoellipticAleksandrov.matrixContraction (A P) (H P)) D := by
  unfold HypoellipticAleksandrov.matrixContraction
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact ((continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn hA)).mul
    ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hH))

/-- The forward operator of a classical function is continuous for continuous coefficients. -/
theorem continuousOn_forwardKineticOperator {d : ℕ} {D : Set (KineticPoint d)}
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D) (A : FullKineticCoefficient d)
    (hA : ContinuousOn (fun P : KineticPoint d => A P.time P.position P.velocity) D) :
    ContinuousOn (forwardKineticOperator A u) D := by
  have hdot : ContinuousOn (fun P => PDE.vecDot P.velocity (kineticPositionGradient u P)) D := by
    unfold PDE.vecDot
    apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_velocity).continuousOn.mul
      ((continuous_apply i).comp_continuousOn hu.continuousOn_kineticPositionGradient)
  exact (hu.continuousOn_kineticTimeDerivative.add hdot).add
    (continuousOn_matrixContraction hA hu.continuousOn_kineticVelocityHessian)

/-- The continuous defect and its positive-set cutoff have the source a.e. domination. -/
theorem abp_defect_cutoff {d : ℕ} {Q : Set (KineticPoint d)} (hQ : MeasurableSet Q)
    (A : FullKineticCoefficient d) (u g₀ : KineticPoint d → ℝ)
    (hu : IsKineticC112On u Q)
    (hA : ContinuousOn (fun P : KineticPoint d => A P.time P.position P.velocity) Q)
    (hg₀0 : ∀ P ∈ Q, 0 ≤ g₀ P)
    (hsub : ∀ᵐ P ∂(volume.restrict Q), -g₀ P ≤ forwardKineticOperator A u P)
    (ε : ℝ) (hε : 0 < ε) :
    let g := fun P => max (-forwardKineticOperator A u P) 0
    ContinuousOn g Q ∧ (∀ P, 0 ≤ g P) ∧
      (∀ P, 0 ≤ forwardKineticOperator A u P + g P) ∧
      (∀ᵐ P ∂(volume.restrict Q), 0 ≤ abpPositiveCutoff ε (u P) * g P ∧
        abpPositiveCutoff ε (u P) * g P ≤ {z | 0 < u z}.indicator g₀ P) := by
  dsimp only
  have hcut := abpPositiveCutoff_spec hε
  refine ⟨(continuousOn_forwardKineticOperator hu A hA).neg.sup continuousOn_const,
    fun P => le_max_right _ _,fun P => ?_,?_⟩
  · have h := le_max_left (-forwardKineticOperator A u P) 0
    linarith only [h]
  · filter_upwards [hsub,ae_restrict_mem hQ] with P hP hPQ
    refine ⟨mul_nonneg (hcut.2.1 _).1 (le_max_right _ _),?_⟩
    by_cases hpos : 0 < u P
    · rw [indicator_of_mem (show P ∈ {z | 0 < u z} from hpos)]
      have hg : max (-forwardKineticOperator A u P) 0 ≤ g₀ P :=
        max_le (by linarith only [hP]) (hg₀0 P hPQ)
      exact (mul_le_of_le_one_left (le_max_right _ _) (hcut.2.1 _).2).trans hg
    · rw [indicator_of_notMem (show P ∉ {z | 0 < u z} from hpos),
        hcut.2.2.1 _ (by linarith [not_lt.mp hpos]),zero_mul]

end HypoellipticAleksandrov.KineticAleksandrov
