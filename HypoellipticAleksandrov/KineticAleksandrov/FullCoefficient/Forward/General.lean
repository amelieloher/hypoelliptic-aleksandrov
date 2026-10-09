module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Extension
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.MollifyAdmissible
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# The forward equation for admissible test functions

The admissible test functions: the forward equation holds for every admissible `φ` (`C¹` in `τ`,
`C²` in `y`), and all integrands are `Γ`-integrable.  The proof mollifies `φ` in `(τ, y)`;
the mollifications are smooth admissible functions with uniform bounds and converge to `φ`
with the listed derivatives, so dominated convergence passes the identity to the limit.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology Convolution

variable {d : ℕ} {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}

theorem forwardIntegrand_eq_testSum (B : FullKineticCoefficient d) (σ₀ : ℝ)
    (φ : ℝ → EvolutionAmbientState d → ℝ) (τ : ℝ) (y : EvolutionAmbientState d) :
    forwardIntegrand B σ₀ φ τ y = testTime φ (τ, y) +
      ∑ i, ∑ j, B (σ₀ + τ) y.1 y.2 i j * testHessian φ i j (τ, y) +
        ∑ i, y.1 i * testPosition φ i (τ, y) := rfl

theorem forwardIntegrand_moll {ρ : ℝ × EvolutionAmbientState d → ℝ} {r : ℝ}
    (hρ : IsMollifierKernel ρ r) (hφ : IsAdmissibleTest T φ) (B : FullKineticCoefficient d)
    (σ₀ τ : ℝ) (y : EvolutionAmbientState d) :
    forwardIntegrand B σ₀ (fun τ y => moll ρ (testValue φ) (τ, y)) τ y =
      moll ρ (testTime φ) (τ, y) +
        ∑ i, ∑ j, B (σ₀ + τ) y.1 y.2 i j * moll ρ (testHessian φ i j) (τ, y) +
          ∑ i, y.1 i * moll ρ (testPosition φ i) (τ, y) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      (fun τ y => moll ρ (testValue φ) (τ, y)) q.1 q.2) := contDiff_moll_test hρ hφ
  rw [forwardIntegrand_eq_forwardReprAt B σ₀ hsm]
  unfold forwardReprAt
  have e : (fun q : ℝ × EvolutionAmbientState d =>
      (fun τ y => moll ρ (testValue φ) (τ, y)) q.1 q.2) = moll ρ (testValue φ) := rfl
  rw [e]
  simp only [jointTimePartial_moll hρ hφ, jointVelocityPartial_velocityPartial_moll hρ hφ,
    jointPositionPartial_moll hρ hφ]

/-- Uniform bound of the forward integrand of the mollifications of an admissible function. -/
theorem exists_uniform_bound_forwardIntegrand_moll (B : FullKineticCoefficient d) (σ₀ Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hB : ∀ σ y z i j, |B σ y z i j| ≤ Λ) (hφ : IsAdmissibleTest T φ) :
    ∃ C : ℝ, ∀ {ρ : ℝ × EvolutionAmbientState d → ℝ} {r : ℝ}, IsMollifierKernel ρ r → r ≤ 1 →
      ∀ τ y, |forwardIntegrand B σ₀ (fun τ y => moll ρ (testValue φ) (τ, y)) τ y| ≤ C := by
  obtain ⟨Ct, hCt⟩ := hφ.timeDeriv.2
  obtain ⟨Ch, hCh⟩ := exists_uniform_bound (fun (ij : Fin d × Fin d)
    (q : ℝ × EvolutionAmbientState d) => testHessian φ ij.1 ij.2 q)
    (fun ij => (hφ.velocityHess _ _).2)
  obtain ⟨Cw, hCw⟩ := exists_uniform_bound (fun (i : Fin d) (q : ℝ × EvolutionAmbientState d) =>
    q.2.1 i * testPosition φ i q) (fun i => (hφ.weightedTransport i i).2)
  obtain ⟨Cp, hCp⟩ := exists_uniform_bound (fun (i : Fin d) (q : ℝ × EvolutionAmbientState d) =>
    testPosition φ i q) (fun i => (hφ.positionGrad i).2)
  refine ⟨Ct + (d : ℝ) * d * (Λ * Ch) + d * (Cw + Cp), fun {ρ r} hρ hr1 τ y => ?_⟩
  rw [forwardIntegrand_moll hρ hφ]
  have hbdd : ∀ {g : ℝ × EvolutionAmbientState d → ℝ} {C : ℝ}, (∀ x, |g x| ≤ C) →
      ∀ x, |moll ρ g x| ≤ C := fun {g C} hg x =>
    abs_moll_le hρ.nonneg hρ.integral_eq_one hρ.integrable hg x
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    (hbdd (g := testTime φ) (fun x => hCt x) (τ, y)) ?_)) ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, B (σ₀ + τ) y.1 y.2 i j * moll ρ (testHessian φ i j) (τ, y)|
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, Λ * Ch := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hB _ _ _ _ _) (hbdd (fun x => hCh (i, j) x) (τ, y)) (abs_nonneg _) hΛ
      _ = (d : ℝ) * d * (Λ * Ch) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |y.1 i * moll ρ (testPosition φ i) (τ, y)| ≤ ∑ _i : Fin d, (Cw + Cp) :=
          Finset.sum_le_sum fun i _ =>
            abs_weighted_moll_le hρ hr1 i (f := testPosition φ i) (fun x => hCw i x)
              (fun x => hCp i x) (τ, y)
      _ = (d : ℝ) * (Cw + Cp) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]

/-- The forward integrand of an admissible function is continuous in `(τ, y)`. -/
theorem continuous_forwardIntegrand {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) (σ₀ : ℝ) (hφ : IsAdmissibleTest T φ) :
    Continuous (fun q : ℝ × EvolutionAmbientState d => forwardIntegrand B σ₀ φ q.1 q.2) := by
  have e : (fun q : ℝ × EvolutionAmbientState d => forwardIntegrand B σ₀ φ q.1 q.2) =
      fun q => testTime φ q + ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j * testHessian φ i j q +
        ∑ i, q.2.1 i * testPosition φ i q := rfl
  rw [e]
  refine (hφ.timeDeriv.1.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => ?_)).add (continuous_finsetSum _ fun i _ => (hφ.weightedTransport i i).1)
  have hc : Continuous (fun q : ℝ × EvolutionAmbientState d => B (σ₀ + q.1) q.2.1 q.2.2 i j) :=
    (hB i j).continuous.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)
  exact hc.mul (hφ.velocityHess i j).1

/-- **Forward equation for admissible tests**:
the Green measure of a point mass annihilates `∂_τ φ + B : D_v² φ + v · ∇_z φ`. -/
theorem integral_forwardIntegrand_green_eq_zero {lam Lam : ℝ} (hd : 1 ≤ d)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (B : FullKineticCoefficient d)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    (hφ : IsAdmissibleTest T φ) :
    ∫ q, forwardIntegrand B σ₀ φ q.1.1 q.2 ∂Γ = 0 := by
  obtain ⟨a, b, ha, hab, hbT, hz⟩ := hφ.support
  have hΛ0 : 0 ≤ Lam := hlam.le.trans hLam
  have hBΛ : ∀ σ y z i j, |B σ y z i j| ≤ Lam := fun σ y z i j =>
    HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hell σ y z).1 (hell σ y z).2 i j
  have : IsFiniteMeasure Γ := ⟨lt_of_le_of_lt (greenMeasure_mass_le K σ₀ T hT
    (Measure.dirac p) Γ hΓ) (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)⟩
  -- the mollification radii
  set r₀ : ℝ := min 1 (min (a / 2) ((T - b) / 2)) with hr₀def
  have hr₀ : 0 < r₀ := lt_min one_pos (lt_min (by linarith) (by linarith))
  have hr₀1 : r₀ ≤ 1 := min_le_left _ _
  have hr₀a : r₀ ≤ a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr₀b : r₀ ≤ (T - b) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let r : ℕ → ℝ := fun n => r₀ / ((n : ℝ) + 1)
  have hrpos : ∀ n, 0 < r n := fun n => div_pos hr₀ (by positivity)
  have hrle : ∀ n, r n ≤ r₀ := fun n => div_le_self hr₀.le (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  let bump : ℕ → ContDiffBump (0 : ℝ × EvolutionAmbientState d) := fun n =>
    ⟨r n / 2, r n, half_pos (hrpos n), half_lt_self (hrpos n)⟩
  let ρ : ℕ → ℝ × EvolutionAmbientState d → ℝ := fun n => (bump n).normed volume
  have hρ : ∀ n, IsMollifierKernel (ρ n) (r n) := fun n =>
    ⟨(bump n).contDiff_normed, (bump n).hasCompactSupport_normed, (bump n).nonneg_normed,
      (bump n).integral_normed, fun x hx => by
        refine Function.notMem_support.1 ?_
        rw [(bump n).support_normed_eq]
        intro hmem
        exact absurd (mem_ball_zero_iff.1 hmem) (not_lt.2 hx.le)⟩
  have hadm : ∀ n, IsAdmissibleTest T (fun τ y => moll (ρ n) (testValue φ) (τ, y)) := fun n =>
    isAdmissibleTest_moll hφ (hρ n) (hrpos n).le ((hrle n).trans hr₀1) hab hz
      (by linarith [hrle n]) (by linarith [hrle n])
  have hzero : ∀ n, ∫ q, forwardIntegrand B σ₀ (fun τ y => moll (ρ n) (testValue φ) (τ, y))
      q.1.1 q.2 ∂Γ = 0 := fun n =>
    (integral_forwardIntegrand_green_eq_zero_of_smooth hd hlam hLam B hB hBs hell S K hreal σ₀ T
      hT p Γ hΓ (hadm n) (contDiff_moll_test (hρ n) hφ)).2
  obtain ⟨C, hC⟩ := exists_uniform_bound_forwardIntegrand_moll B σ₀ Lam hΛ0 hBΛ hφ
  -- convergence of the mollified derivatives
  have hrOut : Tendsto (fun n => (bump n).rOut) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r₀
    simp only [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [r, bump, div_eq_mul_one_div r₀]
  have hconv : ∀ {g : ℝ × EvolutionAmbientState d → ℝ}, Continuous g → ∀ x,
      Tendsto (fun n => moll (ρ n) g x) atTop (𝓝 (g x)) := fun {g} hg x => by
    have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      (φ := bump) (l := atTop) hrOut hg x
    refine h.congr fun n => ?_
    rw [moll_eq_convolution]
  have hlim : ∀ q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d,
      Tendsto (fun n => forwardIntegrand B σ₀ (fun τ y => moll (ρ n) (testValue φ) (τ, y))
        q.1.1 q.2) atTop (𝓝 (forwardIntegrand B σ₀ φ q.1.1 q.2)) := by
    intro q
    simp only [forwardIntegrand_moll (hρ _) hφ, forwardIntegrand_eq_testSum]
    exact ((hconv hφ.timeDeriv.1 _).add (tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => (hconv (hφ.velocityHess i j).1 _).const_mul _)).add
        (tendsto_finsetSum _ fun i _ => (hconv (hφ.positionGrad i).1 _).const_mul _)
  have hmeas : ∀ n, Continuous (fun q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      forwardIntegrand B σ₀ (fun τ y => moll (ρ n) (testValue φ) (τ, y)) q.1.1 q.2) := fun n =>
    (continuous_forwardIntegrand hB σ₀ (hadm n)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hdom := tendsto_integral_of_dominated_convergence (μ := Γ) (fun _ => C)
    (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _)
    (fun n => Filter.Eventually.of_forall fun q => by
      simpa [Real.norm_eq_abs] using hC (hρ n) ((hrle n).trans hr₀1) q.1.1 q.2)
    (Filter.Eventually.of_forall hlim)
  simp only [hzero] at hdom
  exact tendsto_nhds_unique hdom tendsto_const_nhds

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
