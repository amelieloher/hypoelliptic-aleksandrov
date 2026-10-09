module

public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.W1p.Algebra
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Smooth multipliers on representative-level `W^{1,p}`

A smooth scalar multiplier preserves `W^{1,p}` when its value and coordinate
gradient are essentially bounded on the domain. The stored weak gradient is
the exact product-rule expression

`φ Du + u Dφ`.

The exponent hypothesis `1 ≤ p` is needed only to obtain the local
integrability required by the raw distributional product rule.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Multiply a representative-level Sobolev function by a smooth multiplier
whose value and first coordinate derivatives are essentially bounded on the
domain. -/
noncomputable def mulContDiffMemLpTop [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    W1pFunction U p where
  toFun := fun x => φ x * u x
  grad := fun x =>
    φ x • u.grad x + u x • classicalGradient φ x
  memLp := by
    simpa only [mul_comm] using u.memLp.fun_mul hφTop
  gradMemLp := by
    intro i
    have hfirst :
        MemLpOn U p (fun x => φ x * u.grad x i) := by
      simpa only [mul_comm] using
        (u.gradMemLp i).fun_mul hφTop
    have hsecond :
        MemLpOn U p
          (fun x => u x * classicalGradient φ x i) :=
      by
        simpa only [mul_comm] using
          u.memLp.fun_mul (hDφTop i)
    exact hfirst.add hsecond
  hasWeakGradient := by
    convert u.hasWeakGradient.mul_contDiff hφ
      u.locallyIntegrable_toFun u.locallyIntegrable_grad using 1
    funext x i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      classicalGradient_apply]

@[simp]
theorem mulContDiffMemLpTop_toFun [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    (u.mulContDiffMemLpTop hφ hφTop hDφTop).toFun =
      fun x => φ x * u x :=
  rfl

@[simp]
theorem mulContDiffMemLpTop_grad [Fact (1 ≤ p)]
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x :=
  rfl

/-- Exact multiplier cost for the value component. -/
theorem eLpNormOn_mulContDiffMemLpTop_toFun_le
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i)) :
    eLpNormOn U p
        (u.mulContDiffMemLpTop hφ hφTop hDφTop).toFun ≤
      eLpNormOn U ∞ φ * eLpNormOn U p u.toFun := by
  exact
    MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (f := u.toFun) p hφTop.aestronglyMeasurable

/-- Coordinatewise gradient cost of a smooth `L∞` multiplier. Both terms in
the product rule remain visible. -/
theorem eLpNormOn_mulContDiffMemLpTop_grad_coord_le
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφTop : MemLpOn U ∞ φ)
    (hDφTop : ∀ i : Fin d,
      MemLpOn U ∞
        (fun x => classicalGradient φ x i))
    (i : Fin d) :
    eLpNormOn U p
        (fun x =>
          (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i) ≤
      eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) +
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
  let first : Vec d → ℝ :=
    fun x => φ x * u.grad x i
  let second : Vec d → ℝ :=
    fun x => u x * classicalGradient φ x i
  have hfirstMem : MemLpOn U p first := by
    simpa only [first, mul_comm] using
      (u.gradMemLp i).fun_mul hφTop
  have hsecondMem : MemLpOn U p second := by
    simpa only [second, mul_comm] using
      u.memLp.fun_mul (hDφTop i)
  have hfirstBound :
      eLpNormOn U p first ≤
        eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) := by
    exact
      MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
        (f := fun x => u.grad x i) p hφTop.aestronglyMeasurable
  have hsecondBound :
      eLpNormOn U p second ≤
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
    calc
      eLpNormOn U p second =
          eLpNormOn U p
            (fun x => classicalGradient φ x i * u x) := by
        apply MeasureTheory.eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [second, mul_comm]
      _ ≤ eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun := by
        exact
          MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
            (f := u.toFun) p (hDφTop i).aestronglyMeasurable
  calc
    eLpNormOn U p
        (fun x =>
          (u.mulContDiffMemLpTop hφ hφTop hDφTop).grad x i) =
        eLpNormOn U p (first + second) := by
      rfl
    _ ≤ eLpNormOn U p first + eLpNormOn U p second := by
      exact MeasureTheory.eLpNorm_add_le Fact.out
    _ ≤ eLpNormOn U ∞ φ *
          eLpNormOn U p (fun x => u.grad x i) +
        eLpNormOn U ∞
            (fun x => classicalGradient φ x i) *
          eLpNormOn U p u.toFun :=
      add_le_add hfirstBound hsecondBound

/-- Compact support supplies the required `L∞` hypotheses automatically. -/
noncomputable def mulContDiffHasCompactSupport
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    W1pFunction U p := by
  have hφTop : MemLpOn U ∞ φ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U
  have hDφTop :
      ∀ i : Fin d,
        MemLpOn U ∞
          (fun x => classicalGradient φ x i) := by
    intro i
    have hDφCont :
        Continuous (fun x => classicalGradient φ x i) := by
      simpa only [classicalGradient_apply] using
        (hφ.continuous_fderiv (by simp)).clm_apply
          continuous_const
    have hDφCompact :
        HasCompactSupport
          (fun x => classicalGradient φ x i) := by
      simpa only [classicalGradient_apply] using
        hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact
      (hDφCont.memLp_of_hasCompactSupport hDφCompact).restrict U
  exact u.mulContDiffMemLpTop hφ hφTop hDφTop

@[simp]
theorem mulContDiffHasCompactSupport_toFun
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).toFun =
      fun x => φ x * u x := by
  simp only [mulContDiffHasCompactSupport,
    mulContDiffMemLpTop_toFun]

@[simp]
theorem mulContDiffHasCompactSupport_grad
    [Fact (1 ≤ p)] (u : W1pFunction U p)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).grad =
      fun x =>
        φ x • u.grad x + u x • classicalGradient φ x := by
  simp only [mulContDiffHasCompactSupport,
    mulContDiffMemLpTop_grad]

end W1pFunction

end PDE
