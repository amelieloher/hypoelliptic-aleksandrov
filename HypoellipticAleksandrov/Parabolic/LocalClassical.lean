module

public import HypoellipticAleksandrov.Parabolic.Operator

/-!
# Local classical parabolic predicates

This module gives the transparent local classical surfaces used by the
parabolic Harnack development.  The predicates below contain only pointwise
regularity, ellipticity, sign, and equation data; they contain no comparison
or estimate.  The `ContDiffOn ℝ 2` surface is the deliberately stronger
smooth, isotropic local `C²` classical leaf relative to the source's
`C^{1,2}` class.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped MatrixOrder

/-- A coefficient field is continuous at every point of a prescribed set. -/
def IsContinuousCoefficientOn {d : ℕ} (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ContinuousOn (coefficientAt A) U

/-- A coefficient field obeys a lower Loewner ellipticity bound on a set. -/
def HasLowerEllipticityOn {d : ℕ} (lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, lam • (1 : PDE.Mat d) ≤ coefficientAt A z

/-- A coefficient field obeys an upper Loewner ellipticity bound on a set. -/
def HasUpperEllipticityOn {d : ℕ} (Lam : ℝ) (A : CoefficientField d)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, coefficientAt A z ≤ Lam • (1 : PDE.Mat d)

/-- A scalar function is nonnegative at every point of a set. -/
def IsNonnegativeOn {d : ℕ} (q : TimeVelocity d → ℝ)
    (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, 0 ≤ q z

/-- A scalar function is a pointwise supersolution of the forward equation on a set. -/
def IsParabolicSupersolutionOn {d : ℕ} (A : CoefficientField d)
    (f u : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, f z ≤ parabolicOperator A u z

/-- A scalar function satisfies the homogeneous forward parabolic equation on a set. -/
def IsParabolicSolutionOn {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) : Prop :=
  ∀ z ∈ U, parabolicOperator A u z = 0

namespace IsContinuousCoefficientOn

/-- A local coefficient-continuity predicate gives continuity at each of its points. -/
theorem continuousWithinAt {d : ℕ} {A : CoefficientField d}
    {U : Set (TimeVelocity d)} (h : IsContinuousCoefficientOn A U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    ContinuousWithinAt (coefficientAt A) U z :=
  h z hz

/-- Coefficient continuity restricts to a smaller set. -/
theorem mono {d : ℕ} {A : CoefficientField d} {U V : Set (TimeVelocity d)}
    (h : IsContinuousCoefficientOn A U) (hVU : V ⊆ U) :
    IsContinuousCoefficientOn A V :=
  ContinuousOn.mono h hVU

/-- Global coefficient continuity gives local coefficient continuity on every set. -/
theorem of_global {d : ℕ} {A : CoefficientField d}
    (h : IsContinuousCoefficient A) (U : Set (TimeVelocity d)) :
    IsContinuousCoefficientOn A U :=
  h.continuousOn

end IsContinuousCoefficientOn

namespace HasLowerEllipticityOn

/-- A local lower ellipticity bound can be evaluated at each point of its set. -/
theorem le {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U : Set (TimeVelocity d)} (h : HasLowerEllipticityOn lam A U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    lam • (1 : PDE.Mat d) ≤ coefficientAt A z :=
  h z hz

/-- A lower ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {U V : Set (TimeVelocity d)} (h : HasLowerEllipticityOn lam A U)
    (hVU : V ⊆ U) : HasLowerEllipticityOn lam A V :=
  fun z hz => h z (hVU hz)

/-- A global lower ellipticity bound gives the corresponding local bound. -/
theorem of_global {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    (h : HasLowerEllipticity lam A) (U : Set (TimeVelocity d)) :
    HasLowerEllipticityOn lam A U :=
  fun z _ => h z.1 z.2

end HasLowerEllipticityOn

namespace HasUpperEllipticityOn

/-- A local upper ellipticity bound can be evaluated at each point of its set. -/
theorem le {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    {U : Set (TimeVelocity d)} (h : HasUpperEllipticityOn Lam A U)
    {z : TimeVelocity d} (hz : z ∈ U) :
    coefficientAt A z ≤ Lam • (1 : PDE.Mat d) :=
  h z hz

/-- An upper ellipticity bound restricts to a smaller set. -/
theorem mono {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    {U V : Set (TimeVelocity d)} (h : HasUpperEllipticityOn Lam A U)
    (hVU : V ⊆ U) : HasUpperEllipticityOn Lam A V :=
  fun z hz => h z (hVU hz)

/-- A global upper ellipticity bound gives the corresponding local bound. -/
theorem of_global {d : ℕ} {Lam : ℝ} {A : CoefficientField d}
    (h : HasUpperEllipticity Lam A) (U : Set (TimeVelocity d)) :
    HasUpperEllipticityOn Lam A U :=
  fun z _ => h z.1 z.2

end HasUpperEllipticityOn

namespace IsNonnegativeOn

/-- A local nonnegativity predicate can be evaluated at each point of its set. -/
theorem nonneg {d : ℕ} {q : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (h : IsNonnegativeOn q U)
    {z : TimeVelocity d} (hz : z ∈ U) : 0 ≤ q z :=
  h z hz

/-- Nonnegativity restricts to a smaller set. -/
theorem mono {d : ℕ} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsNonnegativeOn q U)
    (hVU : V ⊆ U) : IsNonnegativeOn q V :=
  fun z hz => h z (hVU hz)

/-- Global nonnegativity gives local nonnegativity on every set. -/
theorem of_global {d : ℕ} {q : TimeVelocity d → ℝ}
    (h : ∀ z, 0 ≤ q z) (U : Set (TimeVelocity d)) : IsNonnegativeOn q U :=
  fun z _ => h z

end IsNonnegativeOn

namespace IsParabolicSupersolutionOn

/-- A local supersolution inequality can be evaluated at each point of its set. -/
theorem le {d : ℕ} {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (h : IsParabolicSupersolutionOn A f u U)
    {z : TimeVelocity d} (hz : z ∈ U) : f z ≤ parabolicOperator A u z :=
  h z hz

/-- A supersolution inequality restricts to a smaller set. -/
theorem mono {d : ℕ} {A : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsParabolicSupersolutionOn A f u U)
    (hVU : V ⊆ U) : IsParabolicSupersolutionOn A f u V :=
  fun z hz => h z (hVU hz)

end IsParabolicSupersolutionOn

namespace IsParabolicSolutionOn

/-- A local homogeneous equation can be evaluated at each point of its set. -/
theorem eq_zero {d : ℕ} {A : CoefficientField d} {u : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (h : IsParabolicSolutionOn A u U)
    {z : TimeVelocity d} (hz : z ∈ U) : parabolicOperator A u z = 0 :=
  h z hz

/-- A homogeneous equation restricts to a smaller set. -/
theorem mono {d : ℕ} {A : CoefficientField d} {u : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} (h : IsParabolicSolutionOn A u U)
    (hVU : V ⊆ U) : IsParabolicSolutionOn A u V :=
  fun z hz => h z (hVU hz)

/-- A homogeneous solution is a zero-source subsolution in the orientation. -/
theorem isParabolicSubsolutionOn {d : ℕ} {A : CoefficientField d}
    {u : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)}
    (h : IsParabolicSolutionOn A u U) :
    IsParabolicSubsolutionOn A (fun _ => 0) u U :=
  fun z hz => le_of_eq (h z hz)

/-- A homogeneous solution is a zero-source supersolution. -/
theorem isParabolicSupersolutionOn {d : ℕ} {A : CoefficientField d}
    {u : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)}
    (h : IsParabolicSolutionOn A u U) :
    IsParabolicSupersolutionOn A (fun _ => 0) u U :=
  fun z hz => ge_of_eq (h z hz)

end IsParabolicSolutionOn

/-- A globally `C²` scalar function is `C²` on every prescribed set. -/
theorem contDiffOn_of_global {d : ℕ} {q : TimeVelocity d → ℝ}
    (h : ContDiff ℝ 2 q) (U : Set (TimeVelocity d)) : ContDiffOn ℝ 2 q U :=
  h.contDiffOn

/-- On an open set, local `C²` regularity gives pointwise `C²` regularity. -/
theorem contDiffAt_of_contDiffOn_of_isOpen {d : ℕ} {q : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    {z : TimeVelocity d} (hz : z ∈ U) : ContDiffAt ℝ 2 q z :=
  (hq z hz).contDiffAt (hU.mem_nhds hz)

/-- On an open set, local `C²` regularity makes the velocity Hessian symmetric. -/
theorem velocityHessian_isSymm_of_contDiffOn {d : ℕ} {q : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    {z : TimeVelocity d} (hz : z ∈ U) : (velocityHessian q z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  simpa [velocityHessian] using
    ((contDiffAt_of_contDiffOn_of_isOpen hU hq hz).isSymmSndFDerivAt (by norm_num)).eq
      ((0 : ℝ), Pi.single j 1) ((0 : ℝ), Pi.single i 1)

/-- On an open set, the local trace form of the forward parabolic operator
follows from local `C²`. -/
theorem parabolicOperator_eq_timeDerivative_sub_trace_of_contDiffOn
    {d : ℕ} {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U) (A : CoefficientField d)
    {z : TimeVelocity d} (hz : z ∈ U) :
    parabolicOperator A q z =
      timeDerivative q z - (coefficientAt A z * velocityHessian q z).trace := by
  rw [parabolicOperator_apply,
    HypoellipticAleksandrov.matrixContraction_eq_trace_mul_of_isSymm _ _
      (velocityHessian_isSymm_of_contDiffOn hU hq hz)]

/-- Negation reverses the forward parabolic operator. -/
theorem parabolicOperator_neg {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    parabolicOperator A (fun y => -u y) z = -parabolicOperator A u z := by
  have hfirst : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y := by
    funext y
    exact fderiv_fun_neg
  have htime : timeDerivative (fun y => -u y) z = -timeDerivative u z := by
    unfold timeDerivative
    simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  have hhessian :
      velocityHessian (fun y => -u y) z = -velocityHessian u z := by
    ext i j
    unfold velocityHessian
    rw [hfirst, fderiv_fun_neg]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian,
    HypoellipticAleksandrov.matrixContraction_neg_right]
  ring

/-- Adding a constant preserves the forward parabolic operator. -/
theorem parabolicOperator_add_const {d : ℕ} (A : CoefficientField d)
    (u : TimeVelocity d → ℝ) (c : ℝ) (z : TimeVelocity d) :
    parabolicOperator A (fun y => u y + c) z = parabolicOperator A u z := by
  have hfirst : fderiv ℝ (fun y => u y + c) = fderiv ℝ u := by
    funext y
    exact fderiv_add_const c
  have htime : timeDerivative (fun y => u y + c) z = timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_add_const]
  have hhessian :
      velocityHessian (fun y => u y + c) z = velocityHessian u z := by
    unfold velocityHessian
    rw [hfirst]
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian]

namespace IsParabolicSolutionOn

/-- Negating a homogeneous local solution preserves its homogeneous equation. -/
theorem neg {d : ℕ} {A : CoefficientField d} {u : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (h : IsParabolicSolutionOn A u U) :
    IsParabolicSolutionOn A (fun z => -u z) U :=
  fun z hz => by rw [parabolicOperator_neg, h z hz, neg_zero]

/-- Adding a constant to a homogeneous local solution preserves its homogeneous equation. -/
theorem add_const {d : ℕ} {A : CoefficientField d} {u : TimeVelocity d → ℝ}
    {U : Set (TimeVelocity d)} (h : IsParabolicSolutionOn A u U) (c : ℝ) :
    IsParabolicSolutionOn A (fun z => u z + c) U :=
  fun z hz => by rw [parabolicOperator_add_const, h z hz]

end IsParabolicSolutionOn

/-- The transparent local nonnegative classical solution surface for the
Harnack leaf.  Its `ContDiffOn ℝ 2` assumption deliberately selects the
stronger smooth, isotropic local `C²` leaf relative to the source's
`C^{1,2}` class. -/
def IsLocalClassicalSolutionOn (d : ℕ) (B : CoefficientField d)
    (q : TimeVelocity d → ℝ) (U : Set (TimeVelocity d)) (lam Lam : ℝ) : Prop :=
  IsContinuousCoefficientOn B U ∧
    ContDiffOn ℝ 2 q U ∧
    IsNonnegativeOn q U ∧
    HasLowerEllipticityOn lam B U ∧
    HasUpperEllipticityOn Lam B U ∧
    IsParabolicSolutionOn B q U

namespace IsLocalClassicalSolutionOn

/-- A local classical solution has continuous coefficients on its domain. -/
theorem continuousCoefficientOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) :
    IsContinuousCoefficientOn B U :=
  h.1

/-- A local classical solution is `C²` on its domain. -/
theorem contDiffOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : ContDiffOn ℝ 2 q U :=
  h.2.1

/-- A local classical solution is nonnegative on its domain. -/
theorem nonnegativeOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : IsNonnegativeOn q U :=
  h.2.2.1

/-- A local classical solution obeys its lower ellipticity bound on its domain. -/
theorem lowerEllipticityOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : HasLowerEllipticityOn lam B U :=
  h.2.2.2.1

/-- A local classical solution obeys its upper ellipticity bound on its domain. -/
theorem upperEllipticityOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : HasUpperEllipticityOn Lam B U :=
  h.2.2.2.2.1

/-- A local classical solution satisfies the homogeneous equation on its domain. -/
theorem solutionOn {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) : IsParabolicSolutionOn B q U :=
  h.2.2.2.2.2

/-- A local classical solution is nonnegative at each point of its domain. -/
theorem nonneg {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam)
    {z : TimeVelocity d} (hz : z ∈ U) : 0 ≤ q z :=
  h.nonnegativeOn.nonneg hz

/-- A local classical solution obeys both ellipticity bounds at each point of its domain. -/
theorem ellipticity {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam)
    {z : TimeVelocity d} (hz : z ∈ U) :
    lam • (1 : PDE.Mat d) ≤ coefficientAt B z ∧
      coefficientAt B z ≤ Lam • (1 : PDE.Mat d) :=
  ⟨h.lowerEllipticityOn.le hz, h.upperEllipticityOn.le hz⟩

/-- A local classical solution satisfies the homogeneous equation at each point of its domain. -/
theorem operator_eq_zero {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam)
    {z : TimeVelocity d} (hz : z ∈ U) : parabolicOperator B q z = 0 :=
  h.solutionOn.eq_zero hz

/-- Local classical data restricts to every smaller domain. -/
theorem mono {d : ℕ} {B : CoefficientField d} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} {lam Lam : ℝ}
    (h : IsLocalClassicalSolutionOn d B q U lam Lam) (hVU : V ⊆ U) :
    IsLocalClassicalSolutionOn d B q V lam Lam :=
  ⟨h.continuousCoefficientOn.mono hVU, h.contDiffOn.mono hVU,
    h.nonnegativeOn.mono hVU, h.lowerEllipticityOn.mono hVU,
    h.upperEllipticityOn.mono hVU, h.solutionOn.mono hVU⟩

end IsLocalClassicalSolutionOn

end HypoellipticAleksandrov.Parabolic
