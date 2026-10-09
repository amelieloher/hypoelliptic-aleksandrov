module

public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Representative-level `W^{1,p}`

This compatibility carrier stores concrete value and gradient representatives.
The later Banach carrier is the closed weak-gradient graph modulo a.e.
equality; the two layers intentionally serve different purposes.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

/-- Scalar `L^p` membership on a restricted domain. -/
abbrev MemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u p (volumeOn U)

/-- Coordinatewise gradient `L^p` membership, retained for exact LIH
compatibility. -/
def GradMemLpOn {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemLpOn U p (fun x => Du x i)

/-- A concrete representative and a chosen coordinate weak gradient. -/
structure W1pFunction {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memLp : MemLpOn U p toFun
  gradMemLp : GradMemLpOn U p grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} :
    CoeFun (W1pFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Representative-level membership of a concrete function in `W^{1,p}`. -/
def MemW1p {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) (u : Vec d → ℝ) : Prop :=
  ∃ v : W1pFunction U p, v.toFun = u

theorem memLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemLpOn U p u) :
    MemLpOn V p u :=
  hu.mono_measure (MeasureTheory.Measure.restrict_mono_set
    MeasureTheory.volume hVU)

theorem gradMemLpOn_mono {d : ℕ}
    {U V : Set (Vec d)} {p : ℝ≥0∞} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemLpOn U p Du) :
    GradMemLpOn V p Du := by
  intro i
  exact memLpOn_mono hVU (hDu i)

namespace W1pFunction

@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u v : W1pFunction U p}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

theorem hasWeakPartialDerivOn {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i

theorem grad_memLp {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (i : Fin d) :
    MemLpOn U p (fun x => u.grad x i) :=
  u.gradMemLp i

theorem memW1p {d : ℕ}
    {U : Set (Vec d)} {p : ℝ≥0∞} (u : W1pFunction U p) :
    MemW1p U p u.toFun :=
  ⟨u, rfl⟩

/-- Restrict a representative-level Sobolev function to an open subset. -/
def restrict {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}
    (u : W1pFunction U p) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    W1pFunction V p where
  toFun := u.toFun
  grad := u.grad
  memLp := memLpOn_mono hVU u.memLp
  gradMemLp := gradMemLpOn_mono hVU u.gradMemLp
  hasWeakGradient := u.hasWeakGradient.restrict hVOpen hVU

/-- Package a compactly supported `C¹` function as a Sobolev
representative. -/
noncomputable def ofContDiff {d : ℕ}
    {U : Set (Vec d)} (_hUOpen : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f)
    (hfSupport : HasCompactSupport f) (p : ℝ≥0∞) :
    W1pFunction U p where
  toFun := f
  grad := fun x i => (fderiv ℝ f x) (basisVec i)
  memLp := by
    have hfCont : Continuous f :=
      (hf.differentiable (by simp)).continuous
    exact (hfCont.memLp_of_hasCompactSupport hfSupport).restrict U
  gradMemLp := by
    intro i
    have hderivCont :
        Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
      simpa using
        (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    have hderivSupport :
        HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) := by
      simpa using hfSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hderivCont.memLp_of_hasCompactSupport hderivSupport).restrict U
  hasWeakGradient := HasWeakGradientOn.of_contDiff hf

end W1pFunction

end PDE
