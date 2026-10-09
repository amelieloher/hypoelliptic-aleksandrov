module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise

/-!
# Localized spatial quotient smooth tests

This module bundles the cutoff-weighted forward spatial difference quotient of
a smooth compactly supported test and records its coordinate weak derivative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The localized forward quotient of a bundled smooth test, supported by the
cutoff inside the raw carrier. -/
noncomputable def localizedSpatialDifferenceQuotientWeakTest
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω where
  toFun := localizedSpatialDifferenceQuotient η k h φ
  contDiff := ContDiff.localizedSpatialDifferenceQuotient φ.contDiff η k h
  hasCompactSupport := localizedSpatialDifferenceQuotient_hasCompactSupport η k h φ
  tsupport_subset :=
    (tsupport_localizedSpatialDifferenceQuotient_subset η k h φ).trans hηΩ

/-- The bundled localized quotient has the literal pointwise value. -/
@[simp] theorem localizedSpatialDifferenceQuotientWeakTest_apply
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω) (y : PDE.Vec d) :
    localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ y =
      η y * ((φ (y + h • PDE.basisVec k) - φ y) / h) :=
  rfl

/-- The coordinate derivative of the bundled localized quotient obeys the
literal cutoff product rule. -/
theorem localizedSpatialDifferenceQuotientWeakTest_partialDeriv
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (j : Fin d) (y : PDE.Vec d) :
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ).partialDeriv j y =
      PDE.classicalGradient η.toFun y j *
          ((φ (y + h • PDE.basisVec k) - φ y) / h) +
        η y *
          ((φ.partialDeriv j (y + h • PDE.basisVec k) -
              φ.partialDeriv j y) / h) := by
  unfold PDE.WeakTestFunction.partialDeriv localizedSpatialDifferenceQuotientWeakTest
  change (fderiv ℝ (fun x : PDE.Vec d =>
    η x * ((φ (x + h • PDE.basisVec k) - φ x) / h)) y) (PDE.basisVec j) = _
  have hφshift : DifferentiableAt ℝ
      (fun x : PDE.Vec d => φ (x + h • PDE.basisVec k)) y :=
    (φ.contDiff.comp (contDiff_id.add contDiff_const)).contDiffAt.differentiableAt (by simp)
  have hφ : DifferentiableAt ℝ (φ : PDE.Vec d → ℝ) y :=
    φ.contDiff.contDiffAt.differentiableAt (by simp)
  let q : PDE.Vec d → ℝ := fun x =>
    φ (x + h • PDE.basisVec k) - φ x
  have hq : DifferentiableAt ℝ q y := by
    exact hφshift.sub hφ
  have hquotient : DifferentiableAt ℝ
      (fun x : PDE.Vec d => (φ (x + h • PDE.basisVec k) - φ x) / h) y :=
    by
      convert hq.const_smul h⁻¹ using 1
      funext x
      simp only [q, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
  rw [fderiv_fun_mul
    (η.smooth.contDiffAt.differentiableAt (by simp)) hquotient]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, PDE.classicalGradient_apply]
  have hquotientDeriv :
      (fderiv ℝ (fun x : PDE.Vec d =>
        (φ (x + h • PDE.basisVec k) - φ x) / h) y) (PDE.basisVec j) =
        (φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y) / h := by
    have hrewrite : (fun x : PDE.Vec d =>
        (φ (x + h • PDE.basisVec k) - φ x) / h) =
        fun x => h⁻¹ • q x := by
      funext x
      simp only [q, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hrewrite, fderiv_fun_const_smul hq h⁻¹]
    have hqderiv : (fderiv ℝ q y) (PDE.basisVec j) =
        φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y := by
      dsimp only [q]
      rw [fderiv_fun_sub hφshift hφ, fderiv_comp_add_right]
      rfl
    rw [ContinuousLinearMap.smul_apply, hqderiv]
    simp only [PDE.WeakTestFunction.partialDeriv,
      PDE.WeakTestFunction.partialDeriv, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hquotientDeriv]
  simp only [PDE.WeakTestFunction.partialDeriv]
  ring

/-- The coordinate product rule is the raw weak partial derivative of the
bundled localized quotient. -/
theorem localizedSpatialDifferenceQuotientWeakTest_hasWeakPartialDerivOn
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω) (j : Fin d) :
    PDE.HasWeakPartialDerivOn Ω j
      (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ)
      (fun y =>
        PDE.classicalGradient η.toFun y j *
            ((φ (y + h • PDE.basisVec k) - φ y) / h) +
          η y *
            ((φ.partialDeriv j (y + h • PDE.basisVec k) -
                φ.partialDeriv j y) / h)) := by
  have hcont : ContDiff ℝ 1 (localizedSpatialDifferenceQuotient η k h φ) :=
    (ContDiff.localizedSpatialDifferenceQuotient φ.contDiff η k h).of_le (by simp)
  have hweak := PDE.HasWeakPartialDerivOn.of_contDiff (U := Ω) (i := j) hcont
  convert hweak using 1
  · rfl
  · funext y
    simpa only [PDE.WeakTestFunction.partialDeriv,
      localizedSpatialDifferenceQuotientWeakTest] using
      (localizedSpatialDifferenceQuotientWeakTest_partialDeriv η k h φ hηΩ j y).symm

end HypoellipticAleksandrov.Parabolic.Dirichlet
