module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNativeEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Measurable scalar jet representatives

The position axis is null. Representatives there are zero, as permitted by the exact
profile statement; all off-axis values are the actual native derivatives.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter

/-- The source position jet, with its permitted zero axis representative. -/
def scalarGx (gamma : ScalarGamma) (Lam : ℝ) (q : XV 1) : PDE.Vec 1 :=
  if q.1 0 = 0 then 0 else dx (scalarProfile gamma Lam) q

/-- The source velocity jet, with its permitted zero axis representative. -/
def scalarGv (gamma : ScalarGamma) (Lam : ℝ) (q : XV 1) : PDE.Vec 1 :=
  if q.1 0 = 0 then 0 else dv (scalarProfile gamma Lam) q

/-- The source velocity Hessian, with its permitted zero axis representative. -/
def scalarHess (gamma : ScalarGamma) (Lam : ℝ) (q : XV 1) : PDE.Mat 1 :=
  if q.1 0 = 0 then 0 else dvv (scalarProfile gamma Lam) q

/-- The axis predicate is Borel measurable on the actual native carrier. -/
theorem measurableSet_scalar_axis : MeasurableSet {q : XV 1 | q.1 0 = 0} := by
  exact measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_fst) measurable_const

/-- The selected position jet is measurable. -/
theorem measurable_scalarGx (gamma : ScalarGamma) (Lam : ℝ) :
    Measurable (scalarGx gamma Lam) := by
  apply measurable_const.ite measurableSet_scalar_axis
  exact Measurable.of_eval fun i =>
    measurable_fderiv_apply_const ℝ (scalarProfile gamma Lam) (Pi.single i 1, 0)

/-- The selected velocity jet is measurable. -/
theorem measurable_scalarGv (gamma : ScalarGamma) (Lam : ℝ) :
    Measurable (scalarGv gamma Lam) := by
  apply measurable_const.ite measurableSet_scalar_axis
  exact Measurable.of_eval fun i =>
    measurable_fderiv_apply_const ℝ (scalarProfile gamma Lam) (0, Pi.single i 1)

/-- Every entry of the selected velocity Hessian is measurable. -/
theorem measurable_scalarHess (gamma : ScalarGamma) (Lam : ℝ) (i k : Fin 1) :
    Measurable (fun q => scalarHess gamma Lam q i k) := by
  classical
  have hm : Measurable (fun q : XV 1 => if q.1 0 = 0 then (0 : ℝ) else
      fderiv ℝ (fun z => dv (scalarProfile gamma Lam) z k) q (0, Pi.single i 1)) :=
    (measurable_const (a := (0 : ℝ))).ite measurableSet_scalar_axis
      (measurable_fderiv_apply_const ℝ (fun z => dv (scalarProfile gamma Lam) z k)
        (0, Pi.single i 1))
  convert hm using 1
  funext q
  unfold scalarHess
  split_ifs <;> rfl

/-- The representative fields agree almost everywhere with the actual native selectors. -/
theorem scalarJets_eq_ae (gamma : ScalarGamma) (Lam : ℝ) :
    ∀ᵐ q ∂volume, scalarGx gamma Lam q = dx (scalarProfile gamma Lam) q ∧
      scalarGv gamma Lam q = dv (scalarProfile gamma Lam) q ∧
      scalarHess gamma Lam q = dvv (scalarProfile gamma Lam) q := by
  filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
  have hx : q.1 0 ≠ 0 := by
    intro hz
    apply hq.1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hz
  simp only [scalarGx, scalarGv, scalarHess, hx, ↓reduceIte, and_self]

/-- The selected representatives satisfy the source equation almost everywhere. -/
theorem scalarJets_equation_ae (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    ∀ᵐ q ∂volume,
      matrixContraction (scalarProfileCoefficient Lam q) (scalarHess gamma Lam q) =
        PDE.vecDot q.2 (scalarGx gamma Lam q) := by
  filter_upwards [scalarJets_eq_ae gamma Lam, scalarProfile_equation_ae gamma Lam hLam]
    with q hj he
  rw [hj.1, hj.2.2]
  exact he

/-- The position representative has the exact source homogeneous degree everywhere. -/
theorem scalarGx_homogeneous (gamma : ScalarGamma) (Lam r : ℝ) (hLam : 0 < Lam)
    (hr : 0 < r) (q : XV 1) :
    scalarGx gamma Lam (dilate r q) = Real.rpow r (3 * gamma.1 - 3) • scalarGx gamma Lam q := by
  have hxDil : (dilate r q).1 0 = 0 ↔ q.1 0 = 0 := by
    simp only [dilate, Pi.smul_apply, smul_eq_mul, mul_eq_zero,
      pow_ne_zero 3 hr.ne', false_or]
  unfold scalarGx
  by_cases hx : q.1 0 = 0
  · simp only [hxDil, hx, ↓reduceIte, smul_zero]
  · simp only [hxDil, hx, ↓reduceIte]
    funext i
    exact homogeneous_dx_identity (scalarProfile gamma Lam) (3 * gamma.1) r hr
      (scalarProfile_homogeneous gamma Lam r hr) q
      ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx).differentiableAt (by norm_num))
      ((scalarProfile_contDiffAt_off_axis gamma Lam hLam (dilate r q)
        (mt hxDil.mp hx)).differentiableAt (by norm_num)) i

/-- The velocity representative has the exact source homogeneous degree everywhere. -/
theorem scalarGv_homogeneous (gamma : ScalarGamma) (Lam r : ℝ) (hLam : 0 < Lam)
    (hr : 0 < r) (q : XV 1) :
    scalarGv gamma Lam (dilate r q) = Real.rpow r (3 * gamma.1 - 1) • scalarGv gamma Lam q := by
  have hxDil : (dilate r q).1 0 = 0 ↔ q.1 0 = 0 := by
    simp only [dilate, Pi.smul_apply, smul_eq_mul, mul_eq_zero,
      pow_ne_zero 3 hr.ne', false_or]
  unfold scalarGv
  by_cases hx : q.1 0 = 0
  · simp only [hxDil, hx, ↓reduceIte, smul_zero]
  · simp only [hxDil, hx, ↓reduceIte]
    funext i
    exact homogeneous_dv_identity (scalarProfile gamma Lam) (3 * gamma.1) r hr
      (scalarProfile_homogeneous gamma Lam r hr) q
      ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx).differentiableAt (by norm_num))
      ((scalarProfile_contDiffAt_off_axis gamma Lam hLam (dilate r q)
        (mt hxDil.mp hx)).differentiableAt (by norm_num)) i

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
