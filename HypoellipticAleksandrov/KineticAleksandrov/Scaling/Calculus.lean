module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Affine
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The scaled transported operator (companion paper, (2.11))

For a kinetic affine scaling `Φ` and a function `u` that is `C²` near `Φ p`, the transported
forward operator of the rescaled data applied to `u ∘ Φ` is `a` times the original operator
applied to `u`:
`L̂ (u ∘ Φ) p = a · L u (Φ p)`.  For the source scaling `a = r²` this is
`L u = r⁻² (∂_τ + B_r : D_Y² + b_r · ∇_Z) U`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped Topology

variable {d : ℕ}

/-- The raw coordinates `(σ, (y, z))` of a kinetic point. -/
def rawPoint (p : KineticPoint d) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (p.time, (p.position, p.velocity))

/-- Hessian scaling for an affine change of the slice variable. -/
theorem sliceHessian_affine {g : PDE.Vec d → ℝ} {y₀ : PDE.Vec d} {c : ℝ} {Y : PDE.Vec d}
    (hg : ContDiffAt ℝ 2 g (y₀ + c • Y)) :
    sliceHessian (fun y => g (y₀ + c • y)) Y = c ^ 2 • sliceHessian g (y₀ + c • Y) := by
  set A : PDE.Vec d → PDE.Vec d := fun y => y₀ + c • y with hAdef
  have hAcd : ContDiff ℝ (⊤ : ℕ∞) A := by
    rw [hAdef]
    fun_prop
  have hA : ∀ y, HasFDerivAt A (c • (ContinuousLinearMap.id ℝ (PDE.Vec d))) y := by
    intro y
    have h1 : HasFDerivAt (fun x : PDE.Vec d => y₀ + c • x)
        (c • ContinuousLinearMap.id ℝ (PDE.Vec d)) y :=
      ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul c).const_add y₀
    exact h1
  have hgA : ContDiffAt ℝ 2 (fun y => g (A y)) Y :=
    hg.comp Y (hAcd.contDiffAt.of_le (by norm_cast))
  have hfinite : (2 : WithTop ℕ∞) ≠ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) := by
    norm_cast
  have hlocal := hg.eventually hfinite
  have hev : ∀ᶠ y in 𝓝 Y, fderiv ℝ (fun y => g (A y)) y = c • fderiv ℝ g (A y) := by
    filter_upwards [(hA Y).continuousAt.tendsto.eventually hlocal] with y hy
    change fderiv ℝ (g ∘ A) y = _
    rw [fderiv_comp y (hy.differentiableAt (by norm_num)) (hA y).differentiableAt,
      (hA y).fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) (A Y) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ g (A y))
      ((fderiv ℝ (fderiv ℝ g) (A Y)).comp (c • (ContinuousLinearMap.id ℝ (PDE.Vec d)))) Y :=
    hd2.hasFDerivAt.comp Y (hA Y)
  have hF := (hc.const_smul c).congr_of_eventuallyEq hev
  ext i j
  change sliceHessian (fun y => g (A y)) Y i j = c ^ 2 * sliceHessian g (A Y) i j
  rw [sliceHessian_apply_eq_sndFDeriv hgA, sliceHessian_apply_eq_sndFDeriv hg, hF.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

/-- Time derivative at a point of differentiability of the raw lift. -/
theorem kineticTimeDerivative_eq_fderiv {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint p)) :
    kineticTimeDerivative u p = fderiv ℝ (rawLift u) (rawPoint p) (1, (0, 0)) := by
  have hcurve : HasDerivAt (fun r : ℝ => ((r, (p.position, p.velocity)) :
      ℝ × (PDE.Vec d × PDE.Vec d))) ((1 : ℝ), ((0 : PDE.Vec d × PDE.Vec d))) p.time :=
    (hasDerivAt_id p.time).prodMk (hasDerivAt_const p.time (p.position, p.velocity))
  exact (hu.hasFDerivAt.comp_hasDerivAt p.time hcurve).deriv

/-- The velocity slice is differentiable, with the derivative of the raw lift. -/
theorem hasFDerivAt_velocitySlice {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint p)) :
    HasFDerivAt (fun v : PDE.Vec d => u ⟨p.time, p.position, v⟩)
      ((fderiv ℝ (rawLift u) (rawPoint p)).comp
        ((0 : PDE.Vec d →L[ℝ] ℝ).prod ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod
          (ContinuousLinearMap.id ℝ (PDE.Vec d))))) p.velocity := by
  have hι : HasFDerivAt (fun v : PDE.Vec d => ((p.time, (p.position, v)) :
      ℝ × (PDE.Vec d × PDE.Vec d)))
      ((0 : PDE.Vec d →L[ℝ] ℝ).prod ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod
        (ContinuousLinearMap.id ℝ (PDE.Vec d)))) p.velocity :=
    (hasFDerivAt_const p.time p.velocity).prodMk
      ((hasFDerivAt_const p.position p.velocity).prodMk (hasFDerivAt_id p.velocity))
  exact hu.hasFDerivAt.comp p.velocity hι

/-- The velocity slice has the directional derivative of the raw lift. -/
theorem fderiv_velocitySlice {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint p)) (x : PDE.Vec d) :
    fderiv ℝ (fun v : PDE.Vec d => u ⟨p.time, p.position, v⟩) p.velocity x =
      fderiv ℝ (rawLift u) (rawPoint p) (0, (0, x)) := by
  rw [(hasFDerivAt_velocitySlice hu).fderiv]
  simp

/-- The dot product with the velocity gradient is a directional derivative. -/
theorem vecDot_kineticVelocityGradient {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint p)) (x : PDE.Vec d) :
    PDE.vecDot x (kineticVelocityGradient u p) =
      fderiv ℝ (rawLift u) (rawPoint p) (0, (0, x)) := by
  rw [← fderiv_velocitySlice hu x, PDE.fderiv_apply_eq_vecDot_classicalGradient]
  rw [PDE.vecDot_comm]
  rfl

theorem vecDot_sub_left (x y z : PDE.Vec d) :
    PDE.vecDot (x - y) z = PDE.vecDot x z - PDE.vecDot y z := by
  simp only [PDE.vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem vecDot_smul_left (c : ℝ) (x z : PDE.Vec d) :
    PDE.vecDot (c • x) z = c * PDE.vecDot x z := by
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem vecDot_kineticVelocityGradient_eq_fderiv (u : KineticPoint d → ℝ) (p : KineticPoint d)
    (x : PDE.Vec d) :
    PDE.vecDot x (kineticVelocityGradient u p) =
      fderiv ℝ (fun v : PDE.Vec d => u ⟨p.time, p.position, v⟩) p.velocity x := by
  rw [PDE.vecDot_comm]
  exact (PDE.fderiv_apply_eq_vecDot_classicalGradient _ _ _).symm

namespace KineticAffineScaling

variable (Φ : KineticAffineScaling d) {u : KineticPoint d → ℝ} {p : KineticPoint d}

/-- The raw lift of `u ∘ Φ` is the raw lift of `u` composed with the raw map. -/
theorem rawLift_comp_point : rawLift (fun p => u (Φ.point p)) = fun q => rawLift u (Φ.raw q) :=
  rfl

/-- The time derivative of `u ∘ Φ`: `a (∂_σ u + w · ∇_z u)`, as a directional derivative. -/
theorem kineticTimeDerivative_comp_point
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint (Φ.point p))) :
    kineticTimeDerivative (fun p => u (Φ.point p)) p =
      fderiv ℝ (rawLift u) (rawPoint (Φ.point p)) (Φ.a, (0, Φ.a • Φ.w)) := by
  have hid : HasDerivAt (fun r : ℝ => Φ.a * r) Φ.a p.time := by
    simpa using HasDerivAt.const_mul Φ.a (hasDerivAt_id p.time)
  have h1 : HasDerivAt (fun r : ℝ => Φ.σ₀ + Φ.a * r) Φ.a p.time := hid.const_add Φ.σ₀
  have h3 : HasDerivAt (fun r : ℝ => Φ.z₀ + (Φ.a * r) • Φ.w + Φ.e • p.velocity)
      (Φ.a • Φ.w) p.time := by
    exact ((HasDerivAt.smul_const hid Φ.w).const_add Φ.z₀).add_const (Φ.e • p.velocity)
  have h2 : HasDerivAt (fun _ : ℝ => Φ.y₀ + Φ.c • p.position) 0 p.time :=
    hasDerivAt_const _ _
  have h23 : HasDerivAt (fun r : ℝ => (Φ.y₀ + Φ.c • p.position,
      Φ.z₀ + (Φ.a * r) • Φ.w + Φ.e • p.velocity)) (0, Φ.a • Φ.w) p.time := h2.prodMk h3
  have hcurve : HasDerivAt (fun r : ℝ => Φ.raw (r, (p.position, p.velocity)))
      (Φ.a, (0, Φ.a • Φ.w)) p.time :=
    h1.prodMk h23
  exact (hu.hasFDerivAt.comp_hasDerivAt p.time hcurve).deriv

/-- The velocity gradient of `u ∘ Φ` scales by `e`, tested against any vector. -/
theorem vecDot_kineticVelocityGradient_comp_point
    (hu : DifferentiableAt ℝ (rawLift u) (rawPoint (Φ.point p))) (x : PDE.Vec d) :
    PDE.vecDot x (kineticVelocityGradient (fun p => u (Φ.point p)) p) =
      Φ.e * PDE.vecDot x (kineticVelocityGradient u (Φ.point p)) := by
  have hs := hasFDerivAt_velocitySlice hu
  have hT : HasFDerivAt (Φ.transport p.time)
      (Φ.e • ContinuousLinearMap.id ℝ (PDE.Vec d)) p.velocity := by
    have h1 : HasFDerivAt (fun v : PDE.Vec d => (Φ.z₀ + (Φ.a * p.time) • Φ.w) + Φ.e • v)
        (Φ.e • ContinuousLinearMap.id ℝ (PDE.Vec d)) p.velocity :=
      ((hasFDerivAt_id (𝕜 := ℝ) p.velocity).const_smul Φ.e).const_add _
    exact h1
  have hc := hs.comp p.velocity hT
  rw [vecDot_kineticVelocityGradient_eq_fderiv]
  have hfun : (fun v : PDE.Vec d => (fun p => u (Φ.point p)) ⟨p.time, p.position, v⟩) =
      (fun v : PDE.Vec d => u ⟨(Φ.point p).time, (Φ.point p).position, v⟩) ∘
        Φ.transport p.time := rfl
  rw [hfun, hc.fderiv, vecDot_kineticVelocityGradient hu x]
  simp

/-- The diffused Hessian of `u ∘ Φ` is `c²` times that of `u`. -/
theorem diffusedHessian_comp_point
    (hu : ContDiffAt ℝ 2 (rawLift u) (rawPoint (Φ.point p))) :
    diffusedHessian (fun p => u (Φ.point p)) p = Φ.c ^ 2 • diffusedHessian u (Φ.point p) := by
  rw [diffusedHessian_eq_sliceHessian, diffusedHessian_eq_sliceHessian]
  have hg : ContDiffAt ℝ 2 (fun y : PDE.Vec d => u ⟨(Φ.point p).time, y,
      (Φ.point p).velocity⟩) (Φ.y₀ + Φ.c • p.position) := by
    have hι : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec d => ((Φ.time p.time, (y,
        Φ.transport p.time p.velocity)) : ℝ × (PDE.Vec d × PDE.Vec d))) := by
      fun_prop
    exact ContDiffAt.comp (g := rawLift u) (Φ.y₀ + Φ.c • p.position) hu
      (hι.contDiffAt.of_le (by norm_cast))
  exact sliceHessian_affine (g := fun y : PDE.Vec d => u ⟨(Φ.point p).time, y,
    (Φ.point p).velocity⟩) (y₀ := Φ.y₀) (c := Φ.c) (Y := p.position) hg

/-- **Scaled operator** (companion paper, (2.11)): the transported forward operator of the
rescaled data on `u ∘ Φ` is `a` times the original operator on `u`, at every point where
`u` is `C²`. -/
theorem transportedForwardOperator_comp_point (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d)
    (hu : ContDiffAt ℝ 2 (rawLift u) (rawPoint (Φ.point p))) :
    transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p =
      Φ.a * transportedForwardOperator B b u (Φ.point p) := by
  have hd : DifferentiableAt ℝ (rawLift u) (rawPoint (Φ.point p)) :=
    hu.differentiableAt (by norm_num)
  have hlin : fderiv ℝ (rawLift u) (rawPoint (Φ.point p)) (Φ.a, (0, Φ.a • Φ.w)) =
      Φ.a * fderiv ℝ (rawLift u) (rawPoint (Φ.point p)) (1, (0, 0)) +
        Φ.a * fderiv ℝ (rawLift u) (rawPoint (Φ.point p)) (0, (0, Φ.w)) := by
    have : ((Φ.a, (0, Φ.a • Φ.w)) : ℝ × (PDE.Vec d × PDE.Vec d)) =
        Φ.a • ((1, (0, 0)) : ℝ × (PDE.Vec d × PDE.Vec d)) +
          Φ.a • ((0, (0, Φ.w)) : ℝ × (PDE.Vec d × PDE.Vec d)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul]
    rfl
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply,
    kineticTimeDerivative_comp_point Φ hd, hlin, kineticTimeDerivative_eq_fderiv hd,
    diffusedHessian_comp_point Φ hu]
  have hcoef : fullKineticCoefficientAt (Φ.coefficient B) p =
      (Φ.a / Φ.c ^ 2) • fullKineticCoefficientAt B (Φ.point p) := rfl
  rw [hcoef, matrixContraction_smul_left, matrixContraction_smul_right]
  have hdrift : Φ.drift b p.position =
      (Φ.a / Φ.e) • (b (Φ.point p).position - Φ.w) := rfl
  rw [hdrift, vecDot_smul_left, vecDot_sub_left,
    vecDot_kineticVelocityGradient_comp_point Φ hd,
    vecDot_kineticVelocityGradient_comp_point Φ hd, vecDot_kineticVelocityGradient hd Φ.w]
  have hc : Φ.c ≠ 0 := Φ.c_pos.ne'
  have he : Φ.e ≠ 0 := Φ.e_pos.ne'
  field_simp
  ring

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
