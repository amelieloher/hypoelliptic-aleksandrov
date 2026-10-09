module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Reflection of kinetic cylinders, coefficients and slice jets -/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder Matrix.Norms.Elementwise ContDiff

/-- Reflection fixes relative velocity and reverses relative position. -/
theorem kineticReflection_relative {d : ℕ} (P₀ P : KineticPoint d) :
    relativeVelocity (kineticReflection P₀) (kineticReflection P) =
        relativeVelocity P₀ P ∧
      relativePosition (kineticReflection P₀) (kineticReflection P) =
        -relativePosition P₀ P := by
  constructor
  · rfl
  · ext i
    simp [relativePosition, kineticReflection]
    ring

/-- Reflection is continuous in the existing product topology. -/
theorem continuous_kineticReflection (d : ℕ) :
    Continuous (kineticReflection (d := d)) :=
  KineticPoint.continuous_mk continuous_time.neg continuous_position.neg continuous_velocity

/-- The reflection as a homeomorphism of the existing kinetic carrier. -/
def kineticReflectionHomeomorph (d : ℕ) : KineticPoint d ≃ₜ KineticPoint d where
  toFun := kineticReflection
  invFun := kineticReflection
  left_inv := kineticReflection_involutive
  right_inv := kineticReflection_involutive
  continuous_toFun := continuous_kineticReflection d
  continuous_invFun := continuous_kineticReflection d

private theorem neg_ball {d : ℕ} (x y : PDE.Vec d) (r : ℝ) :
    -x ∈ PDE.euclideanBall (-y) r ↔ x ∈ PDE.euclideanBall y r := by
  change PDE.vecNormSq (-x - -y) < r ^ 2 ↔ PDE.vecNormSq (x-y) < r ^ 2
  rw [show -x - -y = -(x-y) by abel, PDE.vecNormSq_neg]

private theorem neg_sphere {d : ℕ} (x y : PDE.Vec d) (r : ℝ) :
    -x ∈ PDE.euclideanSphere (-y) r ↔ x ∈ PDE.euclideanSphere y r := by
  change PDE.vecNormSq (-x - -y) = r ^ 2 ↔ PDE.vecNormSq (x-y) = r ^ 2
  rw [show -x - -y = -(x-y) by abel, PDE.vecNormSq_neg]

private theorem reflected_mem_forward {d : ℕ}
    (P₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    kineticReflection P ∈ forwardCylinder (kineticReflection P₀) R hR ↔
      P ∈ backwardCylinder P₀ R := by
  rw [mem_forwardCylinder_iff, mem_backwardCylinder_iff]
  rw [(kineticReflection_relative P₀ P).2]
  have hb := neg_ball (relativePosition P₀ P) (0 : PDE.Vec d) (R ^ 3)
  simp only [neg_zero] at hb
  simp only [kineticReflection, neg_lt_neg_iff, hb]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> refine ⟨?_,?_,h3,h4⟩ <;> linarith

/-- Reflection maps the backward cylinder onto the source forward cylinder. -/
theorem kineticReflection_image_backwardCylinder {d : ℕ}
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    kineticReflection '' backwardCylinder P₀ R =
      forwardCylinder (kineticReflection P₀) R hR := by
  ext P
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    exact (reflected_mem_forward P₀ Q R hR).2 hQ
  · intro hP
    refine ⟨kineticReflection P, ?_, kineticReflection_involutive P⟩
    apply (reflected_mem_forward P₀ (kineticReflection P) R hR).1
    rw [kineticReflection_involutive P]
    exact hP

/-- Reflection maps the prescribed kinetic boundary onto the exit boundary. -/
theorem kineticReflection_image_kineticBoundary {d : ℕ}
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    kineticReflection '' kineticBoundary P₀ R =
      exitBoundary (kineticReflection P₀) R hR := by
  have hc : kineticReflection '' closure (backwardCylinder P₀ R) =
      closure (forwardCylinder (kineticReflection P₀) R hR) := by
    rw [← kineticReflection_image_backwardCylinder P₀ R hR]
    exact (kineticReflectionHomeomorph d).image_closure _
  have hmem : ∀ P, kineticReflection P ∈
      exitBoundary (kineticReflection P₀) R hR ↔ P ∈ kineticBoundary P₀ R := by
    intro P
    rw [mem_exitBoundary_iff, mem_kineticBoundary_iff, ← hc]
    have hi : kineticReflection P ∈ kineticReflection '' closure (backwardCylinder P₀ R) ↔
        P ∈ closure (backwardCylinder P₀ R) := by
      exact kineticReflection_involutive.injective.mem_set_image
    rw [hi, (kineticReflection_relative P₀ P).1,
      (kineticReflection_relative P₀ P).2]
    have hs := neg_sphere (relativePosition P₀ P) (0 : PDE.Vec d) (R ^ 3)
    simp only [neg_zero] at hs
    have hd : PDE.vecDot (relativeVelocity P₀ P) (-relativePosition P₀ P) =
        -PDE.vecDot (relativeVelocity P₀ P) (relativePosition P₀ P) := by
      simp [PDE.vecDot, Finset.sum_neg_distrib]
    have ht : -P.time = -P₀.time + R ^ 2 ↔ P.time = P₀.time - R ^ 2 := by
      constructor <;> intro h <;> linarith
    simp only [kineticReflection, hs, hd, neg_nonneg, ht]
  ext P
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    exact (hmem Q).2 hQ
  · intro hP
    refine ⟨kineticReflection P, ?_, kineticReflection_involutive P⟩
    apply (hmem (kineticReflection P)).1
    rw [kineticReflection_involutive P]
    exact hP

/-- Reflection preserves unnormalised product Lebesgue measure. -/
theorem measurePreserving_kineticReflection (d : ℕ) :
    MeasurePreserving (kineticReflection (d := d)) volume volume := by
  let e := (KineticPoint.homeomorphProd d).toMeasurableEquiv
  have he : MeasurePreserving e volume volume := KineticPoint.measurePreserving_equivProd d
  have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    ((Measure.measurePreserving_neg (volume : Measure (PDE.Vec d))).prod
      (MeasurePreserving.id (volume : Measure (PDE.Vec d))))
  exact (he.symm e).comp (hp.comp he)

private theorem coefficientTimeReflection_preserving (d : ℕ) :
    MeasurePreserving (fun z : TimeVelocity d => (-z.1,z.2)) volume volume :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure (PDE.Vec d)))

/-- Source coefficient reflection preserves the Borel coefficient class. -/
theorem isBorelCoefficient_kineticReflectedCoefficient {d : ℕ}
    (A : CoefficientField d) (hA : IsBorelCoefficient A) :
    IsBorelCoefficient (kineticReflectedCoefficient A) :=
  hA.comp ((continuous_fst.neg.prodMk continuous_snd).measurable)

/-- Source coefficient reflection preserves pointwise symmetry. -/
theorem isSymmetricCoefficient_kineticReflectedCoefficient {d : ℕ}
    (A : CoefficientField d) (hA : IsSymmetricCoefficient A) :
    IsSymmetricCoefficient (kineticReflectedCoefficient A) := fun s v => hA (-s) v

/-- Source coefficient reflection preserves almost-everywhere ellipticity bounds. -/
theorem ellipticityAE_kineticReflectedCoefficient {d : ℕ}
    (A : CoefficientField d) (lam Lam : ℝ)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    HasLowerEllipticityAE lam (kineticReflectedCoefficient A) ∧
      HasUpperEllipticityAE Lam (kineticReflectedCoefficient A) := by
  exact ⟨(coefficientTimeReflection_preserving d).quasiMeasurePreserving.ae hlo,
    (coefficientTimeReflection_preserving d).quasiMeasurePreserving.ae hhi⟩

/-- Source time reflection preserves the existing C-infinity coefficient class. -/
theorem isSmoothCoefficient_kineticReflectedCoefficient {d : ℕ} (A : CoefficientField d)
    (hA : IsSmoothCoefficient A) :
    IsSmoothCoefficient (kineticReflectedCoefficient A) :=
  hA.comp (contDiff_fst.neg.prodMk contDiff_snd)

end HypoellipticAleksandrov.KineticAleksandrov
