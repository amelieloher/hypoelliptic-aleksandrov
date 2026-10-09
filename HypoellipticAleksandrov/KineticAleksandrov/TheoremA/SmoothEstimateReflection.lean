module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Reflection of cylinder measures, regularity and boundary suprema -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Set MeasureTheory Parabolic
variable {d : ℕ}

/-- The reflected backward domain is literally the source forward cylinder. -/
theorem preimage_backwardCylinder_reflection (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    kineticReflection ⁻¹' backwardCylinder P₀ R =
      forwardCylinder (kineticReflection P₀) R hR := by
  rw [← kineticReflection_image_backwardCylinder P₀ R hR]
  ext P
  constructor
  · intro hP
    exact ⟨kineticReflection P, hP, kineticReflection_involutive P⟩
  · rintro ⟨q, hq, heq⟩
    have h := congrArg kineticReflection heq
    rw [kineticReflection_involutive q] at h
    change kineticReflection P ∈ backwardCylinder P₀ R
    rw [← h]
    exact hq

/-- Reflection preserves the restricted cylinder volumes, with no scale factor. -/
theorem measurePreserving_reflection_forward (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    MeasurePreserving (kineticReflection (d := d))
      (volume.restrict (forwardCylinder (kineticReflection P₀) R hR))
      (volume.restrict (backwardCylinder P₀ R)) := by
  have h := (measurePreserving_kineticReflection d).restrict_preimage_emb
    (kineticReflectionHomeomorph d).toMeasurableEquiv.measurableEmbedding
    (backwardCylinder P₀ R)
  rw [preimage_backwardCylinder_reflection P₀ R hR] at h
  exact h

/-- Reflection maps the closures used in the boundary-value estimate exactly. -/
theorem preimage_closure_backwardCylinder_reflection
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    kineticReflection ⁻¹' closure (backwardCylinder P₀ R) =
      closure (forwardCylinder (kineticReflection P₀) R hR) := by
  rw [← preimage_backwardCylinder_reflection P₀ R hR]
  exact (kineticReflectionHomeomorph d).preimage_closure _

/-- The reflected boundary supremum is the original kinetic boundary supremum. -/
theorem boundarySup_reflection (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (u : KineticPoint d → ℝ) :
    sSup ((fun P => max ((u ∘ kineticReflection) P) 0) ''
      exitBoundary (kineticReflection P₀) R hR) =
    sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) := by
  rw [← kineticReflection_image_kineticBoundary P₀ R hR, ← image_comp]
  congr 1
  congr 1
  funext P
  simp only [Function.comp_apply]
  rw [kineticReflection_involutive P]

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
