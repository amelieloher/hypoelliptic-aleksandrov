module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityMinimum
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Cap
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular
import Mathlib.Tactic

/-!
# Smooth interior cutoff for the nearly full superlevel estimate

The cutoff is constructed in the existing product coordinates. Its compact support
lies in the literal kinetic cylinder, and it equals one on the closed source cap.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped MatrixOrder

/-- The four coefficient conditions of the full kinetic Hölder theorem. -/
abbrev FullElliptic {d : ℕ} (lam Lam : ℝ) (A : FullKineticCoefficient d) : Prop :=
  Measurable (fullKineticCoefficientAt A) ∧
  (∀ P, (fullKineticCoefficientAt A P).IsSymm) ∧
  (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
    lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) ∧
  (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
    fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))

/-- A smooth compactly supported product-coordinate cutoff for the source cap. -/
theorem exists_unit_cutoff (d : ℕ) :
    ∃ f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      (∀ P ∈ closure (cap d), f (KineticPoint.equivProd d P) = 1) ∧
      HasCompactSupport f ∧
      tsupport f ⊆ (KineticPoint.equivProd d) ''
        backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
  let e := KineticPoint.homeomorphProd d
  have hK := (isCompact_closure_cap d).image e.continuous
  have hQ : IsOpen (e '' backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) :=
    e.isOpen_image.mpr (isOpen_backwardCylinder _ _ (by norm_num))
  have hKQ := image_mono (f := e) (cap_compact_inside d).2
  obtain ⟨U, hU, hKU, hUQ, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK hQ hKQ
  obtain ⟨f, hf, hrange, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU hK.isClosed hKU
  refine ⟨f, hf, fun z => hrange (mem_range_self z), ?_, ?_, ?_⟩
  · intro P hP
    exact (hone _).mp (mem_image_of_mem e hP)
  · change IsCompact (closure (Function.support f))
    rw [hsupport]
    exact hUc
  · change closure (Function.support f) ⊆ _
    rw [hsupport]
    exact hUQ

end HypoellipticAleksandrov.KineticAleksandrov.Holder
