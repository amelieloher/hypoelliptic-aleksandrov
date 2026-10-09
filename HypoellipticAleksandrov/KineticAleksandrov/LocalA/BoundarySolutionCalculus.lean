module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smooth physical probes and their actual compact kinetic sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA Parabolic
open scoped Topology

/-- Smoothness in physical product coordinates gives smoothness in the fixed native packing. -/
theorem boundary_probe_native_smooth {d : ℕ} (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm)) :
    ContDiff ℝ (⊤ : ℕ∞) ((φ ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × PDE.Vec d × PDE.Vec d => (q.1, q.2.2, q.2.1)) :=
    contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)
  exact (hφ.comp hs).comp (evolutionProdCLE d).contDiff

/-- Smooth physical compact probes have globally continuous values. -/
theorem boundary_probe_continuous {d : ℕ} (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm)) : Continuous φ := by
  have hc := hφ.continuous.comp (KineticPoint.homeomorphProd d).continuous
  have heq : (φ ∘ (KineticPoint.equivProd d).symm) ∘ KineticPoint.homeomorphProd d = φ := by
    funext P
    rfl
  rw [heq] at hc
  exact hc

/-- The compact-support finite-sum API in pointwise form. -/
theorem boundary_compact_sum {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (f : ι → X → ℝ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i, f i x) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (f := f) (fun i _ => hf i)
  have heq : (∑ i, f i) = fun x => ∑ i, f i x := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq] at h
  exact h

/-- An actual smooth compact probe has a compactly supported native kinetic operator. -/
theorem boundary_probe_operator_compact {d : ℕ}
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    {f : EvolutionVec d → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (transportedOperator B b f) := by
  have hij (i j : Fin d) : HasCompactSupport (fun x =>
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j *
        fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x (basisV i)) :=
    ((hc.fderiv_apply ℝ (basisV j)).fderiv_apply ℝ (basisV i)).mul_left
  have hj (i : Fin d) : HasCompactSupport (fun x => ∑ j,
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j *
        fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x (basisV i)) := by
    exact boundary_compact_sum (fun j => fun x =>
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j *
        fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x (basisV i)) (fun j => hij i j)
  have hh : HasCompactSupport (fun x => ∑ i, ∑ j,
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j *
        fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x (basisV i)) := by
    exact boundary_compact_sum (fun i => fun x => ∑ j,
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j *
        fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x (basisV i)) (fun i => hj i)
  have hzi (i : Fin d) : HasCompactSupport
      (fun x => b (diffusedCoord d x) i * fderiv ℝ f x (basisZ i)) :=
    (hc.fderiv_apply ℝ (basisZ i)).mul_left
  have hz : HasCompactSupport (fun x => ∑ i,
      b (diffusedCoord d x) i * fderiv ℝ f x (basisZ i)) := by
    exact boundary_compact_sum (fun i => fun x =>
      b (diffusedCoord d x) i * fderiv ℝ f x (basisZ i)) (fun i => hzi i)
  exact ((hc.fderiv_apply ℝ basisT).add hh).add hz

/-- The physical kinetic operator equals the native operator at the fixed swapped packing. -/
theorem boundary_probe_operator_native {d : ℕ} (B : CoefficientField d)
    (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (x : EvolutionVec d) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) φ
      (sectionTwoPoint (evolutionHomeomorph d x)) =
    transportedOperator (zIndependentCoefficient B) (identityDrift d)
      ((φ ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) x := by
  rw [forwardKineticOperator_eq_lop_identity]
  exact (transportedOperator_comp
    ((boundary_probe_native_smooth φ hφ).of_le (by simp)).contDiffAt).symm

/-- Smooth compact physical tests have smooth bounded actual operator data. -/
theorem boundary_probe_operator_bounded {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) :
    Continuous (forwardKineticOperator (ofTimeVelocityCoefficient B) φ) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ P,
        |forwardKineticOperator (ofTimeVelocityCoefficient B) φ P| ≤ M := by
  let H := (evolutionHomeomorph d).trans (sectionTwoHomeomorph d)
  let f := φ ∘ H
  have hfc : HasCompactSupport f := hc.comp_homeomorph H
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := boundary_probe_native_smooth φ hφ
  have hsm := (contDiffOn_duhamel_operator isOpen_univ
    (sectionTwoCoefficient_fullBounds lam Lam B hB).1 (identityDrift_smooth d)
    hfs.contDiffOn)
  have hopc : Continuous
      (transportedOperator (zIndependentCoefficient B) (identityDrift d) f) :=
    (contDiffOn_univ.mp hsm).continuous
  have hopk := boundary_probe_operator_compact
    (zIndependentCoefficient B) (identityDrift d) hfc
  have heq : forwardKineticOperator (ofTimeVelocityCoefficient B) φ =
      transportedOperator (zIndependentCoefficient B) (identityDrift d) f ∘ H.symm := by
    funext P
    have h := boundary_probe_operator_native B φ hφ (H.symm P)
    change forwardKineticOperator (ofTimeVelocityCoefficient B) φ (H (H.symm P)) =
      transportedOperator (zIndependentCoefficient B) (identityDrift d) f (H.symm P) at h
    rw [Homeomorph.apply_symm_apply] at h
    exact h
  refine ⟨by rw [heq]; exact hopc.comp H.symm.continuous, ?_⟩
  obtain ⟨M, hM⟩ := hopk.exists_bound_of_continuous hopc
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro P
  rw [heq]
  exact (hM _).trans (le_max_left _ _)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
