module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalProbe
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Topology.TietzeExtension

/-! # Smooth ambient exit probes and their actual compact kinetic sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

/-- The physical coordinate homeomorphism associated to the native Euclidean packing. -/
def reconstructionPhysicalHomeomorph : EvolutionVec 1 ≃ₜ Point :=
  (evolutionHomeomorph 1).trans (sectionTwoHomeomorph 1)

/-- The homeomorphism agrees with the already fixed physical unpacking. -/
theorem reconstructionPhysicalHomeomorph_apply (x : EvolutionVec 1) :
    reconstructionPhysicalHomeomorph x = reconstructionPhysicalPoint x := rfl

/-- The inverse map packs physical velocity before physical position. -/
@[simp] theorem reconstructionPhysicalHomeomorph_symm_apply (p : Point) :
    reconstructionPhysicalHomeomorph.symm p = packPoint p.time p.velocity p.position := rfl

/-- Ambient smooth compact scalar functions form the exit probe vector space. -/
def exitProbeSubmodule : Submodule ℝ (EvolutionVec 1 → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun _c _f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

/-- The physical test supplied by an ambient exit probe. -/
def exitProbePhysical (f : exitProbeSubmodule) : Point → ℝ :=
  f.1 ∘ reconstructionPhysicalHomeomorph.symm

/-- A physical probe is globally continuous and compactly supported. -/
theorem exitProbePhysical_continuous_compact (f : exitProbeSubmodule) :
    Continuous (exitProbePhysical f) ∧ HasCompactSupport (exitProbePhysical f) :=
  ⟨f.2.1.continuous.comp reconstructionPhysicalHomeomorph.symm.continuous,
    f.2.2.comp_homeomorph reconstructionPhysicalHomeomorph.symm⟩

private theorem probe_native_smooth (f : exitProbeSubmodule) :
    ContDiff ℝ (⊤ : ℕ∞) (exitProbePhysical f ∘ evolutionHomeomorph 1) := by
  have h := f.2.1.comp ((evolutionProdCLE 1).symm.contDiff.comp
    ((contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst)).comp
      (evolutionProdCLE 1).contDiff))
  have heq : exitProbePhysical f ∘ evolutionHomeomorph 1 =
      (f.1 ∘ (evolutionProdCLE 1).symm) ∘
        (fun q : ℝ × PDE.Vec 1 × PDE.Vec 1 => (q.1, q.2.2, q.2.1)) ∘ evolutionProdCLE 1 := by
    funext x
    simp only [exitProbePhysical, Function.comp_apply,
      reconstructionPhysicalHomeomorph_symm_apply, time_evolutionHomeomorph,
      velocity_evolutionHomeomorph, position_evolutionHomeomorph,
      evolutionProdCLE_apply, evolutionProdCLE_symm_apply]
  rw [heq]
  exact h

/-- Smooth ambient probes supply genuine global physical C112 tests. -/
theorem exitProbePhysical_isKineticC112On (f : exitProbeSubmodule) (D : Set Point)
    (hD : IsOpen D) : IsKineticC112On (exitProbePhysical f) D :=
  isKineticC112On_of_contDiffOn hD (probe_native_smooth f).contDiffOn

private theorem probe_derivative_smooth {f : EvolutionVec 1 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : EvolutionVec 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x v) :=
  (hf.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)

private theorem probe_operator_formula {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) :
    transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1 =
      fun x => fderiv ℝ f.1 x basisT +
        A.a (transportedCoord 1 x 0) (diffusedCoord 1 x 0) *
          fderiv ℝ (fun y => fderiv ℝ f.1 y (basisV (0 : Fin 1))) x (basisV (0 : Fin 1)) +
        diffusedCoord 1 x 0 * fderiv ℝ f.1 x (basisZ (0 : Fin 1)) := by
  funext x
  simp only [transportedOperator, Fin.sum_univ_one, evolutionCoefficient, identityDrift, id_eq]

/-- The actual packed kinetic operator of a smooth compact probe is smooth and compact. -/
theorem exitProbe_operator_smooth_compact {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (f : exitProbeSubmodule) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1) ∧
    HasCompactSupport (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1) := by
  have ht := probe_derivative_smooth f.2.1 basisT
  have hv := probe_derivative_smooth f.2.1 (basisV (0 : Fin 1))
  have hz := probe_derivative_smooth f.2.1 (basisZ (0 : Fin 1))
  have hh := probe_derivative_smooth hv (basisV (0 : Fin 1))
  have hvc : HasCompactSupport (fun x => fderiv ℝ f.1 x (basisV (0 : Fin 1))) :=
    f.2.2.fderiv_apply ℝ _
  have hhc := hvc.fderiv_apply ℝ (basisV (0 : Fin 1))
  have haa : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      A.a (transportedCoord 1 x 0) (diffusedCoord 1 x 0)) :=
    A.smooth.comp (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (transportedCoord 1).contDiff).prodMk
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (diffusedCoord 1).contDiff))
  rw [probe_operator_formula A f]
  constructor
  · simpa only [Function.comp_def] using! (ht.add (haa.mul hh)).add
      (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (diffusedCoord 1).contDiff).mul hz)
  · exact ((f.2.2.fderiv_apply ℝ basisT).add hhc.mul_left).add
      (f.2.2.fderiv_apply ℝ (basisZ (0 : Fin 1))).mul_left

/-- The scalar physical operator is exactly the packed probe operator under the fixed map. -/
theorem exitProbePhysical_operator {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) (p : Point) :
    forwardScalarOperator A.a (exitProbePhysical f) p =
      transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1
        (reconstructionPhysicalHomeomorph.symm p) := by
  let x := reconstructionPhysicalHomeomorph.symm p
  have heq : (exitProbePhysical f ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1 = f.1 := by
    funext y
    exact congrArg f.1 (reconstructionPhysicalHomeomorph.symm_apply_apply y)
  have hs : ContDiffAt ℝ 2 ((exitProbePhysical f ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x := by
    rw [heq]
    exact (f.2.1.of_le (by simp)).contDiffAt
  have hop := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hs
  rw [heq, reconstruction_scalar_operator_swap] at hop
  have hx : sectionTwoPoint (evolutionHomeomorph 1 x) = p :=
    reconstructionPhysicalHomeomorph.apply_symm_apply p
  rw [hx] at hop
  exact hop.symm

/-- A compact probe and its actual kinetic operator satisfy the bounded source hypotheses. -/
theorem exitProbePhysical_bounded_source {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) :
    ∃ M : ℝ, ∀ p, |exitProbePhysical f p| ≤ M ∧
      |forwardScalarOperator A.a (exitProbePhysical f) p| ≤ M := by
  obtain ⟨B, hB⟩ := f.2.2.exists_bound_of_continuous f.2.1.continuous
  obtain ⟨C, hC⟩ := (exitProbe_operator_smooth_compact A f).2.exists_bound_of_continuous
    (exitProbe_operator_smooth_compact A f).1.continuous
  refine ⟨max B C, fun p => ⟨(hB _).trans (le_max_left _ _), ?_⟩⟩
  rw [exitProbePhysical_operator A f p]
  exact (hC _).trans (le_max_right _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
