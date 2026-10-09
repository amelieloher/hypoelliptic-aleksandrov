module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourDensityStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsLocality
import Mathlib.MeasureTheory.Integral.Bochner.Set
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry

/-! # Canonical cylinder restrictions of autonomous strip source potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic Filter Topology
open SectionTwo TheoremA Evolution

/-- The actual strip Green measure restricted to the observation cylinder.
The zero value outside the cylinder is immaterial to all interior assertions. -/
def autonomousCylinderGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) : Measure Point := by
  classical
  exact
  if hP : P ∈ forwardCylinder Z₀ R hR then
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
      (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
        (forwardCylinder Z₀ R hR)
  else 0

/-- Compact cylinder sources have the exact ABP potential regularity and equation. -/
theorem autonomous_cylinder_green_potentials
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (g : Point → ℝ)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd 1).symm z)))
    (hgc : HasCompactSupport g) (hgQ : tsupport g ⊆ forwardCylinder Z₀ R hR)
    (hg0 : ∀ P, 0 ≤ g P) :
    IsKineticC112On (fun P => ∫ z, g z ∂autonomousCylinderGreen hH hLE hlam hLam A
        Z₀ R hR P) (forwardCylinder Z₀ R hR) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR,
        0 ≤ ∫ z, g z ∂autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR,
        forwardKineticOperator (autonomousCoefficient A.a)
          (fun P => ∫ z, g z ∂autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P)
          P = -g P) := by
  classical
  let Q := forwardCylinder Z₀ R hR
  let H := capacityCylinderInterval Z₀ R hR
  let T := Z₀.time + R ^ 2
  let E := stripEvolution hH hLE hlam hLam A H
  have hE := stripEvolution_spec hH hLE hlam hLam A H
  have hpacked : ContDiff ℝ (⊤ : ℕ∞) (g ∘ reconstructionPhysicalHomeomorph) := by
    convert hgs.comp ((evolutionProdCLE 1).contDiff.comp nestedSwapPacked_contDiff) using 1
    funext x
    change g (reconstructionPhysicalHomeomorph x) =
      g ((KineticPoint.equivProd 1).symm (evolutionProdCLE 1 (nestedSwapPacked x)))
    apply congrArg g
    exact (nestedSwapPacked_physical x).symm
  let f : exitProbeSubmodule :=
    ⟨g ∘ reconstructionPhysicalHomeomorph, hpacked,
      hgc.comp_homeomorph reconstructionPhysicalHomeomorph⟩
  have hf : exitProbePhysical f = g := by
    funext P
    change g (reconstructionPhysicalHomeomorph
      (reconstructionPhysicalHomeomorph.symm P)) = g P
    rw [Homeomorph.apply_symm_apply]
  have hs : tsupport (exitProbePhysical f) ⊆ {P | P.time < T ∧ P.velocity 0 ∈ H.carrier} := by
    rw [hf]
    intro P hP
    exact ⟨WithTop.coe_lt_coe.mp (capacityCylinderPole Z₀ P R hR (hgQ hP)).2.1,
      (capacityCylinderPole Z₀ P R hR (hgQ hP)).2.2⟩
  let V := nestedSourcePotential H E T f
  let F := fun P => ∫ z, g z ∂autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P
  have heq : ∀ P ∈ Q, F P = V P := by
    intro P hP
    have hi : Q.indicator g = g := by
      funext z
      by_cases hz : z ∈ Q
      · exact indicator_of_mem hz g
      · rw [indicator_of_notMem hz]
        symm
        by_contra hgz
        exact hz (hgQ (subset_closure hgz))
    dsimp only [F, autonomousCylinderGreen]
    rw [dite_eq_left hP,
      ← integral_indicator (isOpen_forwardCylinder Z₀ R hR).measurableSet, hi]
    have hr := nestedSourcePotential_eq_green A H E T f
      (capacityCylinderPole Z₀ P R hR hP)
    rw [hf] at hr
    exact hr.symm
  have hgc' := (exitProbePhysical_continuous_compact f).2.comp_homeomorph
    (sectionTwoHomeomorph 1)
  obtain ⟨-, -, hsm, -, -, -, -, -, -⟩ :=
    kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
      hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
      E.1 E.2 hE T (exitProbePhysical f ∘ sectionTwoPoint) (fun P => by rw [hf]; exact hg0 _)
      (nested_native_probe_raw_smooth f) hgc' (nested_native_probe_source_support H T f hs)
  have hV := nested_physical_contDiffOn hsm
  have hmap : MapsTo (evolutionHomeomorph 1) (evolutionHomeomorph 1 ⁻¹' Q)
      (sectionTwoPoint ⁻¹' evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) := by
    intro x hx
    exact (nested_mem_native_past H T _).mpr
      ⟨WithTop.coe_lt_coe.mp (capacityCylinderPole Z₀ _ R hR hx).2.1,
        (capacityCylinderPole Z₀ _ R hR hx).2.2⟩
  have hVF : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' Q) := hV.mono (fun _ hx => hmap hx)
  have hF := hVF.congr (fun x hx => heq _ hx)
  obtain ⟨-, -, hop⟩ := nestedSourcePotential_regular_source hH hlam hLam A H E hE T f
    (fun P => by rw [hf]; exact hg0 _) hs
  refine ⟨isKineticC112On_of_contDiffOn (isOpen_forwardCylinder Z₀ R hR) hF,
    fun P _ => integral_nonneg hg0, ?_⟩
  intro P hP
  have hn : F =ᶠ[𝓝 P] V := by
    filter_upwards [(isOpen_forwardCylinder Z₀ R hR).mem_nhds hP] with z hz
    exact heq z hz
  rw [forwardKineticOperator_eq_of_eventuallyEq _ hn, forwardOperator_autonomous]
  rw [hop P (WithTop.coe_lt_coe.mp (capacityCylinderPole Z₀ P R hR hP).2.1)
    (capacityCylinderPole Z₀ P R hR hP).2.2, hf]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
