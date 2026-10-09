module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PreliminaryP6Density
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
import Mathlib.Tactic

/-! # The preliminary forward autonomous maximum principle -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The preliminary forward estimate depends only on entrance counting and classical inputs. -/
theorem preliminary_forward_abp_of_entrance
    (hentrance : EntranceStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (u g : Point → ℝ),
      ContinuousOn u (closure (forwardCylinder Z₀ R hR)) →
      IsKineticC112On u (forwardCylinder Z₀ R hR) →
      (∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ g P) →
      MemLp g (ENNReal.ofReal 6) (volume.restrict (forwardCylinder Z₀ R hR)) →
      (∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
        -g P ≤ forwardScalarOperator A.a u P) →
      ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
        sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
          C * R ^ (2 - 6 / (6 : ℝ)) *
            (eLpNorm ({P | 0 < u P}.indicator g) (ENNReal.ofReal 6)
              (volume.restrict (forwardCylinder Z₀ R hR))).toReal := by
  obtain ⟨C, hC, hden⟩ := preliminary_cylinder_density_of_entrance hentrance
    hH hLE lam Lam hlam hLam
  have hq : (1 : ℝ) < 6 / (6 - 1) := by norm_num
  have hid : (6 / (6 - 1)) / (6 / (6 - 1) - 1) = (6 : ℝ) ∧
      6 / (6 / (6 - 1)) - 4 = 2 - 6 / (6 : ℝ) := by norm_num
  refine ⟨C, hC, ?_⟩
  intro A Z₀ R hR u g hcont hreg hg0 hLp hsub
  have hAc : ContinuousOn (fun P : Point =>
      autonomousCoefficient A.a P.time P.position P.velocity) (forwardCylinder Z₀ R hR) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (A.smooth.continuous.comp
      (((continuous_apply 0).comp continuous_position).prodMk
        ((continuous_apply 0).comp continuous_velocity))).continuousOn
  have hpos : ∀ P ∈ forwardCylinder Z₀ R hR,
      (autonomousCoefficient A.a P.time P.position P.velocity).PosSemidef := by
    intro P _
    have heq : autonomousCoefficient A.a P.time P.position P.velocity =
        A.a (P.position 0) (P.velocity 0) • (1 : PDE.Mat 1) := by
      ext i j
      fin_cases i
      fin_cases j
      simp [autonomousCoefficient]
    rw [heq]
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
      (hlam.le.trans (A.bounds _ _).1)
  have hden' : ∀ P ∈ forwardCylinder Z₀ R hR, ∃ G : Point → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P =
        (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
          (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal (6 / (6 - 1)))
        (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (2 - 6 / (6 : ℝ)) ∧
      MemLp G (ENNReal.ofReal (6 / (6 - 1)))
        (volume.restrict (forwardCylinder Z₀ R hR)) := by
    intro P hP
    obtain ⟨G, ⟨hG, hG0, heq⟩, hGLp, hGN⟩ := hden A Z₀ R hR P hP
    have hpower : R ^ (2 - 6 / (6 : ℝ)) = R := by norm_num
    have hGN' : (eLpNorm G (ENNReal.ofReal (6 / (6 - 1)))
        (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤
          C * R ^ (2 - 6 / (6 : ℝ)) := by
      simpa only [hpower, show (6 / (6 - 1) : ℝ) = 6 / 5 by norm_num] using hGN
    refine ⟨G, hG, hG0, ?_, hGN', ?_⟩
    · simp only [autonomousCylinderGreen, dite_eq_left hP]
      exact heq
    · simpa only [show (6 / (6 - 1) : ℝ) = 6 / 5 by norm_num] using hGLp
  have hs : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
      -g P ≤ forwardKineticOperator (autonomousCoefficient A.a) u P := by
    simpa only [forwardOperator_autonomous] using hsub
  have hl : MemLp g (ENNReal.ofReal ((6 / (6 - 1)) / (6 / (6 - 1) - 1)))
      (volume.restrict (forwardCylinder Z₀ R hR)) := by rwa [hid.1]
  have hb := kinetic_abp_abstract_of_continuous Z₀ R hR (autonomousCoefficient A.a)
    hAc hpos (6 / (6 - 1)) hq (C * R ^ (2 - 6 / (6 : ℝ)))
    (mul_pos hC (Real.rpow_pos_of_pos hR _))
    (autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR)
    (autonomous_cylinder_green_potentials hH hLE hlam hLam A Z₀ R hR)
    hden' u g hcont hreg hg0 hl hs
  simpa only [hid.1] using hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
