module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityAtoms
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
import Mathlib.Tactic

/-! # Capacity in the source's forward-cylinder velocity strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The velocity interval of the forward cylinder. -/
def capacityCylinderInterval (Z0 : Point) (R : ℝ) (hR : 0 < R) : Interval :=
  ⟨Z0.velocity 0 - R, Z0.velocity 0 + R, by linarith⟩

/-- Every forward-cylinder point is an interior pole of its velocity strip. -/
def capacityCylinderPole (Z0 P : Point) (R : ℝ) (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z0 R hR) :
    StripPole (capacityCylinderInterval Z0 R hR) (↑(Z0.time + R ^ 2) : WithTop ℝ) := by
  refine ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, ?_⟩
  have hn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hP.2.2.1
  have hc := (PDE.abs_apply_le_vecEuclideanNorm (P.velocity - Z0.velocity) 0).trans_lt hn
  simp only [Pi.sub_apply] at hc
  obtain ⟨hl, hu⟩ := abs_lt.mp hc
  change Z0.velocity 0 - R < P.velocity 0 ∧ P.velocity 0 < Z0.velocity 0 + R
  constructor <;> linarith

/-- The literal source coefficient is twice the cylinder radius divided by ellipticity. -/
theorem cylinder_strip_capacity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (Z0 P : Point) (R : ℝ) (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z0 R hR) (E : Interval) :
    stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)
      {p | p.velocity 0 ∈ E.carrier} ≤ ENNReal.ofReal (2 * R / lam * (E.hi - E.lo)) := by
  have h := strip_capacity hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
    (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP) E
  have hw : (capacityCylinderInterval Z0 R hR).hi -
      (capacityCylinderInterval Z0 R hR).lo = 2 * R := by
    dsimp only [capacityCylinderInterval]
    ring
  rwa [hw] at h

/-- Exact velocity slices have zero mass in the forward-cylinder velocity strip. -/
theorem cylinder_strip_velocity_slice_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (Z0 P : Point) (R : ℝ) (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z0 R hR) (v : ℝ) :
    stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP) {p | p.velocity 0 = v} = 0 :=
  stripGreen_velocity_slice_zero hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
    (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP) v

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
