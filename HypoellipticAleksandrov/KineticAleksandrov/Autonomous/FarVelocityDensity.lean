module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PushforwardStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import Mathlib.Tactic

/-! # A single clock interval controls cylinders far from zero velocity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The source's single clock, with centre v₀ and radius 4R. -/
def farVelocityClock (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (hfar : 8 * R < |Z₀.velocity 0|) : Clock where
  vbar := Z₀.velocity 0
  r := 4 * R
  nonzero := by intro h; rw [h, abs_zero] at hfar; linarith
  positive := by positivity
  radius := by linarith

/-- The cylinder velocity interval is contained in the single clock's active interval. -/
theorem farVelocityClock_contains (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (hfar : 8 * R < |Z₀.velocity 0|) :
    (capacityCylinderInterval Z₀ R hR).carrier ⊆
      (farVelocityClock Z₀ R hR hfar).active := by
  intro v hv
  change Z₀.velocity 0 - R < v ∧ v < Z₀.velocity 0 + R at hv
  change Z₀.velocity 0 - 3 * (4 * R) / 4 < v ∧
    v < Z₀.velocity 0 + 3 * (4 * R) / 4
  constructor <;> linarith [hv.1, hv.2]

/-- The source far-velocity density estimate, conditional only on p:pushforward. -/
theorem cylinder_density_far (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      8 * R < |Z₀.velocity 0| →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4) := by
  obtain ⟨C, hC, hc⟩ := (hpush hH hLE lam Lam hlam hLam).2 q hq
  refine ⟨C * (4 : ℝ) ^ (6 / q - 4), by positivity, ?_⟩
  intro A Z₀ R hR P hP hfar
  let c := farVelocityClock Z₀ R hR hfar
  have hsub := farVelocityClock_contains Z₀ R hR hfar
  let e := capacityCylinderPole Z₀ P R hR hP
  have he : P.velocity 0 ∈ c.active := hsub e.2.2
  obtain ⟨f, hfm, hf0, hfd, hfp, hfn⟩ := hc A c P he
  have hm := stripGreen_mono hH hLE hlam hLam A
    (capacityCylinderInterval Z₀ R hR) c.activeInterval hsub
    (Z₀.time + R ^ 2) ⊤ le_top e
  have hep : stripEnlargePole (capacityCylinderInterval Z₀ R hR) c.activeInterval hsub
      (Z₀.time + R ^ 2) ⊤ le_top e = densityClockPole c P he := Subtype.ext rfl
  rw [hep, hfd] at hm
  have hD : MeasurableSet (densityClockStrip c P) :=
    (isOpen_Ioi.preimage continuous_time).measurableSet.inter
      (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
  have := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := density_restrict_of_le_withDensity volume
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
      (Z₀.time + R ^ 2) e) (densityClockStrip c P) (forwardCylinder Z₀ R hR)
    hD (isOpen_forwardCylinder Z₀ R hR).measurableSet f hfm hf0
    (ENNReal.ofReal q) hfp hm
  refine ⟨g, hgm, hg0, hgd, hgp, ?_⟩
  have hn := (ENNReal.toReal_mono hfp.ne hgn).trans hfn
  have hr : c.r ^ (6 / q - 4) = (4 : ℝ) ^ (6 / q - 4) * R ^ (6 / q - 4) :=
    Real.mul_rpow (by norm_num) hR.le
  rw [hr] at hn
  simpa only [mul_assoc] using hn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
