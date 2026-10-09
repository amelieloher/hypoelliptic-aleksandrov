module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyNativeMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Mixed smoothness of the explicit cutoff integral on a compact spatial carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- Spatial integration of the explicit cutoff formula is jointly smooth in time and
space. The underlying profile parameter is assumed only continuous, never smooth. -/
theorem compact_cutoff_mollification_contDiff {d : ℕ} {A : Type}
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (nu : Measure A) [IsFiniteMeasure nu]
    (y : A → XV d) (hy : Continuous y) (u : A → ℝ) (hu : Continuous u)
    (phi : ContDiffBump (0 : XV d)) (mu R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × XV d =>
      ∫ a, phi.normed volume (z.2 - y a) * timeCutoffTheta
        (u a - Real.exp (-mu * z.1) * (2 - PDE.vecNormSq (y a).2 / R ^ 2)) ∂nu) := by
  let f : (ℝ × XV d) × (XV d × ℝ) → ℝ := fun z =>
    phi.normed volume (z.1.2 - z.2.1) * timeCutoffTheta
      (z.2.2 - Real.exp (-mu * z.1.1) * (2 - PDE.vecNormSq z.2.1.2 / R ^ 2))
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℝ × XV d) × (XV d × ℝ) => z.1.1) :=
    contDiff_fst.fst
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℝ × XV d) × (XV d × ℝ) => z.1.2) :=
    contDiff_fst.snd
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℝ × XV d) × (XV d × ℝ) => z.2.2) :=
    contDiff_snd.snd
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun z : (ℝ × XV d) × (XV d × ℝ) => z.2.1.2) :=
    contDiff_snd.fst.snd
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact (phi.contDiff_normed.comp (hq.sub contDiff_snd.fst)).mul
      (contDiff_timeCutoffTheta.comp (hs.sub
        ((Real.contDiff_exp.comp (contDiff_const.mul ht)).mul
          (contDiff_const.sub ((PDE.contDiff_vecNormSq.comp hv).div_const (R ^ 2))))))
  exact compact_parameter_contDiff nu (fun a => (y a, u a)) (hy.prodMk hu) f hf

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
