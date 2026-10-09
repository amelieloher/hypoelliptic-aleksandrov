module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! # The explicit first derivative of a compact positive-radius parameter integral -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The spatial derivative of a jointly C¹ integrand passes through its compact radius integral. -/
theorem bellman_joint_integral_fderiv {A : Type*}
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (radius : A → ℝ) (hr : Continuous radius) (hrp : ∀ a, 0 < radius a)
    (f : (ℝ × ℝ) × ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (U ×ˢ Ioi 0))
    (q : ℝ × ℝ) (hq : q ∈ U) (e : ℝ × ℝ) :
    fderiv ℝ (fun x => ∫ a, f (x, radius a) ∂mu) q e =
      ∫ a, fderiv ℝ f (q, radius a) (e, 0) ∂mu := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) × ℝ :=
    (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0
  let J : (((ℝ × ℝ) × ℝ) →L[ℝ] ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ) ((ℝ × ℝ) × ℝ) ℝ).flip L
  let g : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun w => J (fderiv ℝ f w)
  have hopen : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have hg : ContinuousOn g (U ×ˢ Ioi 0) :=
    (J.contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen hopen (m := 0) (by norm_num))).continuousOn
  have hmap : MapsTo (fun w : (ℝ × ℝ) × A => (w.1, radius w.2))
      (U ×ˢ univ) (U ×ˢ Ioi 0) := fun w hw => ⟨hw.1, hrp w.2⟩
  have hcm : Continuous (fun w : (ℝ × ℝ) × A => (w.1, radius w.2)) :=
    continuous_fst.prodMk (hr.comp continuous_snd)
  have hc0 := hf.continuousOn.comp hcm.continuousOn hmap
  have hc1 := hg.comp hcm.continuousOn hmap
  have hd : ∀ x ∈ U, ∀ a : A,
      HasFDerivAt (fun z => f (z, radius a)) (g (x, radius a)) x := by
    intro x hx a
    have hdf := ((hf (x, radius a) ⟨hx, hrp a⟩).contDiffAt
      (hopen.mem_nhds ⟨hx, hrp a⟩)).differentiableAt (by norm_num)
    have hdc : HasFDerivAt (fun z : ℝ × ℝ => (z, radius a)) L x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const (radius a) x)
    exact hdf.hasFDerivAt.comp x hdc
  have ht := bellman_compact_parameter_hasFDerivAt mu hU
    (fun x a => f (x, radius a)) (fun x a => g (x, radius a)) hc0 hc1 hd hq
  rw [ht.fderiv, ContinuousLinearMap.integral_apply
    (bellman_compact_parameter_integrable mu (f := fun x a => g (x, radius a)) hc1 hq)]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov
