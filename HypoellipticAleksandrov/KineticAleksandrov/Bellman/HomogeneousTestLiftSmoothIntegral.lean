module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegral
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! # C² compact-parameter integrals of jointly C² functions -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Joint C² regularity gives spatial C² regularity after compact radius integration. -/
theorem bellman_joint_contDiff_integral {E F A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] {U : Set E} (hU : IsOpen U)
    (radius : A → ℝ) (hr : Continuous radius) (hrp : ∀ a, 0 < radius a)
    (f : E × ℝ → F) (hf : ContDiffOn ℝ 2 f (U ×ˢ Ioi 0)) :
    ContDiffOn ℝ 2 (fun q => ∫ a, f (q, radius a) ∂mu) U := by
  let L : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod 0
  let J : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip L
  let g : E × ℝ → E →L[ℝ] F := fun w => J (fderiv ℝ f w)
  have hopen : IsOpen (U ×ˢ Ioi (0 : ℝ)) := hU.prod isOpen_Ioi
  have hg : ContDiffOn ℝ 1 g (U ×ˢ Ioi 0) :=
    J.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hopen (m := 1) (by norm_num))
  -- Pin the first-derivative carrier before elaborating the second derivative.
  let : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  let J' : ((E × ℝ) →L[ℝ] (E →L[ℝ] F)) →L[ℝ] E →L[ℝ] (E →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) (E →L[ℝ] F)).flip L
  let g' : E × ℝ → E →L[ℝ] (E →L[ℝ] F) := fun w => J' (fderiv ℝ g w)
  have hg' : ContinuousOn g' (U ×ˢ Ioi 0) :=
    (J'.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen hopen (m := 0) (by norm_num))).continuousOn
  have hmap : MapsTo (fun w : E × A => (w.1, radius w.2))
      (U ×ˢ univ) (U ×ˢ Ioi 0) := fun w hw => ⟨hw.1, hrp w.2⟩
  have hcm : Continuous (fun w : E × A => (w.1, radius w.2)) :=
    continuous_fst.prodMk (hr.comp continuous_snd)
  have hc0 : ContinuousOn (fun w : E × A => f (w.1, radius w.2))
      (U ×ˢ univ) := hf.continuousOn.comp hcm.continuousOn hmap
  have hc1 : ContinuousOn (fun w : E × A => g (w.1, radius w.2))
      (U ×ˢ univ) := hg.continuousOn.comp hcm.continuousOn hmap
  have hc2 : ContinuousOn (fun w : E × A => g' (w.1, radius w.2))
      (U ×ˢ univ) := hg'.comp hcm.continuousOn hmap
  have hd0 : ∀ q ∈ U, ∀ a : A,
      HasFDerivAt (fun x => f (x, radius a)) (g (q, radius a)) q := by
    intro q hq a
    have hd := ((hf (q, radius a) ⟨hq, hrp a⟩).contDiffAt
      (hopen.mem_nhds ⟨hq, hrp a⟩)).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun q : E => (q, radius a)) L q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const (radius a) q)
    exact hd.hasFDerivAt.comp q hc
  have hd1 : ∀ q ∈ U, ∀ a : A,
      HasFDerivAt (fun x => g (x, radius a)) (g' (q, radius a)) q := by
    intro q hq a
    have hd := ((hg (q, radius a) ⟨hq, hrp a⟩).contDiffAt
      (hopen.mem_nhds ⟨hq, hrp a⟩)).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun q : E => (q, radius a)) L q :=
      (hasFDerivAt_id q).prodMk (hasFDerivAt_const (radius a) q)
    exact hd.hasFDerivAt.comp q hc
  exact bellman_compact_parameter_contDiffOn_two mu hU
    (fun q a => f (q, radius a)) (fun q a => g (q, radius a))
    (fun q a => g' (q, radius a)) hc0 hc1 hc2 hd0 hd1

end HypoellipticAleksandrov.KineticAleksandrov
