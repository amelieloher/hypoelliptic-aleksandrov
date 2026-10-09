module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionError
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGeometry
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Continuity of the actual bounded continuous-source potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- Smooth compact native sources yield continuous physical potentials on the open strip. -/
theorem reconstruction_compact_potential_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) {sMinus : ℝ}
    (f : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ reconstructionSourceDomain H sMinus T) :
    ContinuousOn (fun p => duhamelPotential E.2 T (f ∘ KineticPoint.equivProd 1)
      (sectionTwoPoint p)) (stripPast H T) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (rawLift (f ∘ KineticPoint.equivProd 1)) := hf
  have hgc := hc.comp_homeomorph (KineticPoint.homeomorphProd 1)
  have hgs : tsupport (f ∘ KineticPoint.equivProd 1) ⊆
      evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T := by
    intro p hp
    have hx := hs ((tsupport_comp_subset_preimage f
      (KineticPoint.homeomorphProd 1).continuous) hp)
    change sMinus < p.time ∧ p.time < T ∧ p.position 0 ∈ H.carrier at hx
    refine ⟨hx.2.1, ?_⟩
    apply PDE.mem_translateSet_iff_sub_mem.mpr
    simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
      PDE.vecOneCoordinate, Interval.carrier] using hx.2.2
  have hcont := reconstruction_compact_duhamel_continuousOn hH hlam hLam A H E hE T
    (f ∘ KineticPoint.equivProd 1) hg hgc hgs
  apply hcont.comp (continuous_sectionTwoPoint 1).continuousOn
  intro p hp
  refine ⟨hp.1.le, subset_closure ?_⟩
  apply PDE.mem_translateSet_iff_sub_mem.mpr
  simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
    PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2

/-- Continuity on each bounded position window with a positive lower-time margin follows
from explicit uniform compact-source approximation. -/
theorem reconstruction_source_potential_continuousOn_window
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus a T R₀ : ℝ) (ha : sMinus < a)
    (g : BoundedBorel Point)
    (hg : ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T)) :
    ContinuousOn (stripSourcePotential H E.2 T g)
      {p | a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R₀} := by
  classical
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hR (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  obtain ⟨C, hC, hgb⟩ := g.exists_bound
  choose f hf hc hs hclose using fun n => exists_reconstruction_compact_source_approx
    H sMinus a T ha (hr n) (hR n) (hr n)
    (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x))) hg C hC
    (fun x => hgb _)
  have hfc (n : ℕ) : Continuous (f n) := (hf n).continuous
  have hfb (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f n x| ≤ B := by
    obtain ⟨B, hB⟩ := (hfc n).bounded_above_of_compact_support (hc n)
    refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
    have hh : |f n x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
    exact hh.trans (le_max_left _ _)
  let G (n : ℕ) : BoundedBorel Point :=
    ⟨fun p => f n (KineticPoint.equivProd 1 (sectionTwoPoint p)),
      (hfc n).measurable.comp
        ((KineticPoint.homeomorphProd 1).continuous.comp
          (continuous_sectionTwoPoint 1)).measurable, by
      obtain ⟨B, hB, hb⟩ := hfb n
      exact ⟨B, hB, fun p => hb _⟩⟩
  let F (n : ℕ) (p : Point) : ℝ :=
    duhamelPotential E.2 T (f n ∘ KineticPoint.equivProd 1) (sectionTwoPoint p)
  have hF (n : ℕ) : ContinuousOn (F n) (stripPast H T) :=
    reconstruction_compact_potential_continuousOn hH hlam hLam A H E hE T
      (f n) (hf n) (hc n) (hs n)
  have hFG (n : ℕ) (e : StripPole H (T : WithTop ℝ)) :
      stripPotentialOfKernel H E.2 T (G n) e = F n e.1 := by
    rw [← stripSourcePotential_eq_green H E.2 T (G n) e]
    unfold stripSourcePotential
    congr 1
  let Q := Real.exp ((max |H.lo| |H.hi| + 1) * (T - a)) * (2 * Real.exp R₀)
  let b (n : ℕ) : ℝ := r n * (T - a) + C *
    (Real.exp 1 * (2 * (r n) ^ 2 / lam) + r n + Q * r n)
  have hbd (n : ℕ) (p : Point)
      (hp : a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R₀) :
      |stripSourcePotential H E.2 T g p - F n p| ≤ b n := by
    let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hp.2.1.1, hp.2.1.2⟩
    have herr := reconstruction_green_potential_error hH hlam hLam A H E hE T a e hp.1
      g (G n) C hC (hr n) (hR n) (hr n).le (fun z hz => by
        have hh := hclose n (KineticPoint.equivProd 1 (sectionTwoPoint z)) hz
        rw [Equiv.symm_apply_apply, sectionTwoPoint_involutive] at hh
        simpa only [G, abs_sub_comm] using hh)
    rw [hFG] at herr
    rw [← stripSourcePotential_eq_green H E.2 T g e] at herr
    have hV : 0 ≤ max |H.lo| |H.hi| + 1 := by
      have hv := (abs_nonneg H.lo).trans (le_max_left |H.lo| |H.hi|)
      linarith only [hv]
    have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (sub_le_sub_left hp.1 T) hV)
    have hx := abs_le.mp hp.2.2
    have hxp := Real.exp_le_exp.mpr hx.2
    have hxm := Real.exp_le_exp.mpr (neg_le.mp hx.1)
    have hw : reconstructionSpatialWeight (p.position 0) ≤ 2 * Real.exp R₀ := by
      unfold reconstructionSpatialWeight
      linarith only [hxp, hxm]
    have hQ : Real.exp ((max |H.lo| |H.hi| + 1) * (T - p.time)) *
        reconstructionSpatialWeight (p.position 0) ≤ Q :=
      mul_le_mul hex hw (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (Real.exp_pos _).le
    apply herr.trans
    change _ ≤ b n
    dsimp only [b]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hp.1 T) (hr n).le
    · apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add (le_refl _)
      simpa only [r, div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right hQ (hR n).le
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb0 : Tendsto b atTop (𝓝 0) := by
    simpa only [b, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero, add_zero] using
      (hr0.mul_const (T - a)).add
        ((((hr0.pow 2).const_mul 2).div_const lam).const_mul (Real.exp 1) |>.add hr0 |>.add
          (hr0.const_mul Q) |>.const_mul C)
  have hu : TendstoUniformlyOn F (stripSourcePotential H E.2 T g) atTop
      {p | a ≤ p.time ∧ p ∈ stripPast H T ∧ |p.position 0| ≤ R₀} := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hb0.eventually (gt_mem_nhds hε)] with n hn
    intro p hp
    simpa only [Real.dist_eq] using (hbd n p hp).trans_lt hn
  exact hu.continuousOn (Eventually.of_forall fun n =>
    (hF n).mono (fun p hp => hp.2.1)).frequently

/-- The actual bounded-source potential is continuous at every strictly interior strip point.
Only continuity of the source on the open strip is required. -/
theorem reconstruction_source_potential_continuousOn
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (g : BoundedBorel Point)
    (hg : ContinuousOn (fun x => g (sectionTwoPoint ((KineticPoint.equivProd 1).symm x)))
      (reconstructionSourceDomain H sMinus T)) :
    ContinuousOn (stripSourcePotential H E.2 T g) (reconstructionStrip H sMinus T) := by
  intro p hp
  let a := (sMinus + p.time) / 2
  let R := |p.position 0| + 1
  have ha : sMinus < a := by dsimp only [a]; linarith only [hp.1]
  have hap : a < p.time := by dsimp only [a]; linarith only [hp.1]
  have hR : |p.position 0| < R := by dsimp only [R]; linarith
  have hc := reconstruction_source_potential_continuousOn_window hH hlam hLam A H E hE
    sMinus a T R ha g hg
  have hpos : Continuous (fun q : Point => |q.position 0|) :=
    ((continuous_apply 0).comp continuous_position).abs
  have hn : {q : Point | a ≤ q.time ∧ q ∈ stripPast H T ∧ |q.position 0| ≤ R} ∈ 𝓝 p := by
    have h := (((isOpen_lt continuous_const continuous_time).inter
      (isOpen_stripPast H T)).inter (isOpen_lt hpos continuous_const)).mem_nhds
        ⟨⟨hap, hp.2⟩, hR⟩
    exact Filter.mem_of_superset h (fun q hq => ⟨hq.1.1.le, hq.1.2, hq.2.le⟩)
  exact (hc.continuousAt hn).continuousWithinAt

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
