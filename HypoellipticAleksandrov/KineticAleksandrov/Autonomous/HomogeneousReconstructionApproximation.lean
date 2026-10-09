module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionSpatial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.Piecewise

/-! # Interior compact approximation of continuous bounded strip sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo Evolution
open scoped CompactlySupported Topology

/-- Multiplying a locally continuous source by an interior compact cutoff is continuous. -/
theorem reconstruction_cutoff_mul_continuous
    {V : Set (ℝ × PDE.Vec 1 × PDE.Vec 1)} (hV : IsOpen V)
    {g χ : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ}
    (hg : ContinuousOn g V) (hχ : Continuous χ) (hs : tsupport χ ⊆ V) :
    Continuous (fun x => χ x * g x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ V
  · exact hχ.continuousAt.mul (hg.continuousAt (hV.mem_nhds hx))
  · have ht : x ∈ (tsupport χ)ᶜ := fun hh => hx (hs hh)
    have hn := isClosed_tsupport χ |>.isOpen_compl.mem_nhds ht
    apply (show ContinuousAt (fun _ : ℝ × PDE.Vec 1 × PDE.Vec 1 => (0 : ℝ)) x
      from continuousAt_const).congr
    filter_upwards [hn] with y hy
    have hz : χ y = 0 := by
      by_contra hh
      exact hy (subset_tsupport χ hh)
    simp only [hz, zero_mul]

/-- A continuous compact interior function admits a smooth compact interior approximation. -/
theorem reconstruction_smooth_compact_close
    {V : Set (ℝ × PDE.Vec 1 × PDE.Vec 1)} (hV : IsOpen V)
    (g : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V ∧
      ∀ x, |f x - g x| ≤ ε := by
  obtain ⟨ψ, hψ, hψc, hψs, hb, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hc.isCompact hV hs
  let G : C_c(ℝ × PDE.Vec 1 × PDE.Vec 1, ℝ) := ⟨⟨g, hg⟩, hc⟩
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close G ε hε
  refine ⟨fun x => ψ x * f x, hψ.mul hf, hψc.mul_right,
    tsupport_mul_subset_left.trans hψs, fun x => ?_⟩
  have hpg : ψ x * g x = g x := by
    by_cases hx : g x = 0
    · simp only [hx, mul_zero]
    · rw [hone x (subset_tsupport _ hx), one_mul]
  have heq : ψ x * f x - g x = ψ x * (f x - g x) := by rw [mul_sub, hpg]
  rw [heq, abs_mul, abs_of_nonneg (hb x).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hb x).2).trans (hclose x)

/-- Closed scalar truncation, embedded in native product coordinates. -/
def reconstructionTrim (H : Interval) (a T δ R : ℝ) :
    Set (ℝ × PDE.Vec 1 × PDE.Vec 1) :=
  (fun q : ℝ × ℝ × ℝ => (q.1, (fun _ : Fin 1 => q.2.1),
    (fun _ : Fin 1 => q.2.2))) ''
      (Icc a (T - δ) ×ˢ (Icc (H.lo + δ) (H.hi - δ) ×ˢ Icc (-R) R))

/-- The trimmed coordinate box is compact. -/
theorem isCompact_reconstructionTrim (H : Interval) (a T δ R : ℝ) :
    IsCompact (reconstructionTrim H a T δ R) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
    (continuous_fst.prodMk ((continuous_pi fun _ => continuous_snd.fst).prodMk
      (continuous_pi fun _ => continuous_snd.snd)))

/-- Membership in the trimmed box is exactly its scalar coordinate inequalities. -/
theorem mem_reconstructionTrim (H : Interval) (a T δ R : ℝ)
    (x : ℝ × PDE.Vec 1 × PDE.Vec 1) :
    x ∈ reconstructionTrim H a T δ R ↔
      a ≤ x.1 ∧ x.1 ≤ T - δ ∧ H.lo + δ ≤ x.2.1 0 ∧
        x.2.1 0 ≤ H.hi - δ ∧ |x.2.2 0| ≤ R := by
  constructor
  · rintro ⟨q, ⟨ht, hv, hx⟩, rfl⟩
    exact ⟨ht.1, ht.2, hv.1, hv.2, abs_le.mpr hx⟩
  · rintro ⟨htl, htu, hvl, hvu, hx⟩
    refine ⟨(x.1, x.2.1 0, x.2.2 0), ⟨⟨htl, htu⟩, ⟨hvl, hvu⟩, abs_le.mp hx⟩, ?_⟩
    change (x.1, (fun _ : Fin 1 => x.2.1 0), (fun _ : Fin 1 => x.2.2 0)) = x
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (funext i; fin_cases i; rfl)

/-- Interior source domain in native product coordinates. -/
def reconstructionSourceDomain (H : Interval) (sMinus T : ℝ) :
    Set (ℝ × PDE.Vec 1 × PDE.Vec 1) :=
  {x | sMinus < x.1 ∧ x.1 < T ∧ x.2.1 0 ∈ H.carrier}

/-- The native source domain is open. -/
theorem isOpen_reconstructionSourceDomain (H : Interval) (sMinus T : ℝ) :
    IsOpen (reconstructionSourceDomain H sMinus T) := by
  have heq : reconstructionSourceDomain H sMinus T =
      (Prod.fst ⁻¹' Ioo sMinus T) ∩
        ((fun x : ℝ × PDE.Vec 1 × PDE.Vec 1 => x.2.1 0) ⁻¹' H.carrier) := by
    ext x
    simp only [reconstructionSourceDomain, mem_ofPred, mem_inter_iff, mem_preimage,
      mem_Ioo, and_assoc]
  rw [heq]
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_snd.fst))

/-- The proper exponential weight bounds the absolute spatial coordinate. -/
theorem abs_le_reconstructionSpatialWeight (x : ℝ) :
    |x| ≤ reconstructionSpatialWeight x := by
  have hp := Real.add_one_le_exp x
  have hm := Real.add_one_le_exp (-x)
  have hxp := (Real.exp_pos x).le
  have hxm := (Real.exp_pos (-x)).le
  unfold reconstructionSpatialWeight
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith only [hp, hxm]
  · rw [abs_of_nonpos hx]
    linarith only [hm, hxp]

/-- The localization error weight, including terminal, velocity, and spatial collars. -/
def reconstructionErrorWeight (H : Interval) (T δ R : ℝ)
    (x : ℝ × PDE.Vec 1 × PDE.Vec 1) : ℝ :=
  Real.exp 1 * reconstructionCollarWeight H δ (x.2.1 0) +
    (if T - δ < x.1 then 1 else 0) + reconstructionSpatialWeight (x.2.2 0) / R

/-- Outside the trimmed box at future times, the localization error weight is at least one. -/
theorem reconstructionErrorWeight_ge_one (H : Interval) (a T : ℝ) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (x : ℝ × PDE.Vec 1 × PDE.Vec 1)
    (ha : a ≤ x.1) (hx : x ∉ reconstructionTrim H a T δ R) :
    1 ≤ reconstructionErrorWeight H T δ R x := by
  classical
  have hcol : 0 ≤ Real.exp 1 * reconstructionCollarWeight H δ (x.2.1 0) :=
    mul_nonneg (Real.exp_pos _).le (reconstructionCollarWeight_nonneg _ _ _)
  have hsp : 0 ≤ reconstructionSpatialWeight (x.2.2 0) / R :=
    div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hR.le
  unfold reconstructionErrorWeight
  by_cases ht : T - δ < x.1
  · rw [ite_eq_left ht]
    linarith only [hcol, hsp]
  · rw [ite_eq_right ht, add_zero]
    have htu := le_of_not_gt ht
    by_cases hl : H.lo + δ ≤ x.2.1 0
    · by_cases hh : x.2.1 0 ≤ H.hi - δ
      · have hs : R < |x.2.2 0| := lt_of_not_ge
          (fun hs => hx ((mem_reconstructionTrim H a T δ R x).mpr ⟨ha, htu, hl, hh, hs⟩))
        have hd : 1 ≤ reconstructionSpatialWeight (x.2.2 0) / R :=
          (le_div_iff₀ hR).mpr (by
            simpa only [one_mul] using hs.le.trans (abs_le_reconstructionSpatialWeight _))
        linarith only [hcol, hd]
      · have hs : H.hi - δ < x.2.1 0 := lt_of_not_ge hh
        have hd : -1 ≤ (x.2.1 0 - H.hi) / δ :=
          (le_div_iff₀ hδ).mpr (by linarith only [hs])
        have he : 1 ≤ Real.exp 1 * Real.exp ((x.2.1 0 - H.hi) / δ) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp_iff.mpr (by linarith only [hd])
        have hn := mul_nonneg (Real.exp_pos (1 : ℝ)).le
          (Real.exp_pos ((H.lo - x.2.1 0) / δ)).le
        unfold reconstructionCollarWeight
        nlinarith only [he, hn, hsp]
    · have hs : x.2.1 0 < H.lo + δ := lt_of_not_ge hl
      have hd : -1 ≤ (H.lo - x.2.1 0) / δ :=
        (le_div_iff₀ hδ).mpr (by linarith only [hs])
      have he : 1 ≤ Real.exp 1 * Real.exp ((H.lo - x.2.1 0) / δ) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith only [hd])
      have hn := mul_nonneg (Real.exp_pos (1 : ℝ)).le
        (Real.exp_pos ((x.2.1 0 - H.hi) / δ)).le
      unfold reconstructionCollarWeight
      nlinarith only [he, hn, hsp]

/-- Bounded continuous strip sources have actual smooth compact approximants with an
explicit pointwise collar error. -/
theorem exists_reconstruction_compact_source_approx
    (H : Interval) (sMinus a T : ℝ) (ha : sMinus < a) {δ R ε : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hε : 0 < ε)
    (g : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ)
    (hg : ContinuousOn g (reconstructionSourceDomain H sMinus T))
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ x, |g x| ≤ C) :
    ∃ f : (ℝ × PDE.Vec 1 × PDE.Vec 1) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ reconstructionSourceDomain H sMinus T ∧
      ∀ x, a ≤ x.1 →
        |f x - g x| ≤ ε + C * reconstructionErrorWeight H T δ R x := by
  have hU := isOpen_reconstructionSourceDomain H sMinus T
  have hKU : reconstructionTrim H a T δ R ⊆ reconstructionSourceDomain H sMinus T := by
    intro x hx
    obtain ⟨htl, htu, hvl, hvu, _⟩ := (mem_reconstructionTrim H a T δ R x).mp hx
    exact ⟨ha.trans_le htl, by linarith only [htu, hδ],
      by constructor <;> linarith only [hvl, hvu, hδ]⟩
  obtain ⟨χ, hχ, hc, hs, hb, hone⟩ := exists_smooth_bump_of_isCompact_subset_isOpen
    (isCompact_reconstructionTrim H a T δ R) hU hKU
  have hcont := reconstruction_cutoff_mul_continuous hU hg hχ.continuous hs
  have hcomp : HasCompactSupport (fun x => χ x * g x) := hc.mul_right
  obtain ⟨f, hf, hfc, hfs, hclose⟩ := reconstruction_smooth_compact_close hU
    (fun x => χ x * g x) hcont hcomp (tsupport_mul_subset_left.trans hs) hε
  refine ⟨f, hf, hfc, hfs, fun x hax => ?_⟩
  have hweight : 0 ≤ reconstructionErrorWeight H T δ R x := by
    unfold reconstructionErrorWeight
    exact add_nonneg (add_nonneg
      (mul_nonneg (Real.exp_pos _).le (reconstructionCollarWeight_nonneg _ _ _))
      (by split_ifs <;> norm_num))
      (div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hR.le)
  have herror : |χ x * g x - g x| ≤ C * reconstructionErrorWeight H T δ R x := by
    by_cases hx : x ∈ reconstructionTrim H a T δ R
    · rw [hone _ hx, one_mul, sub_self, abs_zero]
      exact mul_nonneg hC hweight
    · have he : χ x * g x - g x = -(1 - χ x) * g x := by ring
      rw [he, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      have hh : (1 - χ x) * |g x| ≤ C :=
        (mul_le_of_le_one_left (abs_nonneg _) (by linarith only [(hb x).1])).trans (hgb x)
      exact hh.trans (le_mul_of_one_le_right hC
        (reconstructionErrorWeight_ge_one H a T hδ hR x hax hx))
  have heq : f x - g x = (f x - χ x * g x) + (χ x * g x - g x) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (hclose x) herror)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
