module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.JointWitness
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.DensityLadderAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.TerminalLevelArithmetic
import Mathlib.Tactic

/-! # All-density positivity from the proved ink-spots and macroscopic comparisons -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set MeasureTheory Covering

/-- All-density growth with coefficient conditions grouped only by their literal abbreviation. -/
theorem exists_growth_parameters (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      ∃ (Psigma : KineticPoint d) (rsigma : ℝ), 0 < rsigma ∧
        closure (backwardCylinder Psigma rsigma) ⊆
          backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
        ∀ beta : ℝ, 0 < beta → beta ≤ 1 → ∃ kappa : ℝ, 0 < kappa ∧
          ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
          ∀ (P0 : KineticPoint d) (R : ℝ), 0 < R →
          ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P0 R) ⊆ O →
          ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
            IsAdmissibleSupersolution A O p C_A u →
            beta * (volume (kineticAffine P0 R '' backwardCylinder Psigma rsigma)).toReal ≤
              (volume ({P | 1 ≤ u P} ∩
                kineticAffine P0 R '' backwardCylinder Psigma rsigma)).toReal →
            ∀ P ∈ backwardCylinder P0 (theta * R), kappa ≤ u P := by
  obtain ⟨c, C, hc, hc1, hC, hink⟩ := exists_affine_ink_spots_constants d hd
  obtain ⟨eta, m, delta, eps, heta, heta1, hm, ha, ha1, hdelt, hdelt1,
    heps, heps1, hscaled, hsigma, hnear, hstack⟩ :=
    exists_joint_growth_parameters d hd lam Lam p C_A hlam hLam hp c hc hc1
  let a := (((m : ℝ) + 1) / (m : ℝ)) * (1 - c * eta)
  let V := (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (volume_cylinder_pos_ne_top _ zero_lt_one).1.ne'
    (volume_cylinder_pos_ne_top _ zero_lt_one).2
  refine ⟨eps, heps, heps1,
    kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps (samplingCenter d m),
    eps, heps, ?_, ?_⟩
  · rw [← physical_sampling_image _ heps m]
    exact hsigma
  intro beta hbeta _hbeta1
  obtain ⟨N, hN, _, r0, hr0, hr01, herror⟩ :=
    exists_density_leakage_choice ha ha1 heta1 hbeta hC hV m hm
  obtain ⟨cmac, hcmac, _, hmacro⟩ :=
    exists_physical_macroscopic_cap_constant d hd lam Lam hlam hLam m r0 hr0 hr01
  let kappa := (3 / 4 : ℝ) * cmac * delta ^ N
  refine ⟨kappa, by dsimp only [kappa]; positivity, ?_⟩
  intro A hA P0 R hR O hO hdomain u hnonneg hu hdensity
  let scale := R * eps
  have hscale : 0 < scale := mul_pos hR heps
  let G := kineticAffine P0 scale '' referenceRegion d m (referenceBound m)
  let S := kineticAffine P0 scale (samplingCenter d m)
  let Sigma := backwardCylinder S scale
  have hGO : closure G ⊆ O :=
    buffered_reference_preserves_domain P0 hR m hscaled O hdomain
  have hSigmaO : closure Sigma ⊆ O :=
    (physical_sampling_closure_subset P0 hscale m).trans hGO
  have hSigmaG : Sigma ⊆ G := by
    dsimp only [Sigma, S]
    rw [← physical_sampling_image P0 hscale m]
    exact image_mono (subset_closure.trans
      (sampling_closure_subset_reference d m (referenceBound_large m)))
  have hGb : Bornology.IsBounded G := isBounded_kineticAffine_image P0 scale
    (isBounded_referenceRegion d m (by linarith only [referenceBound_large m]))
  have hGopen : IsOpen G := (kineticAffineHomeomorph P0 scale hscale.ne').isOpenMap _
    (isOpen_referenceRegion d m (referenceBound m))
  have hSigmab : Bornology.IsBounded Sigma :=
    (isCompact_closure_backwardCylinder S scale hscale).isBounded.subset subset_closure
  have hSigmaMeas : MeasurableSet Sigma := (isOpen_cylinder S scale).measurableSet
  let E := fun j : ℕ => {P | delta ^ j ≤ u P} ∩ Sigma
  let F := fun j : ℕ => {P | delta ^ (j + 1) ≤ u P} ∩ G
  have hEMeas (j : ℕ) : MeasurableSet (E j) := measurableSet_superlevel_inter hO
    hSigmaMeas (subset_closure.trans hSigmaO) hu.1 _
  have hFMeas (j : ℕ) : MeasurableSet (F j) := measurableSet_superlevel_inter hO
    hGopen.measurableSet (subset_closure.trans hGO) hu.1 _
  have hEb (j : ℕ) : Bornology.IsBounded (E j) :=
    superlevel_inter_isBounded hSigmab u _
  have hFb (j : ℕ) : Bornology.IsBounded (F j) :=
    superlevel_inter_isBounded hGb u _
  have hdown (j : ℕ) : delta ^ (j + 1) ≤ delta ^ j := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hdelt.le j) hdelt1.le
  have hEF (j : ℕ) : E j ⊆ F j ∩ Sigma := by
    intro P hP
    exact ⟨⟨(hdown j).trans hP.1, hSigmaG hP.2⟩, hP.2⟩
  have hFQ (j : ℕ) : F j ∩ Sigma = E (j + 1) := by
    ext P
    constructor
    · intro hP; exact ⟨hP.1.1, hP.2⟩
    · intro hP; exact ⟨⟨hP.1, hSigmaG hP.2⟩, hP.2⟩
  have hlocalLevel (j : ℕ) (Q : KineticPoint d) (r : ℝ)
      (hsub : backwardCylinder Q r ⊆ Sigma) :
      E j ∩ backwardCylinder Q r = {Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r := by
    ext Z
    constructor
    · intro hZ; exact ⟨hZ.1.1, hZ.2⟩
    · intro hZ; exact ⟨⟨hZ.1, hsub hZ.2⟩, hZ.2⟩
  have hmacDensity (j : ℕ) (Q : KineticPoint d) (r : ℝ) (hr : 0 < r)
      (hsub : backwardCylinder Q r ⊆ Sigma) (hbig : r0 * scale ≤ r)
      (hden : (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
        (volume ({Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r)).toReal) :
      ∀ Z ∈ backwardCylinder P0 scale, (3 / 4 : ℝ) * cmac * delta ^ j ≤ u Z := by
    have hQO : closure (backwardCylinder Q r) ⊆ O := (closure_mono hsub).trans hSigmaO
    have hcap := hnear A hA Q r (delta ^ j) hr (pow_nonneg hdelt.le j)
      O hO hQO u hnonneg hu hden
    have hb := hmacro p C_A hp A hA P0 scale hscale O hO hGO u hnonneg hu
      Q r ((3 / 4 : ℝ) * delta ^ j) hr hbig hsub (by positivity) hcap
    intro Z hZ
    convert hb Z hZ using 1
    ring
  have hSigmaVol : (volume Sigma).toReal = scale ^ (4 * d + 2) * V := by
    dsimp only [Sigma]
    rw [← kineticAffine_image_unitCylinder S hscale, volume_affine_image_toReal S hscale]
  have hSigmaVolPos : 0 < (volume Sigma).toReal := by rw [hSigmaVol]; positivity
  have hphysicalSigma : kineticAffine P0 R ''
      backwardCylinder
        (kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps (samplingCenter d m)) eps = Sigma := by
    rw [← physical_sampling_image _ heps m]
    rw [image_image]
    have hc0 : kineticAffine P0 R ∘ kineticAffine (⟨0, 0, 0⟩ : KineticPoint d) eps =
        kineticAffine P0 scale := by
      rw [kineticAffine_comp]
      congr 1
      ext i <;> simp [kineticAffine]
    rw [← Function.comp_def, hc0, physical_sampling_image P0 hscale m]
  rw [hphysicalSigma] at hdensity
  have htarget : backwardCylinder P0 (eps * R) = backwardCylinder P0 scale := by
    dsimp only [scale]
    rw [mul_comm eps R]
  rw [htarget]
  by_cases hmac : ∃ j : ℕ, j < N ∧ ∃ (Q : KineticPoint d) (r : ℝ),
      0 < r ∧ backwardCylinder Q r ⊆ Sigma ∧ r0 * scale ≤ r ∧
      (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
        (volume ({Z | delta ^ j ≤ u Z} ∩ backwardCylinder Q r)).toReal
  · obtain ⟨j, hj, Q, r, hr, hsub, hbig, hden⟩ := hmac
    have hpow : delta ^ N ≤ delta ^ j :=
      pow_le_pow_of_le_one hdelt.le hdelt1.le hj.le
    intro Z hZ
    exact (mul_le_mul_of_nonneg_left hpow (by positivity :
      0 ≤ (3 / 4 : ℝ) * cmac)).trans (hmacDensity j Q r hr hsub hbig hden Z hZ)
  let e := fun j : ℕ => (volume (E j)).toReal / (volume Sigma).toReal
  let L0 := C * (m : ℝ) * r0 ^ 2 / V
  have hzero : beta ≤ e 0 := by
    apply (le_div_iff₀ hSigmaVolPos).mpr
    simpa only [E, pow_zero] using hdensity
  have hstep (j : ℕ) (hj : j < N) : e j ≤ a * (e (j + 1) + L0) := by
    have hcriterion (Q : KineticPoint d) (r : ℝ) (hr : 0 < r)
        (hsub : backwardCylinder Q r ⊆ Sigma)
        (hden : (1 - eta) * (volume (backwardCylinder Q r)).toReal ≤
          (volume (E j ∩ backwardCylinder Q r)).toReal) :
        r < r0 * scale ∧ forwardStack Q r m ⊆ F j := by
      rw [hlocalLevel j Q r hsub] at hden
      have hsmall : r < r0 * scale := by
        by_contra hs
        exact hmac ⟨j, hj, Q, r, hr, hsub, le_of_not_gt hs, hden⟩
      refine ⟨hsmall, ?_⟩
      have hcomp := physical_sampling_comparison_image_subset P0 Q hscale hr m hsub
      have hcompO := (closure_mono hcomp).trans hGO
      have hvis := hstack A hA Q r (delta ^ j) hr (pow_nonneg hdelt.le j)
        O hO hcompO u hnonneg hu hden
      intro Z hZ
      exact ⟨by simpa only [mem_ofPred_eq, pow_succ, mul_comm delta] using hvis Z hZ,
        hcomp (forwardStack_subset_comparison Q hr m hZ)⟩
    have hb := hink m hm eta r0 heta heta1 hr0 hr01 S scale hscale
      (E j) (F j) (hEb j) (hFb j) (hEMeas j) (hFMeas j) (hEF j) hcriterion
    rw [hFQ j] at hb
    apply (div_le_iff₀ hSigmaVolPos).mpr
    have heq : a * (e (j + 1) + L0) * (volume Sigma).toReal =
        a * ((volume (E (j + 1))).toReal + scale ^ (4 * d + 2) * C * (m : ℝ) * r0 ^ 2) := by
      dsimp only [e, L0]
      rw [hSigmaVol]
      field_simp
    rw [heq]
    exact hb
  have hterminal := density_ladder_numeric ha e N hzero hstep
  have hterminalDense : 1 - eta < e N := by linarith only [hterminal, herror]
  have hdenSigma : (1 - eta) * (volume Sigma).toReal ≤
      (volume ({Z | delta ^ N ≤ u Z} ∩ Sigma)).toReal :=
    (le_div_iff₀ hSigmaVolPos).mp hterminalDense.le
  have hbigSigma : r0 * scale ≤ scale :=
    (mul_le_mul_of_nonneg_right hr01.le hscale.le).trans_eq (one_mul scale)
  exact hmacDensity N S scale hscale Subset.rfl hbigSigma hdenSigma

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
