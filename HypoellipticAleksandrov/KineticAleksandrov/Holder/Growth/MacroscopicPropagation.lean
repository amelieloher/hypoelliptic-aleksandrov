module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationInitial
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationDimensionless
import Mathlib.Tactic

/-! # Uniform macroscopic propagation through the constructed buffered reference region -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- A cap on a sampling cylinder of radius at least `r0` controls the entire target cylinder.
The cap premise is the local near-full conclusion, to be discharged by the density argument. -/
theorem exists_macroscopic_cap_constant (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (m : ℕ) (r0 : ℝ)
    (hr0 : 0 < r0) (hr01 : r0 < 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (scale : ℝ), 0 < scale →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ Z ∈ O, 0 ≤ u Z) →
        IsAdmissibleSupersolution A O p C_A u →
      ∀ (Q : KineticPoint d) (r ell : ℝ), r0 ≤ r →
        backwardCylinder Q r ⊆ samplingCylinder d m → 0 ≤ ell →
        (∀ Z ∈ kineticAffine (kineticAffine P0 scale Q) (scale * r) '' cap d,
          ell ≤ u Z) →
        ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
          c * ell ≤ u (kineticAffine P0 scale P) := by
  let M := (m : ℝ) + 3
  have hM : 0 < M := by dsimp only [M]; positivity
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hr02 : r0 ^ 2 ≤ 1 := by nlinarith only [hr0, hr01]
  have hr03 : r0 ^ 3 ≤ 1 := by
    exact (pow_le_pow_left₀ hr0.le hr01.le 3).trans_eq (by norm_num)
  obtain ⟨c, hc, hc1, hprop⟩ := propagation_dimensionless d hd lam Lam
    (r0 ^ 2 / (32 * M)) (macroscopicAcceleration m * Real.sqrt M)
    (r0 ^ 3 / (1024 * M ^ (3 / 2 : ℝ))) (r0 / (16 * Real.sqrt M))
    hlam hLam (by positivity) (by
      apply (div_le_one (by positivity : 0 < 32 * M)).mpr
      dsimp only [M]
      linarith only [hr02, hm])
    (by unfold macroscopicAcceleration; positivity) (by positivity) (by positivity)
  refine ⟨c, hc, hc1, ?_⟩
  intro p C_A hp A hA P0 scale hscale O hO hregion u hnonneg hu Q r ell hr hQ hell hcap
    P hP
  have hrp : 0 < r := hr0.trans_le hr
  let S : KineticPoint d := ⟨stackStartTime Q r, stackStartPosition Q r, Q.velocity⟩
  have hS : S ∈ closure (samplingCylinder d m) := sampling_cap_center_mem m Q hrp hQ
  obtain ⟨x, v, _, _, _, hxP, hvP, hleft, hvc, hxd, hLip, hcorr⟩ :=
    exists_reference_corridor m S P hS hP
  obtain ⟨hTlo, hThi, _, _⟩ := reference_endpoint_bounds m S P hS hP
  let tminus := (kineticAffine P0 scale S).time
  let TP := scale ^ 2 * (P.time - S.time)
  have ht : (kineticAffine P0 scale P).time - tminus = TP := by
    dsimp only [kineticAffine, tminus, TP]
    ring
  have htminus : tminus = P0.time + scale ^ 2 * S.time := rfl
  have hTPlo : (r0 ^ 2 / 32) * scale ^ 2 ≤ TP := by
    have he := mul_le_mul_of_nonneg_left hTlo (sq_nonneg scale)
    dsimp only [TP]
    have hn : r0 ^ 2 / 32 ≤ (m : ℝ) + 1 := by linarith only [hr02, hm]
    exact (mul_le_mul_of_nonneg_right hn (sq_nonneg scale)).trans (by
      simpa only [mul_comm] using he)
  have hTPhi : TP ≤ M * scale ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hThi (sq_nonneg scale)).trans_eq (mul_comm _ _)
  obtain ⟨hscT, hscH, hscX, hscV⟩ := macroscopic_propagation_scaling m r0 hscale
  let xp := physicalPathPosition P0 scale S.time x
  let vp := physicalPathVelocity P0 scale v
  have hsk := physicalPath_isSkeleton P0 hscale S.time
    (-((r0 ^ 2 / 32) * scale ^ 2)) TP hvc hxd hLip
  obtain ⟨hxend, hvend⟩ := physicalPath_endpoint P0 S P hscale.ne' x v hxP hvP
  have hcphys : corridor tminus (-((r0 ^ 2 / 32) * scale ^ 2)) TP
      ((r0 ^ 3 / 1024) * scale ^ 3) ((r0 / 16) * scale) xp vp ⊆ O := by
    apply Subset.trans _ (fun Z hZ => hregion (subset_closure hZ))
    apply Subset.trans _ (physical_corridor_subset_image P0 hscale S.time
      (P.time - S.time) x v _ hcorr)
    rw [htminus]
    apply corridor_mono
    · nlinarith only [mul_le_mul_of_nonneg_right hr02 (sq_nonneg scale), sq_nonneg scale]
    · exact le_rfl
    · nlinarith only [mul_le_mul_of_nonneg_right hr03 (pow_nonneg hscale.le 3),
        pow_nonneg hscale.le 3]
    · nlinarith only [mul_le_mul_of_nonneg_right hr01.le hscale.le, hscale]
  have hPO : kineticAffine P0 scale P ∈ O :=
    hregion (subset_closure ⟨P, unitCylinder_subset_reference d m hP, rfl⟩)
  have hcapInitial := macroscopic_initial_subset_cap P0 Q hscale hr0 hr x v hleft
  have hfinal := hprop (M * scale ^ 2) (mul_pos hM (sq_pos_of_pos hscale))
    p C_A hp A hA O hO tminus (kineticAffine P0 scale P) hPO
  rw [ht, neg_mul, hscT, hscH, hscX, hscV] at hfinal
  apply hfinal hTPlo hTPhi xp vp
    (by simpa only [macroscopicAcceleration] using hsk) hxend hvend hcphys
    ell hell u hnonneg hu
  intro Z hZ htZ
  apply hcap Z
  apply hcapInitial
  exact ⟨⟨hZ.1.1, sub_nonpos.mpr htZ⟩, hZ.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
