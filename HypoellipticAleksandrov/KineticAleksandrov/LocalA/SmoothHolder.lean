module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolderNormalized
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothLocalStatement
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic

/-! # Smooth local regularity conditional only on the spatial derivative bound

The spatial-bound theorem is the sole
hypothesis. All kinetic normalization and Hölder
combination steps are proved here. The joint statement is not claimed unconditionally.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Holder SectionTwo
open scoped ContDiff MatrixOrder Matrix.Norms.Elementwise

/-- Smooth time--velocity coefficients with pointwise bounds meet the Section 2 premises. -/
theorem sectionTwo_of_smooth_bounds {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) {A : CoefficientField d}
    (hA : IsSmoothCoefficient A) (hs : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    IsSectionTwoCoefficient lam Lam A := by
  refine ⟨hlam, hLam, ?_, hs, hlo, hhi⟩
  intro i j
  have hentry : ContDiff ℝ ∞ (fun z : TimeVelocity d => coefficientAt A z i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hA
  exact hentry.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))

/-- The exact joint smooth conditions follows from the sole authorized LA-08 input. -/
theorem smoothLocalRegularityStatement_holds_of_spatial_bounds
    (hsp : ∀ (_hH : HormanderHypoellipticityStatement)
      (_hLE : LiebermanEllipsoidDirichletStatement)
      (d : ℕ) (_hd : 1 ≤ d) (lam Lam : ℝ) (_hlam : 0 < lam) (_hLam : lam ≤ Lam),
      ∃ C_m : ℕ → ℝ, (∀ m, 0 ≤ C_m m) ∧
        ∀ (A : CoefficientField d), IsSectionTwoCoefficient lam Lam A →
        ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
        ∀ (u : KineticPoint d → ℝ),
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
        (∀ P ∈ backwardCylinder P₀ R,
          ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
        ∀ (m : ℕ), 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
          R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
            C_m m * oscillationOn u (backwardCylinder P₀ R)) :
    SmoothLocalRegularityStatement := by
  intro hH hLE d hd lam Lam hlam hLam
  obtain ⟨C_m, hCm, hspatial⟩ := hsp hH hLE d hd lam Lam hlam hLam
  obtain ⟨C, α, hC, hα, hα1, hholder⟩ :=
    normalized_holder_from_slice_jets hLE d hd lam Lam hlam hLam (C_m 1) (hCm 1)
  refine ⟨C_m, C, α, hCm, hC, hα, hα1, ?_⟩
  intro A hA hs hloAE hhiAE P₀ R hR u hc hu he
  obtain ⟨hlo, hhi⟩ := TheoremA.ellipticity_of_smooth_ae hA hloAE hhiAE
  have hsec := sectionTwo_of_smooth_bounds hlam hLam hA hs hlo hhi
  obtain ⟨hsm, hder⟩ := hspatial A hsec P₀ R hR u hc hu he
  refine ⟨hsm, hder, ?_⟩
  let Z : KineticPoint d := ⟨0, 0, 0⟩
  let U := kineticPullback u P₀ R
  let B := kineticPullbackCoefficient A P₀ R
  have hB := kineticPullbackCoefficient_smooth hA P₀ R
  obtain ⟨hBs, hBlo, hBhi⟩ := kineticPullbackCoefficient_bounds hs hlo hhi P₀ R
  obtain ⟨hU, hUe⟩ := kineticPullback_normalized P₀ hR hu hA he
  have hUc := continuousOn_kineticPullback_closure P₀ hR hc
  have hBsec := sectionTwo_of_smooth_bounds hlam hLam hB hBs hBlo hBhi
  have hUae : ∀ᵐ P ∂volume.restrict (backwardCylinder Z 1),
      backwardOperatorOfTimeVelocityCoefficient B U P = 0 := by
    filter_upwards [ae_restrict_mem (isOpen_backwardCylinder Z 1 (by norm_num)).measurableSet]
      with P hP
    exact hUe P hP
  have hgrad : ∀ P ∈ backwardCylinder Z (3 / 4),
      ‖fderiv ℝ (physicalPositionSlice U P) P.position‖ ≤
        C_m 1 * oscillationOn U (backwardCylinder Z 1) := by
    intro P hP
    have hg := (hspatial B hBsec Z 1 (by norm_num) U hUc hU hUae).2 1 (by norm_num) P
      (by simpa only [mul_one] using hP)
    simpa only [one_pow, one_mul, norm_iteratedFDeriv_one] using hg
  have hmod := hholder B hB hBs hBlo hBhi U hUc hU hUe hgrad
  intro P hP Q hQ
  let p := kineticAffineInverse P₀ R P
  let q := kineticAffineInverse P₀ R Q
  have hp : kineticAffine P₀ R p = P := kineticAffine_apply_inverse P₀ hR.ne' P
  have hq : kineticAffine P₀ R q = Q := kineticAffine_apply_inverse P₀ hR.ne' Q
  have hp' : p ∈ backwardCylinder Z (1 / 2) := by
    apply (kineticAffine_mem_radius P₀ p hR (by norm_num : (0 : ℝ) < 1 / 2)).mp
    simpa only [hp, mul_one_div] using hP
  have hq' : q ∈ backwardCylinder Z (1 / 2) := by
    apply (kineticAffine_mem_radius P₀ q hR (by norm_num : (0 : ℝ) < 1 / 2)).mp
    simpa only [hq, mul_one_div] using hQ
  have h := hmod p hp' q hq'
  have hi := kineticIncrement_kineticAffine P₀ p q hR
  rw [hp, hq] at hi
  have ho := oscillationOn_kineticPullback u P₀ hR
  change |u (kineticAffine P₀ R p) - u (kineticAffine P₀ R q)| ≤ _ at h
  rw [hp, hq] at h
  rw [ho, ← hi] at h
  exact h

/-- Smooth kinetic Hölder continuity with constants chosen before the local data. -/
theorem smooth_timeVelocity_holder_of_spatial_bounds
    (hsp : ∀ (_hH : HormanderHypoellipticityStatement)
      (_hLE : LiebermanEllipsoidDirichletStatement)
      (d : ℕ) (_hd : 1 ≤ d) (lam Lam : ℝ) (_hlam : 0 < lam) (_hLam : lam ≤ Lam),
      ∃ C_m : ℕ → ℝ, (∀ m, 0 ≤ C_m m) ∧
        ∀ (A : CoefficientField d), IsSectionTwoCoefficient lam Lam A →
        ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
        ∀ (u : KineticPoint d → ℝ),
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
        (∀ P ∈ backwardCylinder P₀ R,
          ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice u P) P.position) ∧
        ∀ (m : ℕ), 1 ≤ m → ∀ P ∈ backwardCylinder P₀ (3 * R / 4),
          R ^ (3 * m) * ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
            C_m m * oscillationOn u (backwardCylinder P₀ R))
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α < 1 ∧
      ∀ (A : CoefficientField d),
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (u : KineticPoint d → ℝ),
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
        ∀ P ∈ backwardCylinder P₀ (R / 2),
        ∀ Q ∈ backwardCylinder P₀ (R / 2),
          |u P - u Q| ≤ C * oscillationOn u (backwardCylinder P₀ R) *
            (kineticIncrement P₀ P Q / R) ^ α := by
  obtain ⟨C_m, C, α, _, hC, hα, hα1, hreg⟩ :=
    smoothLocalRegularityStatement_holds_of_spatial_bounds hsp
      hH hLE d hd lam Lam hlam hLam
  refine ⟨C, α, hC, hα, hα1, ?_⟩
  intro A hA hs hlo hhi P₀ R hR u hc hu he
  exact (hreg A hA hs hlo hhi P₀ R hR u hc hu he).2.2

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
