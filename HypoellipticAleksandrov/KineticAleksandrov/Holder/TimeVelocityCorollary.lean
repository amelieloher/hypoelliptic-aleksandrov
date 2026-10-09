module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.LocalStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.TimeVelocityCorollaryGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic

/-! # Time–velocity Hölder corollary conditional on the exact joint local theorem

The local theorem is still an unproved input boundary. Constants precede all
coefficient, domain, solution, compact-set and radius data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder LocalA
open scoped MatrixOrder

/-- The time-velocity Holder conclusion, conditional on the local regularity statement. -/
theorem kinetic_holder_timeVelocity_relative_of_local
    (hlocal : LocalTimeVelocityRegularityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  obtain ⟨Cm, D, alpha, _hCm, hD, ha, ha1, hreg⟩ :=
    hlocal hH hLE d hd lam Lam hlam hLam
  let C := max D ((4 : ℝ) ^ alpha)
  have hC : 0 < C := hD.trans_le (le_max_left _ _)
  refine ⟨alpha, C, ha, ha1.le, ?_⟩
  intro A hmeas hsym hlo hhi Omega _hOmega u _hbounded hu heq K _hKO hK R0 hR0 hQ
  let E := holderNeighbourhood R0 K
  obtain ⟨hclosed, hcompact⟩ := holder_neighbourhood_compact K hK R0 hR0
  have hEO : closure E ⊆ Omega := by
    rw [hclosed]
    intro Z hZ
    simp only [mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact hQ P hP hZ
  have hcont : ContinuousOn u (closure E) := hu.continuousOn.mono hEO
  have habc : BddAbove (u '' closure E) := hcompact.bddAbove_image hcont
  have hbbc : BddBelow (u '' closure E) := hcompact.bddBelow_image hcont
  have hab : BddAbove (u '' E) := habc.mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := hbbc.mono (image_mono subset_closure)
  have hcenter (P : KineticPoint d) (hP : P ∈ K) : P ∈ closure E := by
    rw [hclosed]
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP,
      Covering.top_mem_closure_cylinder P (by positivity : 0 < 2 * R0)
        (PDE.center_mem_euclideanBall _ (by positivity))⟩⟩
  have hpair (P : KineticPoint d) (hP : P ∈ K) (Q : KineticPoint d) (hQK : Q ∈ K)
      (ht : P.time ≤ Q.time) :
      |u P - u Q| ≤ C * oscillationOn u E * (quasiDistance P Q / R0) ^ alpha := by
    have hne : E.Nonempty := by
      obtain ⟨Z, hZ⟩ := backwardCylinder_nonempty Q (by positivity : 0 < 2 * R0)
      exact ⟨Z, mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨hQK, hZ⟩⟩⟩
    have hosc := oscillationOn_nonneg hne hab hbb
    have hosccl := oscillationOn_closure hne hcompact hcont
    have hdelta := quasiDistance_nonneg P Q
    by_cases hz : quasiDistance P Q = 0
    · have he := (quasiDistance_eq_zero_iff P Q).mp hz
      rw [congrArg u he, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le hosc)
        (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)
    have hdpos : 0 < quasiDistance P Q := lt_of_le_of_ne hdelta (Ne.symm hz)
    by_cases hnear : quasiDistance P Q < R0 / 4
    · have hhalf : 0 < R0 / 2 := by positivity
      have hdhalf : quasiDistance P Q ≤ R0 / 2 := by linarith only [hnear, hR0]
      obtain ⟨hpcl, hqcl⟩ := pair_mem_closed_later_cylinder P Q ht hdpos
      have hsubhalf := closure_mono (backwardCylinder_radius_mono Q hdpos hdhalf)
      have hsub : backwardCylinder Q R0 ⊆ backwardCylinder Q (2 * R0) :=
        backwardCylinder_radius_mono Q hR0 (by linarith only [hR0])
      have hsmallO : closure (backwardCylinder Q R0) ⊆ Omega :=
        (closure_mono hsub).trans (hQ Q hQK)
      have hsmall : backwardCylinder Q R0 ⊆ Omega := subset_closure.trans hsmallO
      have huSmall : Parabolic.IsKineticC112On u (backwardCylinder Q R0) := by
        refine ⟨hu.1.mono hsmall, ?_, ?_, ?_, hu.2.2.2.2.1.mono hsmall,
          hu.2.2.2.2.2.1.mono hsmall, hu.2.2.2.2.2.2.1.mono hsmall,
          hu.2.2.2.2.2.2.2.mono hsmall⟩
        · exact fun Z hZ => hu.2.1 Z (hsmall hZ)
        · exact fun Z hZ => hu.2.2.1 Z (hsmall hZ)
        · exact fun Z hZ => hu.2.2.2.1 Z (hsmall hZ)
      have huc := hu.continuousOn.mono hsmallO
      have hestimate := (hreg A hmeas hsym hlo hhi Q R0 hR0 u huc huSmall
        (ae_restrict_of_ae_restrict_of_subset hsmall heq)).2.2
      have hhalfsub : closure (backwardCylinder Q (R0 / 2)) ⊆
          closure (backwardCylinder Q R0) :=
        closure_mono (backwardCylinder_radius_mono Q hhalf (by linarith only [hR0]))
      have hbound := local_estimate_on_closure Q ha.le u (huc.mono hhalfsub)
        hestimate (hsubhalf hpcl) (hsubhalf hqcl)
      have hbigE : backwardCylinder Q R0 ⊆ E := fun Z hZ =>
        mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨hQK, hsub hZ⟩⟩
      have hsmallosc := oscillationOn_nonneg (backwardCylinder_nonempty Q hR0)
        (hab.mono (image_mono hbigE)) (hbb.mono (image_mono hbigE))
      have hoscmono := oscillationOn_mono (backwardCylinder_nonempty Q hR0) hbigE hab hbb
      have hincnonneg : 0 ≤ kineticIncrement Q P Q := by
        exact add_nonneg
          (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (PDE.vecEuclideanNorm_nonneg _))
          (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
      have hpower := Real.rpow_le_rpow (div_nonneg hincnonneg hR0.le)
        (div_le_div_of_nonneg_right (kineticIncrement_later_le_distance P Q) hR0.le)
        ha.le
      exact hbound.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_left D _) hoscmono hsmallosc hC.le)
        (Real.rpow_nonneg (div_nonneg hincnonneg hR0.le) _)).trans
        (mul_le_mul_of_nonneg_left hpower (mul_nonneg hC.le hosc)))
    · have hbase := abs_sub_le_oscillationOn habc hbbc (hcenter P hP) (hcenter Q hQK)
      rw [hosccl] at hbase
      have hratio : 1 / 4 ≤ quasiDistance P Q / R0 := by
        apply (le_div_iff₀ hR0).mpr
        have hh := le_of_not_gt hnear
        linarith only [hh]
      have hpower := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hratio ha.le
      have hfour : (4 : ℝ) ^ alpha * (1 / 4 : ℝ) ^ alpha = 1 := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by norm_num)]
        norm_num
      have hcoeff : 1 ≤ C * (quasiDistance P Q / R0) ^ alpha := by
        rw [← hfour]
        exact mul_le_mul (le_max_right D _) hpower (Real.rpow_nonneg (by norm_num) _)
          hC.le
      have hb := mul_le_mul_of_nonneg_right hcoeff hosc
      rw [one_mul] at hb
      exact hbase.trans (hb.trans_eq (by ring))
  intro P hP Q hQK
  rcases le_total P.time Q.time with ht | ht
  · exact hpair P hP Q hQK ht
  · have hb := hpair Q hQK P hP ht
    simpa only [abs_sub_comm, quasiDistance_symm Q P] using hb

end HypoellipticAleksandrov.KineticAleksandrov
