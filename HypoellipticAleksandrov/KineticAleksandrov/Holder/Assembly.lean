module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
import Mathlib.Tactic

/-! # The kinetic Holder theorem from the proved growth and oscillation estimates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder
open scoped ENNReal MatrixOrder

/-- The kinetic Holder theorem, conditional only on its admissibility predicate. -/
theorem kinetic_holder_of_aleksandrov_aux
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsAdmissibleSolution A Omega p C_A u →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha  := by
  obtain ⟨alpha, D, ha, ha1, hdecay⟩ := oscillation_decay d hd lam Lam p C_A hlam hLam hp
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro A hmeas hsym hlo hhi Omega hOmega u _hbounded hu K _hKO hK R0 hR0 hQ
  have hA : FullElliptic lam Lam A := ⟨hmeas, hsym, hlo, hhi⟩
  let E := holderNeighbourhood R0 K
  obtain ⟨hclosed, hcompact⟩ := holder_neighbourhood_compact K hK R0 hR0
  have hEO : closure E ⊆ Omega := by
    rw [hclosed]
    intro Z hZ
    simp only [mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact hQ P hP hZ
  have hcont : ContinuousOn u (closure E) := hu.1.1.mono hEO
  have habc : BddAbove (u '' closure E) := hcompact.bddAbove_image hcont
  have hbbc : BddBelow (u '' closure E) := hcompact.bddBelow_image hcont
  have hab : BddAbove (u '' E) := habc.mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := hbbc.mono (image_mono subset_closure)
  have hcenter (P : KineticPoint d) (hP : P ∈ K) : P ∈ closure E := by
    rw [hclosed]
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP,
      Covering.top_mem_closure_cylinder P (by positivity : 0 < 2 * R0)
        (PDE.center_mem_euclideanBall _ (by positivity))⟩⟩
  have hpair (P : KineticPoint d) (hP : P ∈ K) (P' : KineticPoint d) (hP' : P' ∈ K)
      (ht : P.time ≤ P'.time) :
      |u P - u P'| ≤ C * oscillationOn u E * (quasiDistance P P' / R0) ^ alpha := by
    have hne : E.Nonempty := by
      obtain ⟨Z, hZ⟩ := backwardCylinder_nonempty P (by positivity : 0 < 2 * R0)
      exact ⟨Z, mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hZ⟩⟩⟩
    have hosc := oscillationOn_nonneg hne hab hbb
    have hosccl : oscillationOn u (closure E) = oscillationOn u E :=
      oscillationOn_closure hne hcompact hcont
    have hdelta := quasiDistance_nonneg P P'
    by_cases hz : quasiDistance P P' = 0
    · have heq := (quasiDistance_eq_zero_iff P P').mp hz
      rw [congrArg u heq, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le hosc)
        (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)
    have hdpos : 0 < quasiDistance P P' := lt_of_le_of_ne hdelta (Ne.symm hz)
    by_cases hnear : quasiDistance P P' ≤ R0
    · have hR : 0 < 2 * R0 := by positivity
      have hdistR : quasiDistance P P' ≤ 2 * R0 := by linarith only [hnear, hR0]
      obtain ⟨hpcl, hp'cl⟩ := pair_mem_closed_later_cylinder P P' ht hdpos
      have hsmallO : closure (backwardCylinder P' (quasiDistance P P')) ⊆ Omega :=
        (closure_mono (backwardCylinder_radius_mono P' hdpos hdistR)).trans (hQ P' hP')
      have hcsmall := isCompact_closure_backwardCylinder P' _ hdpos
      have hucsmall := hu.1.1.mono hsmallO
      have habsmall := hcsmall.bddAbove_image hucsmall
      have hbbsmall := hcsmall.bddBelow_image hucsmall
      have habdiff := abs_sub_le_oscillationOn habsmall hbbsmall hpcl hp'cl
      rw [oscillationOn_closure (backwardCylinder_nonempty P' hdpos) hcsmall hucsmall]
        at habdiff
      have hd := hdecay A hA Omega hOmega P' (2 * R0) (quasiDistance P P')
        hR hdpos hdistR (hQ P' hP') u hu
      have hbigE : backwardCylinder P' (2 * R0) ⊆ E := fun Z hZ =>
        mem_iUnion.mpr ⟨P', mem_iUnion.mpr ⟨hP', hZ⟩⟩
      have hbigosc := oscillationOn_nonneg (backwardCylinder_nonempty P' hR)
        (hab.mono (image_mono hbigE)) (hbb.mono (image_mono hbigE))
      have hoscmono := oscillationOn_mono (backwardCylinder_nonempty P' hR) hbigE hab hbb
      have hratio : quasiDistance P P' / (2 * R0) ≤ quasiDistance P P' / R0 :=
        div_le_div_of_nonneg_left hdelta hR0 (by linarith only [hR0])
      have hpower := Real.rpow_le_rpow (div_nonneg hdelta hR.le) hratio ha.le
      have hcoeff : D * (quasiDistance P P' / (2 * R0)) ^ alpha ≤
          C * (quasiDistance P P' / R0) ^ alpha :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (div_nonneg hdelta hR.le) _)).trans
          (mul_le_mul_of_nonneg_left hpower hC.le)
      have hb := (habdiff.trans hd).trans
        (mul_le_mul_of_nonneg_right hcoeff hbigosc)
      have hb' := hb.trans (mul_le_mul_of_nonneg_left hoscmono
        (mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)))
      exact hb'.trans_eq (by ring)
    · have hbase := abs_sub_le_oscillationOn habc hbbc (hcenter P hP) (hcenter P' hP')
      rw [hosccl] at hbase
      have hratio : 1 ≤ quasiDistance P P' / R0 :=
        (one_le_div hR0).mpr (le_of_not_ge hnear)
      have hpower : 1 ≤ (quasiDistance P P' / R0) ^ alpha := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hratio ha.le
      have hCpower : C ≤ C * (quasiDistance P P' / R0) ^ alpha := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hC.le
      have hcoeff : 1 ≤ C * (quasiDistance P P' / R0) ^ alpha :=
        (le_max_right D 1).trans hCpower
      have hb := mul_le_mul_of_nonneg_right hcoeff hosc
      rw [one_mul] at hb
      exact hbase.trans (hb.trans_eq (by ring))
  intro P hP P' hP'
  rcases le_total P.time P'.time with ht | ht
  · exact hpair P hP P' hP' ht
  · have hb := hpair P' hP' P hP ht
    simpa only [abs_sub_comm, quasiDistance_symm P' P] using hb

end HypoellipticAleksandrov.KineticAleksandrov
