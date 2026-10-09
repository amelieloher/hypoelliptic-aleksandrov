module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitMassesStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandScaling
import Mathlib.Tactic

/-! # Source core-start bound for the same enlarged-strip visit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- The closed entrance band lies strictly inside the active band. -/
theorem enlargedEntrance_subset_active (c : Clock) : closure c.entrance ⊆ c.active := by
  rw [Clock.entrance, closure_Ioo (by linarith [c.positive])]
  intro v hv
  change c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4
  constructor <;> linarith [hv.1, hv.2, c.positive]

/-- Cell masses in the source position-visits theorem are the actual starting masses. -/
theorem enlargedVisit_power_sum_eq (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s q : ℝ) (hq : 0 < q)
    (hnu : ∀ᵐ p ∂nu, p.velocity 0 ∈ closure c.entrance) :
    (∑' a : ℕ × ℤ, nu (enlargedStartCell c s 0 a.1 a.2) ^ q) =
      ∑' j : ℕ, ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s 0 j k ^ q) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro j
  apply tsum_congr
  intro k
  rw [enlargedPositionVisitMass_eq_startCellMass nu c s 0 j k hnu]
  unfold enlargedStartCellMass
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The all-time active mixture of enlarged visits has the source improved band norm. -/
theorem core_start_visit_density (hpush : PushforwardStatement) (htail : RestartTailStatement)
    (hvisits : PositionVisitsStatement) (hmasses : PositionVisitMassesStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ)
    (ha : enlargedAdmissibleAlpha lam Lam hlam hLam alpha) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (J : Interval) (R T : ℝ) (P : Point),
      0 < R → 0 < T → T ≤ R ^ 2 → |c.vbar| = 2 * c.r → c.r ≤ 6 * R →
      closure c.active ⊆ J.carrier → P.velocity 0 ∈ closure c.entrance →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c
          (visitsFromZero hH hLE hlam hLam A c J T P) =
            volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤
          (C * R ^ (6 - 4 * q) *
            (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q) := by
  obtain ⟨Cd, hCd, hd⟩ := position_density_sum hpush htail hH hLE hlam hLam q hq
  obtain ⟨Cv, hCv, hv⟩ := (hvisits hH hLE lam Lam hlam hLam alpha ha).2 q hq
  obtain ⟨Cm, _, hm⟩ := hmasses hH hLE lam Lam hlam hLam
  let eta := 1 - (2 - alpha) * (q - 1)
  have hb := bellmanAdjointExponent_range (Lam / lam) ((le_div_iff₀ hlam).2
    (by simpa only [one_mul] using hLam))
  have ha0 : 0 < alpha := by dsimp [enlargedAdmissibleAlpha] at ha; linarith [ha.1, hb.1]
  have heta : 0 ≤ eta := by dsimp [eta]; nlinarith [hq.1, hq.2, ha.2]
  let C := Cd * Cv * 7 ^ eta
  have hC : 0 < C := mul_pos (mul_pos hCd hCv) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  intro A c J R T P hR hT hTR hc hr hJ hvel
  let nu := visitsFromZero hH hLE hlam hLam A c J T P
  have hp := hm A c J R T P hR hT hTR hc hJ hvel
  have : IsFiniteMeasure nu := hp.1
  have hnu : ∀ᵐ p ∂nu, P.time ≤ p.time ∧ p.velocity 0 ∈ c.active :=
    hp.2.1.mono (fun _ h => ⟨h.1, enlargedEntrance_subset_active c h.2.2⟩)
  obtain ⟨G, hG, hG0, hGd, hGp, hGi⟩ := hd A c hc P.time 0 nu hnu
  have hsum := hv A c J R T P hR hT hTR hc hJ hvel
  rw [enlargedVisit_power_sum_eq nu c P.time q (by linarith) (hp.2.1.mono (fun _ h => h.2.2))]
    at hGi
  have hscale := coreStartBand_scaling c.r R (6 - 4 * q) eta c.positive hR heta hr
  rw [coreStartBand_exponent alpha q] at hscale
  let K := C * R ^ (6 - 4 * q) * (c.r / R) ^
    (4 - 3 * q + (1 - alpha) * (q - 1))
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))
      (Real.rpow_nonneg (div_pos c.positive hR).le _)
  have hi : (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal K := by
    apply hGi.trans
    apply (mul_le_mul_right hsum _).trans
    rw [← ENNReal.ofReal_mul (mul_nonneg hCd.le (Real.rpow_nonneg c.positive.le _))]
    apply ENNReal.ofReal_le_ofReal
    have he : Cd * c.r ^ (6 - 4 * q) * (Cv * (1 + R / c.r) ^ eta) =
        (Cd * Cv) * (c.r ^ (6 - 4 * q) * (1 + R / c.r) ^ eta) := by ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hscale (mul_nonneg hCd.le hCv.le)).trans_eq
      (by dsimp [K, C]; ring)
  obtain ⟨_, hnorm⟩ := density_norm_of_power_bound volume G hG q K (by linarith) hK hi
  exact ⟨G, hG, hG0, hGd, hGp, hnorm⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
