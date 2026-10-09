module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartFullSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount

/-! # The source position-start slab bound for the canonical enlarged visit measure

The only conditional domination input is the already assigned terminal-domination
conclusion. Occupation domination, finiteness and the localized identity are internal.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The exact source `hStart` estimate, relative only to the existing terminal domination input. -/
theorem positionStartSlabBound_holds
    (hTerminal : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → 0 < T → closure c.active ⊆ J.carrier →
      P.velocity 0 ∈ closure c.entrance →
      ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b) :
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal) := by
  intro hH hLE lam Lam hlam hLam
  obtain ⟨C, hC, hbound⟩ := positionStartQuadratic_slab_mass_bound hlam hLam
  refine ⟨4, 9 / 5 + 16 * C / 5, by norm_num, by positivity, ?_⟩
  intro A c J T P hc hJ hT hv a b k ha hab _hlen hb
  let mu := visitsFromZero hH hLE hlam hLam A c J T P
  have : IsFiniteMeasure mu :=
    visitsFromZero_isFiniteMeasure hH hLE hlam hLam A c J T P hc hJ hT hv
  let Y := ((k : ℝ) + 1 / 2) * c.r ^ 3
  let S := {q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b}
  let W := positionStartBox c Y
  let B := positionStartTerminalKernel hH hLE hlam hLam A c J (P.time + b) ∘ₘ mu
  let G := coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let F := (kernelXV E (Real.toNNReal b) (P.position 0, P.velocity 0) (box 4 c.r Y)).toReal
  let I := ∫ t in Ioc a b,
    (kernelXV E (Real.toNNReal t) (P.position 0, P.velocity 0) (box 4 c.r Y)).toReal
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioc fun _ _ => ENNReal.toReal_nonneg
  have hs := enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
    P le_rfl (by linarith only [hT])
  have hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance := hs.mono fun _ hp => hp.2.2
  have hB : B ≤ enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) := by
    change (Measure.sum
      (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P)).bind
        (positionStartTerminalKernel hH hLE hlam hLam A c J (P.time + b)) ≤ _
    rw [Measure.bind_sum _ _ (Kernel.aemeasurable _)]
    apply positionStart_sum_le_of_partial_le
    intro N
    exact hTerminal hH hLE lam Lam hlam hLam A c J T P hc hT hJ hv N (P.time + b)
      (by linarith only [ha, hab]) (by linarith only [hb])
  have hBF : (B W).toReal ≤ F := by
    have hm := (hB W).trans_eq
      (positionStartFullSpaceTerminal_box hH hLE hlam hLam A c P Y b)
    exact ENNReal.toReal_mono
      ((measure_mono (subset_univ _)).trans_lt
        ((kernelXV_mass_le_one E (Real.toNNReal b) (P.position 0, P.velocity 0)).trans_lt
          ENNReal.one_lt_top)).ne hm
  have hW := measurableSet_positionStartBox c Y
  have he := positionStartGreenMixture_slab_eq_finite hH hLE hlam hLam A c J
    (P.time + a) (P.time + b) (P.time + T) hJ mu
      (hs.mono fun _ hp => ⟨enlarged_closedEntrance_subset_active c hp.2.2, hp.2.1⟩)
        (by linarith only [hb])
  have hGE : G (S ∩ W) ≤ ENNReal.ofReal I := by
    have hh := congrArg (fun rho : Measure Point => rho W) he
    rw [Measure.restrict_apply hW, Measure.restrict_apply hW, inter_comm W] at hh
    change G (S ∩ W) = _ at hh
    rw [hh]
    apply (positionStart_all_occupation_le_fullspace hH hLE hlam hLam A c J T P hT
      (hJ (subset_closure (enlarged_closedEntrance_subset_active c hv))) (S ∩ W)).trans_eq
    exact (positionStartFullSpaceOccupation_box_slab
      hH hLE hlam hLam A c P Y a b T ha hb).trans
        (positionStartBox_slab_ofReal_integral E (P.position 0, P.velocity 0) c.r Y a b).symm
  have hGI := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGE
  rw [ENNReal.toReal_ofReal hI] at hGI
  have hn := hbound hH hLE A c J P.time 0 a b k mu hc hJ hab.le hmu
  simp only [zero_add] at hn
  have hfinal := hn.trans (add_le_add
    (mul_le_mul_of_nonneg_left hBF (by positivity))
    (mul_le_mul_of_nonneg_left hGI hC.le))
  exact positionStart_slab_arithmetic c.r C _ F I c.positive hC.le
    ENNReal.toReal_nonneg hI hfinal

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
