module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountDecay

/-! # Uniform time-bin decay from the entrance slab estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- A slab of length at most one bin inherits the source square-root decay. -/
theorem timeBinCount_slab_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (C : ℝ) (hC : 0 < C)
    (hDecay : ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point),
      |c.vbar| = 2 * c.r → P.velocity 0 ∈ closure c.entrance →
      ∀ (j : ℕ) (t : ℝ), (j : ℝ) * c.r ^ 2 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) ≤
        C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier) (hT : 0 < T)
    (hvel : P.velocity 0 ∈ closure c.entrance) (j : ℕ) (a b : ℝ)
    (hja : (j : ℝ) * c.r ^ 2 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hlen : b - a ≤ c.r ^ 2) :
    (visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).toReal ≤
      (2 * entranceSlabConstant Lam * C) * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
  let d := C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)
  let f := fun t => S hH hLE hlam hLam A t (activeVelocityDatum c)
    (P.position 0, P.velocity 0)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have ha : 0 ≤ a := (by positivity : 0 ≤ (j : ℝ) * c.r ^ 2).trans hja
  have hp : f b ≤ d := hDecay A c P hbar hvel j b (hja.trans hab)
  have hg : (∫ t in Ioc a b, f t) ≤ c.r ^ 2 * d :=
    timeBinCount_integral_le hab hlen hd
      (entranceSlab_activeAction_integrableOn hH hLE hlam hLam A c
        (P.position 0, P.velocity 0) a b ha)
      (fun t ht => hDecay A c P hbar hvel j t (hja.trans ht.1.le))
  have hn : c.r ^ (-2 : ℤ) * c.r ^ 2 = 1 := by
    norm_num only [zpow_neg, zpow_ofNat]
    exact inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos c.positive))
  have hb : entranceSlabConstant Lam *
      (f b + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, f t) ≤
        (2 * entranceSlabConstant Lam * C) * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
    calc
      _ ≤ entranceSlabConstant Lam * (d + c.r ^ (-2 : ℤ) * (c.r ^ 2 * d)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hp (mul_le_mul_of_nonneg_left hg (by positivity)))
          (entranceSlabConstant_pos hlam hLam).le
      _ = _ := by rw [← mul_assoc, hn]; dsimp only [d]; ring
  have hv : P.velocity 0 ∈ J.carrier := hJ
    (subset_closure (enlarged_closedEntrance_subset_active c hvel))
  have hm := entranceSlab_mass_le hH hLE hlam hLam A c J T a b hT ha hab hbT hJ P hv
  have hm' := hm.trans (ENNReal.ofReal_le_ofReal hb)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm'
  have hCs := entranceSlabConstant_pos hlam hLam
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
