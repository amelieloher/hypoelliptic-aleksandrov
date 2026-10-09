module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityTransport

/-! # Remove the actual velocity weight and obtain the physical pole density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

/-- The inverse velocity weight is masked to the actual physical active interval. -/
def poleInverseVelocity (c : Clock) (p : Point) : ℝ :=
  by
    classical
    exact if p.velocity 0 ∈ c.active then 1 / |p.velocity 0| else 0

/-- The masked inverse velocity weight is Borel. -/
theorem poleInverseVelocity_measurable (c : Clock) : Measurable (poleInverseVelocity c) := by
  classical
  unfold poleInverseVelocity
  exact Measurable.ite (isOpen_Ioo.preimage ((continuous_apply 0).comp
    continuous_velocity)).measurableSet
    (measurable_const.div (((continuous_apply 0).comp continuous_velocity).abs.measurable))
    measurable_const

/-- The masked inverse weight is everywhere nonnegative. -/
theorem poleInverseVelocity_nonneg (c : Clock) (p : Point) : 0 ≤ poleInverseVelocity c p := by
  unfold poleInverseVelocity
  split
  · exact div_nonneg zero_le_one (abs_nonneg _)
  · exact le_rfl

/-- The active strip bounds the inverse velocity uniformly by twice the inverse centre speed. -/
theorem poleInverseVelocity_le (c : Clock) (p : Point) :
    poleInverseVelocity c p ≤ 2 / |c.vbar| := by
  have hc : 0 < |c.vbar| := abs_pos.mpr c.nonzero
  unfold poleInverseVelocity
  split
  next hp =>
    have hb := (c.active_abs_bounds hp).1
    have hv : 0 < |p.velocity 0| := lt_of_lt_of_le (by linarith) hb
    apply (div_le_div_iff₀ hv hc).mpr
    nlinarith
  next => exact div_nonneg (by norm_num) hc.le

/-- The literal physical pole density obtained by removing the velocity weight. -/
def polePhysicalDensity (c : Clock) (e : Point) (F : Point → ℝ) (p : Point) : ℝ :=
  ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p)) * poleInverseVelocity c p

/-- The physical density formula is Borel. -/
theorem polePhysicalDensity_measurable (c : Clock) (e : Point) (F : Point → ℝ)
    (hF : Measurable F) : Measurable (polePhysicalDensity c e F) :=
  (measurable_const.mul (hF.comp (c.continuous_map e).measurable)).mul
    (poleInverseVelocity_measurable c)

/-- The physical density formula is nonnegative when the normalized density is nonnegative. -/
theorem polePhysicalDensity_nonneg (c : Clock) (e : Point) (F : Point → ℝ)
    (hF : ∀ p, 0 ≤ F p) (p : Point) : 0 ≤ polePhysicalDensity c e F p := by
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
    (hF _)) (poleInverseVelocity_nonneg c p)

/-- The actual physical Green has exactly the density computed from the actual normalized one. -/
theorem clock_physical_green_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active)
    (F : Point → ℝ) (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p)
    (hFd : clockGreen hH hLE hlam hLam A c e he =
      volume.withDensity (fun p => ENNReal.ofReal (F p))) :
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
      volume.withDensity (fun p => ENNReal.ofReal (polePhysicalDensity c e F p)) := by
  let μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
  have hi : (μ.withDensity (fun p => ENNReal.ofReal |p.velocity 0|)).withDensity
      (fun p => ENNReal.ofReal (poleInverseVelocity c p)) = μ := by
    rw [← withDensity_mul μ clock_velocity_weight_measurable
      (poleInverseVelocity_measurable c).ennreal_ofReal]
    have hh : ((fun p => ENNReal.ofReal |p.velocity 0|) *
        fun p => ENNReal.ofReal (poleInverseVelocity c p)) =ᵐ[μ] 1 := by
      filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
        ⟨e, WithTop.coe_lt_top _, he⟩] with p hp
      have hc : 0 < |c.vbar| := abs_pos.mpr c.nonzero
      have hv : 0 < |p.velocity 0| := lt_of_lt_of_le (by linarith) (c.active_abs_bounds hp.2).1
      have hpactive : p.velocity 0 ∈ c.active := hp.2
      change ENNReal.ofReal |p.velocity 0| * ENNReal.ofReal (poleInverseVelocity c p) = 1
      rw [poleInverseVelocity, ite_eq_left hpactive, ← ENNReal.ofReal_mul (abs_nonneg _),
        mul_one_div_cancel hv.ne', ENNReal.ofReal_one]
    exact (withDensity_congr_ae hh).trans withDensity_one
  have hw := clock_weightedGreen_density hH hLE hlam hLam A c e he F hF hFn hFd
  have hm : Measurable (fun p => ENNReal.ofReal
      ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := (measurable_const.mul (hF.comp
        (c.continuous_map e).measurable)).ennreal_ofReal
  have hp := withDensity_mul (volume : Measure Point) hm
    (poleInverseVelocity_measurable c).ennreal_ofReal
  have hg : ((fun p => ENNReal.ofReal
      ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) *
      fun p => ENNReal.ofReal (poleInverseVelocity c p)) =
      fun p => ENNReal.ofReal (polePhysicalDensity c e F p) := by
    funext p
    exact (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg
      (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
      (hFn _))).symm
  exact hi.symm.trans ((congrArg (fun ν : Measure Point => ν.withDensity
    (fun p => ENNReal.ofReal (poleInverseVelocity c p))) hw).trans
      (hp.symm.trans (congrArg (fun g : Point → ℝ≥0∞ => volume.withDensity g) hg)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
