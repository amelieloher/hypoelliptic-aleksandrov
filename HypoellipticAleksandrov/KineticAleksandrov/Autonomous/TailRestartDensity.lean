module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement

/-! # Quantitative density tails from the genuine terminal restart -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- Equal nonnegative density measures have equal real densities almost everywhere. -/
theorem mixture_density_unique {X : Type*} [MeasurableSpace X] (m : Measure X)
    [SigmaFinite m] (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (he : m.withDensity (fun x => ENNReal.ofReal (f x)) =
      m.withDensity (fun x => ENNReal.ofReal (g x))) : f =ᵐ[m] g := by
  have hh := (withDensity_eq_iff_of_sigmaFinite
    hf.ennreal_ofReal.aemeasurable hg.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hh] with x hx
  have ht := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using ht

/-- A restarted density bounds the restriction of the original density, independently of choices. -/
theorem mixture_density_restrict_bound {X : Type*} [MeasurableSpace X] (m : Measure X)
    [SigmaFinite m] (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (L : Set X)
    (hL : MeasurableSet L) (p : ℝ≥0∞) (hgp : MemLp g p m)
    (he : (m.withDensity (fun x => ENNReal.ofReal (f x))).restrict L =
      m.withDensity (fun x => ENNReal.ofReal (g x))) :
    MemLp f p (m.restrict L) ∧ eLpNorm f p (m.restrict L) ≤ eLpNorm g p m := by
  have hh := congrArg (fun mu : Measure X => mu.restrict L) he
  rw [Measure.restrict_restrict hL, inter_self,
    restrict_withDensity hL, restrict_withDensity hL] at hh
  have ha := mixture_density_unique (m.restrict L) f g hf hg hf0 hg0 hh
  exact ⟨(eLpNorm_congr_ae ha).trans_lt (hgp.restrict L),
    (eLpNorm_congr_ae ha).le.trans (eLpNorm_restrict_le g p m L)⟩

/-- The actual surviving terminal measure is finite. -/
theorem activeRestartMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (he : e.velocity 0 ∈ c.active) (t : ℝ) (ht : 0 ≤ t) :
    IsFiniteMeasure (activeRestartMeasure hH hLE hlam hLam A c e he t ht) := by
  constructor
  rw [activeRestartMeasure_mass hH hLE hlam hLam A c e he t ht]
  exact ENNReal.ofReal_lt_top

/-- One fixed one-pole density has the uniform exponential Lq tail at every delay. -/
theorem active_density_tail
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active),
      ∃ G : Point → ℝ, enlargedIsDensityOn
        (stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he))
        (densityClockStrip c e) G ∧ ∀ t : ℝ, 0 ≤ t →
        MemLp G (ENNReal.ofReal q)
          (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active})).toReal ≤
          C * Real.exp (-c₀ * t / c.r ^ 2) * c.r ^ (6 / q - 4) := by
  obtain ⟨C1, hC1, hm⟩ := enlargedActiveGreen_density hH hLE hlam hLam q hq hq2
  obtain ⟨C2, c₀, hC2, hc₀, hs⟩ :=
    activeRestartMeasure_mass_exp hH hLE hlam hLam
  obtain ⟨_, _, hp⟩ := one_sign_pole_density hH hLE hlam hLam q hq hq2
  refine ⟨C1 * C2, c₀, mul_pos hC1 hC2, hc₀, ?_⟩
  intro A c e he
  obtain ⟨G, hGm, hG0, hGd, _, hGa⟩ := hp A c e he
  change stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) =
    volume.withDensity (fun p => ENNReal.ofReal (G p)) at hGd
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  refine ⟨G, ⟨hGm, hG0, ?_⟩, ?_⟩
  · have hr := Measure.restrict_eq_self_of_ae_mem hGa
    have hS : MeasurableSet (densityClockStrip c e) :=
      (continuous_time.measurable measurableSet_Ioi).inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable)
    change (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c e he)).restrict (densityClockStrip c e) = _ at hr
    exact hr.symm.trans ((congrArg (fun mu : Measure Point =>
      mu.restrict (densityClockStrip c e)) hGd).trans
        (restrict_withDensity hS (fun p => ENNReal.ofReal (G p))))
  · intro t ht
    let nu := activeRestartMeasure hH hLE hlam hLam A c e he t ht
    have : IsFiniteMeasure nu :=
      activeRestartMeasure_isFiniteMeasure hH hLE hlam hLam A c e he t ht
    obtain ⟨g, hgm, hg0, hgd, hgp, hgb⟩ := hm A c nu
    have heq := active_tail_restart_identity hH hLE hlam hLam A c e he t ht
    have hed := (congrArg (fun mu : Measure Point =>
      mu.restrict {p | e.time + t ≤ p.time}) hGd).symm.trans (heq.trans hgd)
    have hL : MeasurableSet {p : Point | e.time + t ≤ p.time} :=
      continuous_time.measurable measurableSet_Ici
    obtain ⟨hGp, hGn⟩ := mixture_density_restrict_bound volume G g hGm hgm hG0 hg0
      _ hL (ENNReal.ofReal q) hgp hed
    let S := {p : Point | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}
    have hsub : S ⊆ {p : Point | e.time + t ≤ p.time} := fun _ h => h.1
    have hpn := hGp.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hnn := (eLpNorm_mono_measure G (Measure.restrict_mono hsub le_rfl)).trans hGn
    refine ⟨hpn, ?_⟩
    have hreal := (ENNReal.toReal_mono hgp.ne_top hnn).trans hgb
    have hmass : (nu univ).toReal ≤ C2 * Real.exp (-c₀ * t / c.r ^ 2) :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hs A c e he t ht)).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC2.le (Real.exp_pos _).le))
    have hb := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg hC1.le (Real.rpow_nonneg c.positive.le (6 / q - 4)))
    exact hreal.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb)

/-- The literal restarted-tail statement follows from the genuine restart and density proofs. -/
theorem restartTailStatement_holds :
    RestartTailStatement := by
  intro hH hLE lam Lam hlam hLam q hq
  exact active_density_tail hH hLE hlam hLam q hq.1 hq.2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
