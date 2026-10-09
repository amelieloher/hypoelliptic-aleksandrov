module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationPotential
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ActiveTerminalDominationFullSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity

/-! # Full-space domination of the actual enlarged terminal visits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Parabolic
open SectionTwo TheoremA Evolution

/-- At every observation time in the source window, the genuine finite terminal sum is
bounded by the FULL-SPACE terminal measure. Initial-time entrance atoms are retained. -/
theorem enlarged_active_terminal_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (N : ℕ) (b : ℝ)
    (hb : P.time ≤ b) (hBT : b ≤ T) :
    enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b ≤
      enlargedFullSpaceTerminal hH hLE hlam hLam A P b := by
  let mu := enlargedActiveTerminal hH hLE hlam hLam A c J s T P N b
  let nu := enlargedFullSpaceTerminal hH hLE hlam hLam A P b
  have : IsFiniteMeasure nu := ⟨(enlargedFullSpaceTerminal_mass_le_one
    hH hLE hlam hLam A P b).trans_lt ENNReal.one_lt_top⟩
  apply enlarged_physical_measure_le
  intro f hf0
  let G : EvolutionAmbientState 1 → ℝ :=
    fun z => f.1 ((evolutionProdCLE 1).symm (b, z.1, z.2))
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := f.2.1.comp
    ((evolutionProdCLE 1).symm.contDiff.comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)))
  obtain ⟨C, hC⟩ := f.2.2.exists_bound_of_continuous f.2.1.continuous
  let F : BoundedBorel (EvolutionAmbientState 1) :=
    ⟨G, hG.continuous.measurable, max C 0, le_max_right _ _, fun z => by
      have hx : |G z| ≤ C := by
        simpa only [Real.norm_eq_abs] using (hC ((evolutionProdCLE 1).symm (b, z.1, z.2)))
      exact hx.trans (le_max_left _ _)⟩
  have hF0 : ∀ z, 0 ≤ F z := fun z => hf0 ⟨b, z.2, z.1⟩
  obtain ⟨u, hphi, hc, ⟨M, hM, hbound⟩, hop, hn, ht, hr⟩ :=
    enlarged_exists_fullspace_potential hH hLE hlam hLam A b F hG hF0
  have hp : enlargedStoppedPotential b u =ᵐ[mu] exitProbePhysical f := by
    filter_upwards [enlargedActiveTerminal_ae_time hH hLE hlam hLam A c J s T P N b]
      with p hp
    rw [show enlargedStoppedPotential b u p = u p from ite_eq_left hp.le, ht p hp]
    change f.1 ((evolutionProdCLE 1).symm (b, p.velocity, p.position)) =
      f.1 ((evolutionProdCLE 1).symm (p.time, p.velocity, p.position))
    rw [hp]
  have hh := enlarged_terminal_stopped_potential_le hH hLE hlam hLam A c J s T b P hs hT
    hBT hJ u hphi hc M hM hbound hop hn N
  change (∫ p, enlargedStoppedPotential b u p ∂mu) ≤ enlargedStoppedPotential b u P at hh
  rw [integral_congr_ae hp, show enlargedStoppedPotential b u P = u P from ite_eq_left hb,
    hr P hb] at hh
  have he : (∫ z, F z ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
      (wholeSpaceQuery P.time b hb P.velocity P.position)) =
      ∫ p, exitProbePhysical f p ∂nu := by
    have hi := enlargedFullSpace_native_terminal_integral hH hLE hlam hLam A P b hb
      (exitProbePhysical f) (exitProbePhysical_continuous_compact f).1.measurable
    change (∫ z, F z ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
      (wholeSpaceQuery P.time b hb P.velocity P.position)) = _ at hi
    unfold nu enlargedFullSpaceTerminal
    rw [integral_map (enlargedTerminalPoint_measurable b).aemeasurable
      (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable]
    exact hi
  rw [he] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
