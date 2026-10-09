module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelSlice
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriers

/-! # Uniform source insets and the integrated kinetic lateral barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open scoped Topology
variable {d : ℕ} {γ : ℝ → PDE.Vec d}

/-- The support of a source slice lifts into the support of the spacetime source. -/
theorem duhamelSlice_tsupport_lift (g : KineticPoint d → ℝ) (r : ℝ)
    (w : EvolutionAmbientState d) (hw : w ∈ tsupport (fun w => g ⟨r, w.1, w.2⟩)) :
    (KineticPoint.mk r w.1 w.2) ∈ tsupport g := by
  have hc : Continuous (fun w : EvolutionAmbientState d => (KineticPoint.mk r w.1 w.2)) :=
    KineticPoint.continuous_mk continuous_const continuous_fst continuous_snd
  have hsub : tsupport (fun w : EvolutionAmbientState d => g ⟨r, w.1, w.2⟩) ⊆
      (fun w : EvolutionAmbientState d => (KineticPoint.mk r w.1 w.2)) ⁻¹' tsupport g :=
    closure_minimal (fun w hw => subset_closure hw) ((isClosed_tsupport g).preimage hc)
  exact hsub hw

/-- Compact interior support has a uniform positive distance from the moving ball boundary. -/
theorem exists_duhamelSource_inset (c : PDE.Vec d) (R : ℝ) (hR : 0 < R)
    (hγ : Continuous γ) (g : KineticPoint d → ℝ) (hc : HasCompactSupport g) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder (PDE.euclideanBall c R) γ T) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R / 4 ∧ ∀ p ∈ tsupport g,
      2 * δ ≤ R - PDE.vecEuclideanNorm (p.position - (γ p.time + c)) := by
  have hmargin : Continuous (fun p : KineticPoint d =>
      R - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) :=
    continuous_const.sub (PDE.continuous_vecEuclideanNorm.comp
      (continuous_position.sub ((hγ.comp continuous_time).add continuous_const)))
  have hpos : ∀ p ∈ tsupport g,
      0 < R - PDE.vecEuclideanNorm (p.position - (γ p.time + c)) := by
    intro p hp
    have hm := (hU hp).2
    rw [mem_movingDomain_iff, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hm
    have he : p.position - γ p.time - c = p.position - (γ p.time + c) := by abel
    rw [he] at hm
    exact sub_pos.mpr hm
  obtain ⟨e, he, heb⟩ := hc.exists_forall_le' hmargin.continuousOn hpos
  refine ⟨min (e / 4) (R / 8), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro p hp
    have := heb p hp
    have := min_le_left (e / 4) (R / 8)
    linarith

/-- The supplied kinetic source slices satisfy the existing lateral barrier uniformly in time. -/
theorem duhamelIntegrand_le_barrier {c : PDE.Vec d} {R : ℝ} (hR : 0 < R)
    (hγ : IsContinuousPiecewiseC1 γ) (a T : ℝ) (_haT : a < T)
    (L : ℝ) (hL : 0 ≤ L) (hγL : CurveLipschitzOn γ L (Icc a T))
    {lam Lam : ℝ} (hlam : 0 < lam) (B : FullKineticCoefficient d)
    (hell : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    (b : PDE.Vec d → PDE.Vec d) (hb : HasEuclideanLipschitzDrift Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) γ)
    (K : MovingFiberKernel (PDE.euclideanBall c R) γ)
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) γ
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩))
    (hU : tsupport g ⊆ evolutionPastOpenCylinder (PDE.euclideanBall c R) γ T)
    (δ : ℝ) (hδ : 0 < δ) (hδR : δ < R / 4)
    (hinset : ∀ p ∈ tsupport g,
      2 * δ ≤ R - PDE.vecEuclideanNorm (p.position - (γ p.time + c)))
    (C : ℝ) (hC : ∀ p, |g p| ≤ C) (p : KineticPoint d)
    (hp : p ∈ movingClosedSlab (PDE.euclideanBall c R) γ a T)
    (r : ℝ) (hr : r ∈ Ioc p.time T) :
    |duhamelIntegrand K g p r| ≤ C * min 1
      (barrierW (collarKappa L lam)
        (R - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa L lam) δ) := by
  have hΩ := (PDE.isOpen_euclideanBall c R).measurableSet
  let F := duhamelSlice (duhamelSourceBorel g hg hc) r
  have hF := isSmoothCompactTerminalDatum_duhamelSlice g hg hc hs T hU r
  obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal g hg hc hs T hU r
  have hν := (isClassicalViscousTerminalSolution_zero_iff _ γ B b r F V).2 hV
  obtain ⟨M, -, hM⟩ := exists_uniform_terminalDatum_operator_bound hlam hell hb r F hF
  have har : a < r := lt_of_le_of_lt hp.1 hr.1
  have hγr : CurveLipschitzOn γ L (Icc a r) := fun s hs t ht =>
    hγL s ⟨hs.1, hs.2.trans hr.2⟩ t ⟨ht.1, ht.2.trans hr.2⟩
  have hFs : ∀ w ∈ tsupport (F : EvolutionAmbientState d → ℝ),
      2 * δ ≤ R - PDE.vecEuclideanNorm (w.1 - (γ r + c)) := fun w hw =>
    hinset ⟨r, w.1, w.2⟩ (duhamelSlice_tsupport_lift g r w hw)
  have hbar := (two_barriers_on_finite_slab hR hγ a r har L hL hγr hlam hell hb
    (ε := 0) le_rfl (by norm_num) hF δ hδ hδR hFs C M
    (fun w => hC ⟨r, w.1, w.2⟩) (fun q _ => hM 0 le_rfl (by norm_num) q) hν).1
  have hpr : p ∈ movingClosedSlab (PDE.euclideanBall c R) γ a r :=
    ⟨hp.1, hr.1.le, hp.2.2⟩
  have hΩa : IsAdmissibleEvolutionDomain (PDE.euclideanBall c R) := Or.inr (Or.inl ⟨c, R, hR, rfl⟩)
  rw [duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe p
    ⟨hr.1.le, hp.2.2⟩]
  exact hbar p hpr

/-- Integrating the uniform source-slice barrier gives the source's quantitative lateral bound. -/
theorem duhamelPotential_le_barrier {c : PDE.Vec d} {R : ℝ} (hR : 0 < R)
    (hγ : IsContinuousPiecewiseC1 γ) (a T : ℝ) (_haT : a < T)
    (L : ℝ) (hL : 0 ≤ L) (hγL : CurveLipschitzOn γ L (Icc a T))
    {lam Lam : ℝ} (hlam : 0 < lam) (B : FullKineticCoefficient d)
    (hell : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    (b : PDE.Vec d → PDE.Vec d) (hb : HasEuclideanLipschitzDrift Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) γ)
    (K : MovingFiberKernel (PDE.euclideanBall c R) γ)
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) γ
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩))
    (hU : tsupport g ⊆ evolutionPastOpenCylinder (PDE.euclideanBall c R) γ T)
    (δ : ℝ) (hδ : 0 < δ) (hδR : δ < R / 4)
    (hinset : ∀ p ∈ tsupport g,
      2 * δ ≤ R - PDE.vecEuclideanNorm (p.position - (γ p.time + c)))
    (C : ℝ) (hC : ∀ p, |g p| ≤ C)
    (hgn : ∀ p, 0 ≤ g p) (p : KineticPoint d)
    (hp : p ∈ movingClosedSlab (PDE.euclideanBall c R) γ a T) :
    duhamelPotential K T g p ≤ (T - p.time) * C * min 1
      (barrierW (collarKappa L lam)
        (R - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
          barrierW (collarKappa L lam) δ) := by
  let A := C * min 1 (barrierW (collarKappa L lam)
    (R - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
      barrierW (collarKappa L lam) δ)
  have hn : ‖duhamelPotential K T g p‖ ≤ A * (volume.restrict (Ioc p.time T)).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs]
    exact duhamelIntegrand_le_barrier hR hγ a T _haT L hL hγL hlam B hell b hb
      S K hreal g hg hc hs hU δ hδ hδR hinset C hC p hp r hr
  have hnon : 0 ≤ duhamelPotential K T g p :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hgn p r)
  rw [Real.norm_eq_abs, abs_of_nonneg hnon] at hn
  have hv : (volume.restrict (Ioc p.time T)).real univ = T - p.time := by
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2.1)]
  rw [hv] at hn
  convert hn using 1
  dsimp only [A]
  ring

/-- Uniform source inset and finite-slab motion bounds discharge the integrated barrier premises. -/
theorem duhamelPotential_exists_uniform_barrier {c : PDE.Vec d} {R : ℝ} (hR : 0 < R)
    (hγ : IsContinuousPiecewiseC1 γ) (T : ℝ)
    {lam Lam : ℝ} (hlam : 0 < lam) (B : FullKineticCoefficient d)
    (hell : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    (b : PDE.Vec d → PDE.Vec d) (hb : HasEuclideanLipschitzDrift Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) γ)
    (K : MovingFiberKernel (PDE.euclideanBall c R) γ)
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) γ
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩))
    (hU : tsupport g ⊆ evolutionPastOpenCylinder (PDE.euclideanBall c R) γ T)
    (hgn : ∀ p, 0 ≤ g p) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R / 4 ∧ ∀ a : ℝ, a < T →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ movingClosedSlab (PDE.euclideanBall c R) γ a T,
        duhamelPotential K T g p ≤ (T - p.time) * (⨆ q, g q) * min 1
          (barrierW (collarKappa L lam)
            (R - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) δ) := by
  obtain ⟨δ, hδ, hδR, hinset⟩ := exists_duhamelSource_inset c R hR hγ.1 g hc T hU
  obtain ⟨C, hCb⟩ := hg.bddAbove_range_of_hasCompactSupport hc
  have hbdd : BddAbove (range g) := ⟨C, hCb⟩
  have hC : ∀ p, |g p| ≤ ⨆ q, g q := fun p => by
    rw [abs_of_nonneg (hgn p)]
    exact le_ciSup hbdd p
  refine ⟨δ, hδ, hδR, fun a haT => ?_⟩
  obtain ⟨L, hL, hγL⟩ := exists_evolution_curve_lipschitzOn hγ a T haT
  refine ⟨L, hL, fun p hp => ?_⟩
  exact duhamelPotential_le_barrier hR hγ a T haT L hL hγL hlam B hell b hb S K hreal
    g hg hc hs hU δ hδ hδR hinset _ hC hgn p hp

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
