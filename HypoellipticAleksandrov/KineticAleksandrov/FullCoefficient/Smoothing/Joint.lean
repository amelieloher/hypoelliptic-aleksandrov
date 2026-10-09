module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coefficient

/-!
# Joint continuity of the smoothed densities in `(h, y)`

If `(h, y) ↦ Φ_h(y)` is jointly continuous on `(0,∞) × ℝ^{2d}` (a field of
`SmoothingKernelFamily`), so is every weighted smoothing `(h, y) ↦ ∫ Φ_h(y - y') f(y') dm(y')`
with `f` bounded measurable and `m` finite; in particular the smoothed density and the smoothed
flux entries of the smoothing estimates. Continuous functions are Borel
measurable on the open set `(0,∞) × ℝ^{2d}`, which gives the joint measurability needed for
Fubini in `(h, y)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam)
  {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

/-- Joint continuity of the weighted smoothing in `(h, y)` on `(0, ∞) × ℝ^{2d}`. -/
theorem continuousOn_smoothWeighted_joint (hf : Measurable f) (hfb : ∀ a, |f a| ≤ Cf) :
    ContinuousOn (fun p : ℝ × EvolutionAmbientState d => smoothWeighted Φ p.1 f m p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (EvolutionAmbientState d))) :=
    isOpen_Ioi.prod isOpen_univ
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨h0, y0⟩ := p
  have hh0 : 0 < h0 := hp.1
  set K : Set ℝ := Metric.closedBall h0 (h0 / 2) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKs : K ⊆ Set.Ioi 0 := fun s hs => by
    rw [hK, Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
    simp only [Set.mem_Ioi]; linarith [hs.1]
  obtain ⟨Cs, hCs0, hCs⟩ := Φ.exists_sup_bound hKc hKs
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hfb 0)
  have hnhds : ∀ᶠ x : ℝ × EvolutionAmbientState d in 𝓝 (h0, y0), x.1 ∈ K := by
    have : K ∈ 𝓝 h0 := Metric.closedBall_mem_nhds h0 (by linarith)
    exact (continuous_fst.continuousAt (x := (h0, y0))).eventually this
  have hpos : ∀ᶠ x : ℝ × EvolutionAmbientState d in 𝓝 (h0, y0), 0 < x.1 :=
    hnhds.mono fun x hx => hKs hx
  unfold smoothWeighted wconv
  refine continuousAt_of_dominated (bound := fun _ => Cf * Cs) ?_ ?_ (integrable_const _) ?_
  · filter_upwards [hpos] with x hx
    exact hf.aestronglyMeasurable.smul
      (((Φ.contDiff hx).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards [hnhds] with x hx
    refine Filter.Eventually.of_forall fun a => ?_
    have hx0 : 0 < x.1 := hKs hx
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Φ.pos hx0 _)]
    exact mul_le_mul (hfb a) (hCs x.1 hx _) (Φ.pos hx0 _).le hCf
  · refine Filter.Eventually.of_forall fun a => ?_
    have hc : ContinuousAt (fun p : ℝ × EvolutionAmbientState d => Φ.kernel p.1 p.2)
        (h0, y0 - a) :=
      Φ.joint.continuousAt (hopen.mem_nhds ⟨hh0, Set.mem_univ _⟩)
    have : ContinuousAt (fun x : ℝ × EvolutionAmbientState d => (x.1, x.2 - a)) (h0, y0) :=
      continuousAt_fst.prodMk (continuousAt_snd.sub continuousAt_const)
    exact (hc.comp (f := fun x : ℝ × EvolutionAmbientState d => (x.1, x.2 - a)) this).const_smul
      (f a)

theorem continuousOn_smoothDensity_joint :
    ContinuousOn (fun p : ℝ × EvolutionAmbientState d => smoothDensity Φ p.1 m p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  simp only [smoothDensity_eq]
  exact continuousOn_smoothWeighted_joint Φ m measurable_const (Cf := 1) (fun _ => by simp)

theorem continuousOn_smoothFluxEntry_joint {Lam : ℝ} {F : EvolutionAmbientState d → PDE.Mat d}
    (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F) (i j : Fin d) :
    ContinuousOn (fun p : ℝ × EvolutionAmbientState d => smoothFluxEntry Φ p.1 F m i j p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  simp only [smoothFluxEntry_eq]
  exact continuousOn_smoothWeighted_joint Φ m (hF.measurable i j)
    (fun a => hF.abs_apply_le hlam a i j)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
