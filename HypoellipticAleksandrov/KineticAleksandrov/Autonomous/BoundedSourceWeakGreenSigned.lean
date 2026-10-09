module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenBounded

/-! # Signed bounded-source Green representation

A constant positive shift reduces the signed representation to the proved nonnegative
representation. Integrability and Duhamel linearity use the shared bounded-source API.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo
open scoped ENNReal

private theorem sourceSlice_integrable (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (g : BoundedBorel Point)
    (q : EvolutionQuery (intervalDomain H) (fun _ => 0)) :
    Integrable (fun w => g ⟨q.1.2.1, w.1, w.2⟩) (K.master q) := by
  obtain ⟨C, -, hg⟩ := g.exists_bound
  apply integrable_bounded_real (K.master q) _ _ C (fun w => hg _)
  exact g.measurable.comp ((KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk measurable_id))

/-- The actual finite-horizon Duhamel potential is linear under bounded-source subtraction. -/
theorem strip_duhamel_sub (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (g f : BoundedBorel Point)
    (p : Point) (T : ℝ) :
    duhamelPotential K T (g - f : BoundedBorel Point) p =
      duhamelPotential K T g p - duhamelPotential K T f p := by
  have hi : duhamelIntegrand K (g - f : BoundedBorel Point) p = fun r =>
      duhamelIntegrand K g p r - duhamelIntegrand K f p r := by
    funext r
    unfold duhamelIntegrand
    split
    · unfold duhamelSourceIntegral
      exact integral_sub (sourceSlice_integrable H K g _) (sourceSlice_integrable H K f _)
    · simp only [sub_self]
  obtain ⟨Cg, hCg, hg⟩ := g.exists_bound
  obtain ⟨Cf, hCf, hf⟩ := f.exists_bound
  unfold duhamelPotential
  rw [hi]
  exact integral_sub
    (integrableOn_duhamelIntegrand_bounded K (intervalDomain_measurable H)
      continuous_const g g.measurable Cg hCg hg p T)
    (integrableOn_duhamelIntegrand_bounded K (intervalDomain_measurable H)
      continuous_const f f.measurable Cf hCf hf p T)

/-- Every bounded signed Borel source has the exact actual Green representation. -/
theorem duhamelPotential_eq_green_bounded (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (s : ℝ) (hs : s < T)
    (p : EvolutionState (intervalDomain H) (fun _ => 0) s)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState 1))
    (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s)) (Measure.dirac p) Γ) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂Γ := by
  obtain ⟨C, hC, hg⟩ := g.exists_bound
  let c : BoundedBorel Point := BoundedBorel.const C
  have hp0 : ∀ q, 0 ≤ (g + c) q := by
    intro q
    change 0 ≤ g q + C
    linarith [neg_abs_le (g q), hg q]
  have hmass := greenMeasure_mass_le K s (T - s) (sub_pos.mpr hs) (Measure.dirac p) Γ hΓ
  have : IsFiniteMeasure Γ := ⟨lt_of_le_of_lt hmass (by simp)⟩
  have hi (f : BoundedBorel Point) :
      Integrable (fun q => f ⟨s + q.1.1, q.2.1, q.2.2⟩) Γ := by
    obtain ⟨B, -, hb⟩ := f.exists_bound
    apply integrable_bounded_real Γ _ _ B (fun q => hb _)
    exact f.measurable.comp ((KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd))
  have h1 := duhamelPotential_eq_green_bounded_nonneg H K T (g + c) hp0 s hs p Γ hΓ
  have h2 := duhamelPotential_eq_green_bounded_nonneg H K T c (fun _ => hC) s hs p Γ hΓ
  have hsub := strip_duhamel_sub H K (g + c) c ⟨s, p.1.1, p.1.2⟩ T
  rw [add_sub_cancel_right] at hsub
  rw [hsub, h1, h2, ← integral_sub (hi (g + c)) (hi c)]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    change (g _ + C) - C = g _
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
