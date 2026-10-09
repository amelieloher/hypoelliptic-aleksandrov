module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentative

/-!
# Canonical reverse-time Hilbert traces

This module selects the continuous spatial-`L²` representative of a
reverse-time Gelfand curve and evaluates that representative at the two closed
time endpoints. These are not evaluations of the raw Bochner representative.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Two continuous spatial-`L²` curves which agree with the same reverse-time
Bochner curve almost everywhere have the same closed-time representative. -/
theorem ReverseTimeHilbertRepresentativeAgrees.unique
    {d : ℕ} {Ω : Set (PDE.Vec d)} {hΩ : IsOpen Ω} {T : ℝ}
    {u : ReverseTimeL2V hΩ T}
    {Ubar Vbar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞))}
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar)
    (hT : 0 < T)
    (hVbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Vbar) :
    Ubar = Vbar := by
  let Uext : ℝ → PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun t =>
    if ht : t ∈ Icc 0 T then Ubar ⟨t, ht⟩ else 0
  let Vext : ℝ → PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun t =>
    if ht : t ∈ Icc 0 T then Vbar ⟨t, ht⟩ else 0
  have hUextCont : ContinuousOn Uext (Icc 0 T) := by
    rw [continuousOn_iff_continuous_restrict]
    have hEq : (Icc 0 T).domRestrict Uext = Ubar := by
      funext t
      simp only [Set.domRestrict_apply, Uext, dif_pos t.2]
    rw [hEq]
    exact Ubar.continuous
  have hVextCont : ContinuousOn Vext (Icc 0 T) := by
    rw [continuousOn_iff_continuous_restrict]
    have hEq : (Icc 0 T).domRestrict Vext = Vbar := by
      funext t
      simp only [Set.domRestrict_apply, Vext, dif_pos t.2]
    rw [hEq]
    exact Vbar.continuous
  have hIoo : ∀ᵐ t ∂volume.restrict (Icc 0 T), t ∈ Ioo 0 T := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hUbarIcc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Ubar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) := by
    simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
      reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hUbar
  have hVbarIcc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      ∀ ht : t ∈ Ioo 0 T,
        Vbar ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u t) := by
    simpa only [ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
      reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hVbar
  have hUVAE : Uext =ᵐ[volume.restrict (Icc 0 T)] Vext := by
    filter_upwards [hIoo, hUbarIcc, hVbarIcc] with t ht hUbar hVbar
    have htIcc : t ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    calc
      Uext t = Ubar ⟨t, htIcc⟩ := by simp only [Uext, dif_pos htIcc]
      _ = valueCLM hΩ (u t) := hUbar ht
      _ = Vbar ⟨t, htIcc⟩ := (hVbar ht).symm
      _ = Vext t := by simp only [Vext, dif_pos htIcc]
  have hEqOn : EqOn Uext Vext (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hUVAE hUextCont hVextCont
  apply ContinuousMap.ext
  intro t
  simpa only [Uext, Vext, dif_pos t.2] using hEqOn t.2

/-- The canonical continuous spatial-`L²` representative supplied by the
reverse-time Hilbert-representative theorem. -/
noncomputable def reverseTimeHilbertRepresentative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  Classical.choose (ExistsUnique.exists
    (existsUnique_reverseTimeHilbertRepresentative hΩ T hT u g hderiv))

/-- The canonical representative agrees with the reverse-time Bochner curve
almost everywhere and satisfies the positive-sign energy increment. -/
theorem reverseTimeHilbertRepresentative_spec
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    ReverseTimeHilbertRepresentativeAgrees hΩ T u
      (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) ∧
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
      s ≤ t →
        ‖reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩‖ ^ 2 -
            ‖reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩‖ ^ 2 =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) :=
  Classical.choose_spec (ExistsUnique.exists
    (existsUnique_reverseTimeHilbertRepresentative hΩ T hT u g hderiv))

/-- The reverse-time initial spatial-`L²` trace, defined at `tau = 0` from
the canonical continuous representative and not from the raw Bochner curve. -/
noncomputable def reverseTimeInitialTrace
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  reverseTimeHilbertRepresentative hΩ T hT u g hderiv
    ⟨(0 : ℝ), ⟨le_rfl, hT.le⟩⟩

/-- The reverse-time terminal spatial-`L²` trace, defined at `tau = T` from
the canonical continuous representative and not from the raw Bochner curve. -/
noncomputable def reverseTimeTerminalTrace
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  reverseTimeHilbertRepresentative hΩ T hT u g hderiv
    ⟨T, ⟨hT.le, le_rfl⟩⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
