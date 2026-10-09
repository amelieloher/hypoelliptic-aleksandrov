module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Source
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Classical
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak

/-!
# The forward equation for smooth compactly supported tests

The forward equation of the Green slices. For a smooth function `Φ` of absolute time and phase-space
point, with
compact support in the open slab `(σ₀, T) × ℝ^{2d}`, the Green measure `Γ` of a point mass
satisfies `∫ (∂_σ Φ + B : D_v² Φ + v · ∇_z Φ) dΓ = 0` (case W, identity drift, full coefficient).

The proof: the source `g = -𝓛Φ` is split into non-negative sources
`g₁ - g₂`, Duhamel potentials are formed, `Φ - W` is a classical solution with zero terminal
datum, hence vanishes by the uniqueness clause of the realization, and the Green identity of
the Duhamel potentials is applied at the pole.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped ENNReal

variable {d : ℕ}

/-- **Forward equation**, smooth compactly supported form in absolute
time: the Green measure of a point mass annihilates the forward operator of every smooth
compactly supported test function in the open slab. -/
theorem integral_forwardRepr_green_eq_zero {lam Lam : ℝ} (hd : 1 ≤ d) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ T : ℝ) (hσ : σ₀ < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - σ₀)) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal (T - σ₀)) (Measure.dirac p) Γ)
    {Φ : ℝ × EvolutionAmbientState d → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ) (hΦs : tsupport Φ ⊆ Ioo σ₀ T ×ˢ univ) :
    ∫ q, forwardRepr B (identityDrift d) Φ (σ₀ + q.1.1, q.2) ∂Γ = 0 := by
  obtain ⟨g₁, g₂, h₁, h₂, c₁, c₂, s₁, s₂, n₁, n₂, hdiff⟩ :=
    exists_source_split B hB σ₀ T hΦ hΦc hΦs
  have hH : HormanderHypoellipticityStatement := hormanderHypoellipticityStatement_holds
  -- the sources as functions of a kinetic point
  let e := KineticPoint.homeomorphProd d
  have hc₁' : HasCompactSupport (g₁ ∘ e) := c₁.comp_homeomorph e
  have hc₂' : HasCompactSupport (g₂ ∘ e) := c₂.comp_homeomorph e
  have hU : ∀ g : ℝ × EvolutionAmbientState d → ℝ, tsupport g ⊆ Ioo σ₀ T ×ˢ univ →
      tsupport (g ∘ e) ⊆ evolutionPastOpenCylinder (wholeSpace d) (fun _ => 0) T := by
    intro g hg x hx
    rw [tsupport_comp_eq_preimage] at hx
    exact ⟨(hg hx).1.2, by rw [movingDomain_wholeSpace]; trivial⟩
  obtain ⟨⟨-, C₁, hC₁0, hC₁⟩, -, hsm₁, -, heq₁, hcont₁, hterm₁, -, -⟩ :=
    kinetic_duhamel hH hd (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d) hlam hLam one_pos
      B hB hBs hell (identityDrift d) (identityDrift_smooth d) (identityDrift_bounds d) S K hreal
      T (g₁ ∘ e) (fun x => n₁ _) h₁ hc₁' (hU g₁ s₁)
  obtain ⟨⟨-, C₂, hC₂0, hC₂⟩, -, hsm₂, -, heq₂, hcont₂, hterm₂, -, -⟩ :=
    kinetic_duhamel hH hd (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d) hlam hLam one_pos
      B hB hBs hell (identityDrift d) (identityDrift_smooth d) (identityDrift_bounds d) S K hreal
      T (g₂ ∘ e) (fun x => n₂ _) h₂ hc₂' (hU g₂ s₂)
  -- smooth compactly supported functions are integrable against the finite Green measure
  have : IsFiniteMeasure Γ := ⟨lt_of_le_of_lt (greenMeasure_mass_le K σ₀ (T - σ₀)
    (sub_pos.2 hσ) (Measure.dirac p) Γ hΓ) (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)⟩
  have hint : ∀ g : ℝ × EvolutionAmbientState d → ℝ, Continuous g → HasCompactSupport g →
      Integrable (fun q : ElapsedTime (ENNReal.ofReal (T - σ₀)) × EvolutionAmbientState d =>
        g (σ₀ + q.1.1, q.2)) Γ := by
    intro g hg hc
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun q => hC _)
    exact (hg.comp ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_snd)).aestronglyMeasurable
  -- coordinates
  let Φk : KineticPoint d → ℝ := Φ ∘ e
  have hOint : IsOpen (evolutionPastInteriorRaw (wholeSpace d) (fun _ => 0) T) :=
    isOpen_evolutionPastInteriorRaw
      (isOpen_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) continuous_const T
  have hsmI : ∀ (W : KineticPoint d → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (W ∘ evolutionHomeomorph d)
        (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder (wholeSpace d) (fun _ => 0) T) →
      ContDiffOn ℝ (⊤ : ℕ∞) (rawOf W)
        (evolutionPastInteriorRaw (wholeSpace d) (fun _ => 0) T) := by
    intro W hW
    have := contDiffOn_comp_evolutionHomeomorph_iff.mp hW
    rwa [← evolutionPastInteriorRaw_eq_image] at this
  have hs₁ := hsmI _ hsm₁
  have hs₂ := hsmI _ hsm₂
  have hΦk : ContDiffOn ℝ (⊤ : ℕ∞) (rawOf Φk)
      (evolutionPastInteriorRaw (wholeSpace d) (fun _ => 0) T) := hΦ.contDiffOn
  obtain ⟨CΦ, hCΦ⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg _).trans (hCΦ 0)
  have hΦT : ∀ y : EvolutionAmbientState d, Φ (T, y) = 0 := fun y =>
    image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl _ (hΦs h).1.2)
  have hΦσ : ∀ y : EvolutionAmbientState d, Φ (σ₀, y) = 0 := fun y =>
    image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl _ (hΦs h).1.1)
  let W₁ := duhamelPotential K T (g₁ ∘ e)
  let W₂ := duhamelPotential K T (g₂ ∘ e)
  have hclass : IsClassicalTerminalSolution (wholeSpace d) (fun _ => 0) B (identityDrift d) T
      (0 : BoundedBorel (EvolutionAmbientState d)) (fun x => Φk x - (W₁ x - W₂ x)) := by
    refine ⟨⟨CΦ + C₁ + C₂, by positivity, fun x _ => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · have a := hCΦ (e x)
      have b : |W₁ x| ≤ C₁ := hC₁ x
      have c : |W₂ x| ≤ C₂ := hC₂ x
      rw [Real.norm_eq_abs] at a
      calc |Φk x - (W₁ x - W₂ x)| ≤ |Φk x| + |W₁ x - W₂ x| := abs_sub _ _
        _ ≤ |Φk x| + (|W₁ x| + |W₂ x|) := by gcongr; exact abs_sub _ _
        _ ≤ CΦ + C₁ + C₂ := by
          have : |Φk x| ≤ CΦ := a
          rw [add_assoc]
          exact add_le_add this (add_le_add b c)
    · exact (hΦ.continuous.comp e.continuous).continuousOn.sub (hcont₁.sub hcont₂)
    · exact hΦk.sub (hs₁.sub hs₂)
    · intro x hx
      have hq : (x.time, (x.position, x.velocity)) ∈
          evolutionPastInteriorRaw (wholeSpace d) (fun _ => 0) T := hx
      have k1 := transportedForwardOperator_sub B (identityDrift d) Φk (fun y => W₁ y - W₂ y)
        hOint hΦk (hs₁.sub hs₂) _ hq
      have k2 := transportedForwardOperator_sub B (identityDrift d) W₁ W₂ hOint hs₁ hs₂ _ hq
      have k3 := transportedForwardOperator_eq_forwardRepr B (identityDrift d) Φk isOpen_univ
        hΦ.contDiffOn _ (mem_univ (x.time, (x.position, x.velocity)))
      have e1 := heq₁ x hx
      have e2 := heq₂ x hx
      have d1 := hdiff (x.time, (x.position, x.velocity))
      change transportedForwardOperator B (identityDrift d) (fun y => Φk y - (W₁ y - W₂ y)) x = 0
      rw [show x = ⟨x.time, x.position, x.velocity⟩ from rfl] at e1 e2 ⊢
      rw [k1, k2, e1, e2, k3]
      have ee : e ⟨x.time, x.position, x.velocity⟩ = (x.time, (x.position, x.velocity)) := rfl
      change forwardRepr B (identityDrift d) Φ _ - (-g₁ (e ⟨x.time, x.position, x.velocity⟩) -
        -g₂ (e ⟨x.time, x.position, x.velocity⟩)) = 0
      rw [ee]
      linarith
    · intro x hx
      have h1 : W₁ x = 0 := hterm₁ x hx.1
      have h2 : W₂ x = 0 := hterm₂ x hx.1
      rw [BoundedBorel.zero_apply]
      change Φ (x.time, (x.position, x.velocity)) - (W₁ x - W₂ x) = 0
      rw [h1, h2, hx.1, hΦT]
      simp
    · intro x hx
      have := hx.2
      rw [movingDomain_wholeSpace, frontier_univ] at this
      exact this.elim
  have hp0 : (⟨σ₀, p.1.1, p.1.2⟩ : KineticPoint d) ∈
      evolutionPastClosedCylinder (wholeSpace d) (fun _ => 0) T := by
    refine ⟨hσ.le, ?_⟩
    rw [movingDomain_wholeSpace, closure_univ]
    trivial
  have h0 := classicalSolution_zero_datum_eq_zero hreal T hclass hp0
  change Φ (σ₀, (p.1.1, p.1.2)) - (W₁ ⟨σ₀, p.1.1, p.1.2⟩ - W₂ ⟨σ₀, p.1.1, p.1.2⟩) = 0 at h0
  rw [hΦσ] at h0
  have hG₁ : W₁ ⟨σ₀, p.1.1, p.1.2⟩ = ∫ q, g₁ (σ₀ + q.1.1, q.2) ∂Γ :=
    duhamelPotential_eq_green K MeasurableSet.univ continuous_const T (g₁ ∘ e)
      (fun x => n₁ _) (h₁.continuous.comp e.continuous) hc₁' σ₀ hσ p Γ hΓ
  have hG₂ : W₂ ⟨σ₀, p.1.1, p.1.2⟩ = ∫ q, g₂ (σ₀ + q.1.1, q.2) ∂Γ :=
    duhamelPotential_eq_green K MeasurableSet.univ continuous_const T (g₂ ∘ e)
      (fun x => n₂ _) (h₂.continuous.comp e.continuous) hc₂' σ₀ hσ p Γ hΓ
  have hI₁ := hint g₁ h₁.continuous c₁
  have hI₂ := hint g₂ h₂.continuous c₂
  have hcongr : (fun q : ElapsedTime (ENNReal.ofReal (T - σ₀)) × EvolutionAmbientState d =>
      forwardRepr B (identityDrift d) Φ (σ₀ + q.1.1, q.2)) =
      fun q => -(g₁ (σ₀ + q.1.1, q.2) - g₂ (σ₀ + q.1.1, q.2)) := by
    funext q
    rw [hdiff]
    ring
  rw [hcongr, integral_neg, integral_sub hI₁ hI₂, ← hG₁, ← hG₂]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
