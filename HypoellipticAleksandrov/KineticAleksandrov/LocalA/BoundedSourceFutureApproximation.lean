module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceSmoothApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceActionConvergence
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary

/-! # Actual homogeneous approximations before the forcing starts -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The literal source domain strictly after a chosen separating time. -/
def boundedSourceFutureSet (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (s T : ℝ) :
    Set (ℝ × EvolutionAmbientState d) :=
  {q | s < q.1 ∧ q ∈ boundedSourcePast Ω γ T}

/-- The future source region is open with the original moving geometry. -/
theorem isOpen_boundedSourceFutureSet (hΩ : IsOpen Ω) (hγ : Continuous γ) (s T : ℝ) :
    IsOpen (boundedSourceFutureSet Ω γ s T) :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_boundedSourcePast hΩ hγ T)

/-- Actual positive bounded future potentials have continuous homogeneous approximants
converging for any supplied finite starting measure. -/
theorem exists_duhamelFuture_approximating_sequence
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (a s T : ℝ) (hsT : s ≤ T)
    (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (hfloor : ∀ᵐ p ∂ν, a ≤ p.time)
    (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
    ∃ f : ℕ → KineticPoint d → ℝ,
      (∀ n, Measurable (f n)) ∧ (∀ n p, 0 ≤ f n p ∧ f n p ≤ M + 2) ∧
      (∀ n, ContinuousOn (duhamelPotential K T (f n))
        (evolutionPastClosedCylinder Ω γ T)) ∧
      (∀ n, IsWeakTransportedSolution B b
        (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
        (duhamelPotential K T (f n) ∘ evolutionHomeomorph d) (fun _ => 0)) ∧
      (∀ᵐ p ∂ν, Tendsto (fun n => duhamelPotential K T (f n) p) atTop
        (𝓝 (duhamelPotential K T F p))) := by
  classical
  let μ := boundedSourceActionMeasure K ν a T
  let G : ℝ × EvolutionAmbientState d → ℝ :=
    fun q => F ⟨q.1, q.2.1, q.2.2⟩
  have hG : Measurable G := hF.comp (KineticPoint.measurable_equivProd_symm d)
  have hU := isOpen_boundedSourceFutureSet (isOpen_of_isAdmissibleEvolutionDomain hΩa)
    hγ s T
  obtain ⟨φ, hφ, hφb, hφlim⟩ := exists_boundedSourceSmoothApproximation μ
    (boundedSourceFutureSet Ω γ s T) hU G hG M hM (fun q => hFb _) (by
      intro q hq
      exact hFz _ hq)
  let f (n : ℕ) := φ n ∘ KineticPoint.equivProd d
  have hfc (n : ℕ) : Continuous (f n) :=
    (hφ n).1.continuous.comp (KineticPoint.homeomorphProd d).continuous
  have hfs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      f n ⟨q.1, q.2.1, q.2.2⟩) := (hφ n).1
  have hfn (n : ℕ) : ∀ p, 0 ≤ f n p := fun p => (hφb n _).1
  have hfb (n : ℕ) : ∀ p, |f n p| ≤ M + 2 := fun p => by
    rw [abs_of_nonneg (hfn n p)]
    exact (hφb n _).2
  have hfsup (n : ℕ) : tsupport (f n) ⊆ evolutionPastOpenCylinder Ω γ T := by
    intro p hp
    change p ∈ tsupport (φ n ∘ KineticPoint.equivProd d) at hp
    rw [boundedSourceTest_support] at hp
    exact ((hφ n).2.2 hp).2
  have hzero (n : ℕ) : ∀ p : KineticPoint d, p.time < s → f n p = 0 := by
    intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    change p ∈ tsupport (φ n ∘ KineticPoint.equivProd d) at hm
    rw [boundedSourceTest_support] at hm
    have hs := ((hφ n).2.2 hm).1
    exact (not_lt_of_gt hp) hs
  refine ⟨f, fun n => (hfc n).measurable, fun n p => hφb n _, ?_, ?_, ?_⟩
  · intro n
    exact continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal (f n) (hfn n)
      (hfc n) ((hφ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd d))
      (hfs n) T (hfsup n)
  · intro n
    exact duhamelPotential_weak_before_source hΩa hΩ hγ B b S K hreal hB hBs hb
      (f n) (hfc n).measurable (M + 2) (by linarith) (hfb n) s T hsT (hzero n)
  · exact ae_tendsto_duhamelPotential_of_action_ae K hΩ hγ ν a T hfloor f
      (fun n => (hfc n).measurable) F hF (M + 2) (by linarith) hfb hφlim

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
