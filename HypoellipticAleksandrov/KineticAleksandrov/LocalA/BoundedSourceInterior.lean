module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourcePositiveContinuity

/-! # Interior continuity of literal signed bounded source potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Evolution
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Every signed bounded Borel source supported in the past domain has a continuous
literal potential there, with only the Hörmander input. -/
theorem continuousOn_duhamelPotential_bounded_signed
    (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (T : ℝ) (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, |F p| ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → F p = 0) :
    ContinuousOn (duhamelPotential K T F) (evolutionPastOpenCylinder Ω γ T) := by
  let f := fun p => max (F p) 0
  let g := fun p => max (-F p) 0
  have hfm : Measurable f := hF.max measurable_const
  have hgm : Measurable g := hF.neg.max measurable_const
  have hfb (p : KineticPoint d) : 0 ≤ f p ∧ f p ≤ M :=
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hFb p)) hM⟩
  have hgb (p : KineticPoint d) : 0 ≤ g p ∧ g p ≤ M :=
    ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hFb p)) hM⟩
  have hfz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → f p = 0 := by
    intro p hp
    simp only [f, hFz p hp, max_self]
  have hgz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → g p = 0 := by
    intro p hp
    simp only [g, hFz p hp, neg_zero, max_self]
  have hfc := continuousOn_duhamelPotential_bounded_nonneg hH hΩa hΩ hγ B b S K hreal
    hB hBs hb lam Lam m hlam hm hell hcoerc T f hfm M hM hfb hfz
  have hgc := continuousOn_duhamelPotential_bounded_nonneg hH hΩa hΩ hγ B b S K hreal
    hB hBs hb lam Lam m hlam hm hell hcoerc T g hgm M hM hgb hgz
  have hsplit : F = (fun p => f p + -g p) := by
    funext p
    change F p = max (F p) 0 + -max (-F p) 0
    by_cases hp : 0 ≤ F p
    · rw [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp), neg_zero, add_zero]
    · rw [max_eq_right (le_of_not_ge hp), max_eq_left (by linarith), neg_neg, zero_add]
  have heq : duhamelPotential K T F =
      (fun p => duhamelPotential K T f p - duhamelPotential K T g p) := by
    funext p
    conv_lhs => rw [hsplit]
    rw [duhamelPotential_add_bounded K hΩ hγ f (fun p => -g p) hfm hgm.neg M M hM hM
      (fun p => by rw [abs_of_nonneg (hfb p).1]; exact (hfb p).2)
      (fun p => by rw [abs_neg, abs_of_nonneg (hgb p).1]; exact (hgb p).2),
      duhamelPotential_neg]
    rfl
  rw [heq]
  exact hfc.sub hgc

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
