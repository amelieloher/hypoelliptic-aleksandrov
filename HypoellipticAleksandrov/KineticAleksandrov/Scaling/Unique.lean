module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Transport
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

/-!
# Any realization of the rescaled problem is the pushforward

Combining the realization transport (`Scaling.Transport`) with the terminal-evolution
uniqueness (`SectionTwo.terminalEvolution_unique`): every realization `(Ŝ', K̂')` of the
rescaled problem has kernels equal to the pushforward of the original kernel.  This is the
statement used by consumers of Lemma 2.5.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov

namespace KineticAffineScaling

variable {d : ℕ} {Φ : KineticAffineScaling d} {Ω Ω' : Set (PDE.Vec d)}
  {γ γ' : ℝ → PDE.Vec d}

/-- **Kernel transport.**  If `(S, K)` realizes the terminal evolution for `(Ω, γ, B, b)`
and `(S', K')` realizes it for the rescaled data `(Ω', γ', Φ.coefficient B, Φ.drift b)`, then
`K'` is the pushforward of `K` and `S'` is integration against it. -/
theorem realizes_unique_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ')
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hΩ' : IsAdmissibleEvolutionDomain Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    {S' : TerminalOperatorFamily Ω' γ'} {K' : MovingFiberKernel Ω' γ'}
    (hreal' : SectionTwo.RealizesTerminalEvolution Ω' γ'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') (Φ.coefficient B) (Φ.drift b) S' K') :
    K' = pushKernel h K ∧
      S' = fiberOperator (pushKernel h K) (measurableSet_of_isAdmissibleEvolutionDomain hΩ') := by
  have hpush := realizes_pushKernel h (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1
    (measurableSet_of_isAdmissibleEvolutionDomain hΩ') hreal
  obtain ⟨hS, hK⟩ := SectionTwo.terminalEvolution_unique Ω' γ' hΩ' (Φ.coefficient B)
    (Φ.drift b) S' _ K' _ hreal' hpush
  exact ⟨hK, hS⟩

/-- The master kernel of any realization of the rescaled problem, in the pushforward form
`K̂'.master q' = (K.master (Φ q')).map (Φ_{τ'})⁻¹`. -/
theorem realizes_master_eq_map (h : Φ.MapsDomain Ω γ Ω' γ')
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hΩ' : IsAdmissibleEvolutionDomain Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    {S' : TerminalOperatorFamily Ω' γ'} {K' : MovingFiberKernel Ω' γ'}
    (hreal' : SectionTwo.RealizesTerminalEvolution Ω' γ'
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ') (Φ.coefficient B) (Φ.drift b) S' K')
    (q : EvolutionQuery Ω' γ') :
    K'.master q = (K.master (queryMap h q)).map (Φ.ambientEquiv q.1.2.1).symm := by
  rw [(realizes_unique_pushKernel h hΩ hγ hΩ' hreal hreal').1]
  exact pushKernel_master_apply h K q

end KineticAffineScaling

/-! ### Case W -/

/-- The whole space with the stationary curve is mapped to itself by every scaling. -/
theorem KineticAffineScaling.mapsDomain_wholeSpace {d : ℕ} (Φ : KineticAffineScaling d) :
    Φ.MapsDomain (Set.univ : Set (PDE.Vec d)) (fun _ => 0) Set.univ (fun _ => 0) := by
  intro τ
  have h : ∀ σ : ℝ, movingDomain (Set.univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d)) σ =
      Set.univ := SectionTwo.movingDomain_wholeSpace d
  rw [h, h, preimage_univ]

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
