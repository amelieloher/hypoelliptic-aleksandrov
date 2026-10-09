module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciplePiecewise

/-!
# Maximum principle on a moving ball or bounded interval

This is the finite-subdivision maximum principle.
The theorem needs only continuous motion, slice regularity, and positive
semidefinite diffusion; the source's stronger hypotheses imply these directly.
The transported coordinate remains unrestricted throughout.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- The source's bounded admissible domains have compact closure. -/
theorem isCompact_closure_of_maximumPrinciple_domain {d : ℕ}
    {Ω : Set (PDE.Vec d)}
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a b, a < b ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a b)) :
    IsCompact (closure Ω) := by
  rcases hΩ with ⟨c, R, hR, rfl⟩ | ⟨hd, a, b, hab, heq⟩
  · exact (Metric.isBounded_ball.subset (PDE.euclideanBall_subset_supBall hR)).isCompact_closure
  · cases hd
    have heq' : Ω = PDE.oneDimensionalAxisBox a b := by simpa using heq
    rw [heq']
    exact (PDE.isBoundedDomain_axisBox (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)).isBounded
      |>.isCompact_closure

/-- Maximum principle on the entire closed moving tube over a finite subdivision.
This includes initial, terminal, lateral, and subdivision slices. The source's
piecewise C¹ curve assumption can be weakened to continuity. -/
theorem movingDomain_maximumPrinciple {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ}
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a b, a < b ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a b))
    (n : ℕ) :
    ∀ (r : Fin (n + 2) → ℝ) (_ : StrictMono r)
    (_ : ContinuousOn γ (Icc (r 0) (r (Fin.last (n + 1)))))
    (_ : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : IsTransportIndependentOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      (B p.time p.position p.velocity).PosSemidef)
    (_ : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ transportedForwardOperator B drift u p)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.time = r (Fin.last (n + 1)) → u p ≤ 0)
    (_ : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0),
    ∀ q ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))), u q ≤ 0 := by
  have hopen := isOpen_of_isAdmissibleEvolutionDomain (Or.inr hΩ)
  exact nonpos_on_piecewise_maximumClosedTube hopen
    (isCompact_closure_of_maximumPrinciple_domain hΩ) n

end HypoellipticAleksandrov.KineticAleksandrov.Decay
