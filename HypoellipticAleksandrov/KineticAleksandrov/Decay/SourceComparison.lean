module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.Parabolic.KineticClassical

/-!
# Source-facing moving-domain maximum principle

The source's standing coefficient and anisotropic regularity assumptions imply
those of the existing slice-wise maximum principle. No analytic premise is added.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder

/-- The source maximum principle with its literal standing assumptions. -/
theorem moving_domain_maximum_principle_source {d : ℕ} (hd : 1 ≤ d)
    (lam Lam m Lb : ℝ) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (D : Set (PDE.Vec d)) (hcase : SourceCase D b m Lb)
    (hB : IsSectionTwoCoefficient lam Lam B) (hb : IsSmoothDrift b)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hbounds : HasTransportBounds m Lb b)
    (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (u : KineticPoint d → ℝ)
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a c, a < c ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a c))
    (n : ℕ) (r : Fin (n + 2) → ℝ) (hr : StrictMono r)
    (hγ : ContinuousOn γ (Icc (r 0) (r (Fin.last (n + 1)))))
    (hγpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hu : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (hreg : ∀ i : Fin (n + 1), IsKineticC112On (u ∘ swapDiffusedTransported)
      (swapDiffusedTransported '' maximumOpenTube Ω γ (r i.castSucc) (r i.succ)))
    (hcontrol : IsTransportIndependentOn u
      (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))) ∨
      IsUniformlyNegAtInfinityOn u
        (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (hsub : ∀ i : Fin (n + 1), ∀ p ∈ maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ lop B b u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.time = r (Fin.last (n + 1)) → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) :
    ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))), u p ≤ 0 := by
  have _hd := hd
  have _hcase := hcase
  have _hb := hb
  have _hm := hm
  have _hmLb := hmLb
  have _hbounds := hbounds
  have _hγpieces := hγpieces
  apply movingDomain_maximumPrinciple (B := zIndependentCoefficient B) (drift := b)
    hΩ n r hr hγ hu hcontrol
  · intro i p hp
    have hmem : swapDiffusedTransported p ∈
        swapDiffusedTransported '' maximumOpenTube Ω γ (r i.castSucc) (r i.succ) :=
      ⟨p, hp, rfl⟩
    have ht := (hreg i).timeSlice_differentiableAt hmem
    have hv := (hreg i).velocitySlice_contDiffAt hmem
    have hz := (hreg i).positionSlice_contDiffAt hmem
    exact ⟨ht, hv, hz.differentiableAt (by norm_num)⟩
  · intro i p hp
    exact (posDef_of_loewner_lower hB.1 (hB.2.2.2.2.1 p.time p.position)).posSemidef
  · exact hsub
  · exact hterminal
  · exact hlateral

/-- Source subdivision comparison on the entire closed tube. -/
theorem moving_domain_piecewise_comparison_source {d : ℕ} (hd : 1 ≤ d)
    (lam Lam m Lb : ℝ) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (D : Set (PDE.Vec d)) (hcase : SourceCase D b m Lb)
    (hB : IsSectionTwoCoefficient lam Lam B) (hb : IsSmoothDrift b)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hbounds : HasTransportBounds m Lb b)
    (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (u : KineticPoint d → ℝ)
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a c, a < c ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a c))
    (n : ℕ) (r : Fin (n + 2) → ℝ) (hr : StrictMono r)
    (hγ : ContinuousOn γ (Icc (r 0) (r (Fin.last (n + 1)))))
    (hγpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hu : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (hreg : ∀ i : Fin (n + 1), IsKineticC112On (u ∘ swapDiffusedTransported)
      (swapDiffusedTransported '' maximumOpenTube Ω γ (r i.castSucc) (r i.succ)))
    (hcontrol : IsTransportIndependentOn u
      (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))) ∨
      IsUniformlyNegAtInfinityOn u
        (maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1)))))
    (hsub : ∀ i : Fin (n + 1), ∀ p ∈ maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ lop B b u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.time = r (Fin.last (n + 1)) → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) :
    ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (n + 1))), u p ≤ 0 := by
  exact moving_domain_maximum_principle_source hd lam Lam m Lb B b D hcase hB hb hm hmLb
    hbounds Ω γ u hΩ n r hr hγ hγpieces hu hreg hcontrol hsub hterminal hlateral

/-- Source comparison on one smooth time slab. -/
theorem moving_domain_single_piece_comparison_source {d : ℕ} (hd : 1 ≤ d)
    (lam Lam m Lb : ℝ) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (D : Set (PDE.Vec d)) (hcase : SourceCase D b m Lb)
    (hB : IsSectionTwoCoefficient lam Lam B) (hb : IsSmoothDrift b)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hbounds : HasTransportBounds m Lb b)
    (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (u : KineticPoint d → ℝ)
    (hΩ : (∃ c R, 0 < R ∧ Ω = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a c, a < c ∧ hd ▸ Ω = PDE.oneDimensionalAxisBox a c))
    (r : Fin (0 + 2) → ℝ) (hr : StrictMono r)
    (hγ : ContinuousOn γ (Icc (r 0) (r (Fin.last (0 + 1)))))
    (hγpieces : ∀ i : Fin (0 + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hu : ContinuousOn u (maximumClosedTube Ω γ (r 0) (r (Fin.last (0 + 1)))))
    (hreg : ∀ i : Fin (0 + 1), IsKineticC112On (u ∘ swapDiffusedTransported)
      (swapDiffusedTransported '' maximumOpenTube Ω γ (r i.castSucc) (r i.succ)))
    (hcontrol : IsTransportIndependentOn u
      (maximumClosedTube Ω γ (r 0) (r (Fin.last (0 + 1)))) ∨
      IsUniformlyNegAtInfinityOn u
        (maximumClosedTube Ω γ (r 0) (r (Fin.last (0 + 1)))))
    (hsub : ∀ i : Fin (0 + 1), ∀ p ∈ maximumOpenTube Ω γ (r i.castSucc) (r i.succ),
      0 ≤ lop B b u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (0 + 1))),
      p.time = r (Fin.last (0 + 1)) → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (0 + 1))),
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0) :
    ∀ p ∈ maximumClosedTube Ω γ (r 0) (r (Fin.last (0 + 1))), u p ≤ 0 := by
  exact moving_domain_maximum_principle_source hd lam Lam m Lb B b D hcase hB hb hm hmLb
    hbounds Ω γ u hΩ 0 r hr hγ hγpieces hu hreg hcontrol hsub hterminal hlateral

end HypoellipticAleksandrov.KineticAleksandrov.Decay
