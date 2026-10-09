module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.PolyGen
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Commutator

/-!
# Derivative bounds for the Gaussian flow kernel

The Gaussian flow estimates: every iterated coordinate derivative of
`Φ_h` is bounded by `C (1 + ‖y‖)^k Φ_h` with `C` locally uniform in `h`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The iterated coordinate derivative along a word of directions; the head of the list is the
outermost derivative. -/
def iterPartial : List (Fin d ⊕ Fin d) → (EvolutionAmbientState d → ℝ) →
    EvolutionAmbientState d → ℝ
  | [], F => F
  | δ :: l, F => dirPartial δ (iterPartial l F)

theorem PG.bound {S : ℝ} {k : ℕ} {p : Theta → EvolutionAmbientState d → ℝ} (hp : PG k S p) :
    ∃ C : ℝ, ∀ θ ∈ Coef S, ∀ y, |p θ y| ≤ C * (1 + ‖y‖) ^ k := by
  cases k with
  | zero =>
    obtain ⟨C, hC⟩ := hp
    refine ⟨C, fun θ hθ y => ?_⟩
    obtain ⟨c, hc, e⟩ := hC θ hθ
    simpa [e] using hc
  | succ k => exact hp.1

theorem PG.differentiable {S : ℝ} {k : ℕ} {p : Theta → EvolutionAmbientState d → ℝ}
    (hp : PG k S p) {θ : Theta} (hθ : θ ∈ Coef S) : Differentiable ℝ (p θ) := by
  cases k with
  | zero =>
    obtain ⟨C, hC⟩ := hp
    obtain ⟨c, _, e⟩ := hC θ hθ
    rw [e]; exact differentiable_const _
  | succ k => exact hp.2.1 θ hθ

theorem iterPartial_gaussExp (S : ℝ) : ∀ l : List (Fin d ⊕ Fin d),
    ∃ P : Theta → EvolutionAmbientState d → ℝ, PG l.length S P ∧
      ∀ θ ∈ Coef S, ∀ K : ℝ, iterPartial l (fun y => K * gaussExpT θ y) =
        fun y => K * P θ y * gaussExpT θ y
  | [] => by
      refine ⟨fun _ _ => 1, ⟨1, fun θ _ => ⟨1, by simp, rfl⟩⟩, fun θ _ K => ?_⟩
      funext y
      simp [iterPartial]
  | δ :: l => by
      obtain ⟨P, hP, hE⟩ := iterPartial_gaussExp S l
      refine ⟨fun θ y => dirPartial δ (P θ) y + (-1) * (genT θ δ y * P θ y), ?_, ?_⟩
      · exact PG.add _ (PG.partial_succ δ _ hP)
          (PG.const_mul _ (c := fun _ => (-1 : ℝ)) (M := 1) (fun _ _ => by simp)
            (PG.mul_gen δ _ hP))
      · intro θ hθ K
        have hd := PG.differentiable hP hθ
        funext y
        change dirPartial δ (iterPartial l (fun y => K * gaussExpT θ y)) y = _
        rw [hE θ hθ K]
        have e1 : (fun y => K * P θ y * gaussExpT θ y) =
            fun y => (K * P θ y) * gaussExp θ.1 θ.2.1 θ.2.2 y := rfl
        rw [e1, dirPartial_mul_gaussExp θ.1 θ.2.1 θ.2.2 δ (hd.const_mul K y),
          dirPartial_const_mul' δ K hd]
        unfold gaussExpT genT
        ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
