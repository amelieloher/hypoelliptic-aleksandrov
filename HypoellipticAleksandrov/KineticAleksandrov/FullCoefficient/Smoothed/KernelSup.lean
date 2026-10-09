module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coordinates

/-!
# Weighted sup bounds of the kernel derivatives

The admissibility of the test function `η_δ(τ - s) Φ_h(y - y')` needs
`sup_w (1 + |w|) |∂Φ_h(w)| < ∞`, which follows from the pointwise derivative
bound `|DΦ_h| ≤ C (1 + |w|) Φ_h` and the weighted sup bound `(1 + |w|)^2 Φ_h ≤ C`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h : ℝ}

theorem exists_weighted_partial_bound (hh : 0 < h) :
    ∃ C : ℝ, ∀ (c : Fin d ⊕ Fin d) (w : EvolutionAmbientState d),
      (1 + ‖w‖) * |coordPartial c (Φ.kernel h) w| ≤ C := by
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C₁, hC₁⟩ := Φ.deriv_bound 1 hK hsub
  obtain ⟨W, hW⟩ := Φ.weight_le 2 hK hsub
  refine ⟨|C₁| * W, fun c w => ?_⟩
  have h1 := hC₁ h rfl w
  have h2 := hW h rfl w
  have hp := Φ.pos hh w
  have h3 : |coordPartial c (Φ.kernel h) w| ≤ C₁ * (1 + ‖w‖) ^ 1 * Φ.kernel h w := by
    refine (abs_coordPartial_le c _ w).trans ?_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := Φ.kernel h) (x := w)]
    exact h1
  have hw : 0 ≤ 1 + ‖w‖ := by positivity
  calc (1 + ‖w‖) * |coordPartial c (Φ.kernel h) w|
      ≤ (1 + ‖w‖) * (C₁ * (1 + ‖w‖) ^ 1 * Φ.kernel h w) := mul_le_mul_of_nonneg_left h3 hw
    _ = C₁ * ((1 + ‖w‖) ^ 2 * Φ.kernel h w) := by ring
    _ ≤ |C₁| * ((1 + ‖w‖) ^ 2 * Φ.kernel h w) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C₁| * W := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

theorem exists_partial_bound (hh : 0 < h) :
    ∃ C : ℝ, ∀ (c : Fin d ⊕ Fin d) (w : EvolutionAmbientState d),
      |coordPartial c (Φ.kernel h) w| ≤ C := by
  obtain ⟨C, hC⟩ := exists_weighted_partial_bound Φ hh
  refine ⟨C, fun c w => le_trans ?_ (hC c w)⟩
  have : 1 ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
  calc _ = 1 * |coordPartial c (Φ.kernel h) w| := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right this (abs_nonneg _)

theorem exists_partial_two_bound (hh : 0 < h) :
    ∃ C : ℝ, ∀ (c c' : Fin d ⊕ Fin d) (w : EvolutionAmbientState d),
      |coordPartial c' (coordPartial c (Φ.kernel h)) w| ≤ C := by
  obtain ⟨C, hC⟩ := (Φ.isBoundedSmooth hh).bounded 2
  exact ⟨C, fun c c' w => (abs_coordPartial_coordPartial_le (Φ.contDiff hh) c' c w).trans (hC w)⟩

theorem exists_abs_kernel_bound (hh : 0 < h) :
    ∃ C : ℝ, ∀ w : EvolutionAmbientState d, |Φ.kernel h w| ≤ C := by
  obtain ⟨C, -, hC⟩ := Φ.exists_sup_bound (K := {h}) isCompact_singleton (by simpa using hh)
  exact ⟨C, fun w => by rw [abs_of_pos (Φ.pos hh w)]; exact hC h rfl w⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
