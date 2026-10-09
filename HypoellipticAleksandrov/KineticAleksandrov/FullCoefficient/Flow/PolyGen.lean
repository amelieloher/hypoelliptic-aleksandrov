module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.PolyClass

/-!
# Iterated derivatives of the Gaussian exponential

The iterated coordinate derivatives of `K * G_θ` are polynomial multiples `K * P_θ * G_θ`, with
`P` in the class `PG` of the length of the derivative word. This is the polynomial structure behind
the derivative bounds of the Gaussian flow.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem abs_coord_le (y : EvolutionAmbientState d) (i : Fin d) :
    |y.1 i| ≤ ‖y‖ ∧ |y.2 i| ≤ ‖y‖ := by
  constructor
  · calc |y.1 i| = ‖y.1 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖y.1‖ := norm_le_pi_norm y.1 i
      _ ≤ ‖y‖ := norm_fst_le y
  · calc |y.2 i| = ‖y.2 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖y.2‖ := norm_le_pi_norm y.2 i
      _ ≤ ‖y‖ := norm_snd_le y

theorem abs_genT_le {S : ℝ} {θ : Theta} (hθ : θ ∈ Coef S) (δ : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) : |genT θ δ y| ≤ 3 * S * (1 + ‖y‖) := by
  obtain ⟨ha, hb, hc⟩ := hθ
  have hS : 0 ≤ S := (abs_nonneg _).trans ha
  have hn := norm_nonneg y
  rcases δ with i | i
  · obtain ⟨h1, h2⟩ := abs_coord_le y i
    unfold genT gen
    calc |θ.2.1 * y.2 i + 2 * θ.2.2 * y.1 i|
        ≤ |θ.2.1 * y.2 i| + |2 * θ.2.2 * y.1 i| := abs_add_le _ _
      _ = |θ.2.1| * |y.2 i| + 2 * |θ.2.2| * |y.1 i| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ S * ‖y‖ + 2 * S * ‖y‖ := by
          gcongr
      _ ≤ 3 * S * (1 + ‖y‖) := by nlinarith
  · obtain ⟨h1, h2⟩ := abs_coord_le y i
    unfold genT gen
    calc |2 * θ.1 * y.2 i + θ.2.1 * y.1 i|
        ≤ |2 * θ.1 * y.2 i| + |θ.2.1 * y.1 i| := abs_add_le _ _
      _ = 2 * |θ.1| * |y.2 i| + |θ.2.1| * |y.1 i| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ 2 * S * ‖y‖ + S * ‖y‖ := by
          gcongr
      _ ≤ 3 * S * (1 + ‖y‖) := by nlinarith

theorem abs_genCoeffT_le {S : ℝ} {θ : Theta} (hθ : θ ∈ Coef S) (δ δ' : Fin d ⊕ Fin d) :
    |genCoeffT θ δ δ'| ≤ 2 * S := by
  obtain ⟨ha, hb, hc⟩ := hθ
  have hS : 0 ≤ S := (abs_nonneg _).trans ha
  unfold genCoeffT genCoeff
  rcases δ with i | i <;> rcases δ' with j | j <;> simp only <;> split_ifs <;>
    simp [abs_mul] <;> nlinarith [abs_nonneg θ.1, abs_nonneg θ.2.1, abs_nonneg θ.2.2]

theorem differentiable_genT (θ : Theta) (δ : Fin d ⊕ Fin d) :
    Differentiable ℝ (genT θ δ : EvolutionAmbientState d → ℝ) :=
  differentiable_gen θ.1 θ.2.1 θ.2.2 δ

theorem dirPartial_genT (θ : Theta) (δ δ' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    dirPartial δ' (genT θ δ) y = genCoeffT θ δ δ' :=
  dirPartial_gen θ.1 θ.2.1 θ.2.2 δ δ' y

theorem dirPartial_mul' (δ : Fin d ⊕ Fin d) {p q : EvolutionAmbientState d → ℝ}
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) (y : EvolutionAmbientState d) :
    dirPartial δ (fun y => p y * q y) y = dirPartial δ p y * q y + p y * dirPartial δ q y := by
  unfold dirPartial
  rw [fderiv_fun_mul (hp y) (hq y)]
  simp
  ring

/-- Multiplication by a gradient component raises the degree by one. -/
theorem PG.mul_gen (δ : Fin d ⊕ Fin d) : ∀ (k : ℕ) {S : ℝ}
    {p : Theta → EvolutionAmbientState d → ℝ},
    PG k S p → PG (k + 1) S (fun θ y => genT θ δ y * p θ y)
  | 0, S, p, hp => by
      obtain ⟨C, hC⟩ := hp
      refine ⟨⟨3 * S * C, fun θ hθ y => ?_⟩, fun θ hθ => ?_, fun δ' => ?_⟩
      · obtain ⟨c, hc, e⟩ := hC θ hθ
        have hS := Coef.nonneg hθ
        have : |genT θ δ y * p θ y| ≤ 3 * S * (1 + ‖y‖) * C := by
          rw [abs_mul, e]
          exact mul_le_mul (abs_genT_le hθ δ y) hc (abs_nonneg _) (by positivity)
        simpa [mul_assoc, mul_comm, mul_left_comm] using this
      · obtain ⟨c, hc, e⟩ := hC θ hθ
        show Differentiable ℝ (fun y => genT θ δ y * p θ y)
        rw [show (fun y => genT θ δ y * p θ y) = fun y => c * genT θ δ y by
          funext y; rw [e]; ring]
        exact (differentiable_genT θ δ).const_mul c
      · refine ⟨2 * S * C, fun θ hθ => ?_⟩
        obtain ⟨c, hc, e⟩ := hC θ hθ
        refine ⟨c * genCoeffT θ δ δ', ?_, ?_⟩
        · rw [abs_mul]
          calc |c| * |genCoeffT θ δ δ'| ≤ C * (2 * S) :=
                mul_le_mul hc (abs_genCoeffT_le hθ δ δ') (abs_nonneg _)
                  ((abs_nonneg _).trans hc)
            _ = 2 * S * C := by ring
        · funext y
          show dirPartial δ' (fun y => genT θ δ y * p θ y) y = _
          rw [show (fun y => genT θ δ y * p θ y) = fun y => c * genT θ δ y by
            funext y; rw [e]; ring]
          rw [dirPartial_const_mul' δ' c (differentiable_genT θ δ), dirPartial_genT]
  | k + 1, S, p, hp => by
      obtain ⟨⟨C, hb⟩, hd, hpart⟩ := hp
      refine ⟨⟨3 * S * C, fun θ hθ y => ?_⟩, fun θ hθ => ?_, fun δ' => ?_⟩
      · have hS := Coef.nonneg hθ
        have h1 := hb θ hθ y
        have : |genT θ δ y * p θ y| ≤ 3 * S * (1 + ‖y‖) * (C * (1 + ‖y‖) ^ (k + 1)) := by
          rw [abs_mul]
          exact mul_le_mul (abs_genT_le hθ δ y) h1 (abs_nonneg _) (by positivity)
        calc |genT θ δ y * p θ y| ≤ _ := this
          _ = 3 * S * C * (1 + ‖y‖) ^ (k + 1 + 1) := by ring
      · exact (differentiable_genT θ δ).mul (hd θ hθ)
      · have h1 : PG (k + 1) S (fun θ y => genCoeffT θ δ δ' * p θ y) :=
          PG.const_mul (k + 1) (fun θ hθ => abs_genCoeffT_le hθ δ δ') ⟨⟨C, hb⟩, hd, hpart⟩
        have h2 : PG (k + 1) S (fun θ y => genT θ δ y * dirPartial δ' (p θ) y) :=
          PG.mul_gen δ k (hpart δ')
        refine (PG.add (k + 1) h1 h2).congr (k + 1) fun θ hθ => ?_
        funext y
        show _ = dirPartial δ' (fun y => genT θ δ y * p θ y) y
        rw [dirPartial_mul' δ' (differentiable_genT θ δ) (hd θ hθ), dirPartial_genT]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
