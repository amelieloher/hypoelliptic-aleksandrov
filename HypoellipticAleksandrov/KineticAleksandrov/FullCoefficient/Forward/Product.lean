module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Elapsed

/-!
# The forward expression of a product with a phase-space cut-off

For smooth `G` and a smooth cut-off `ψ` of the phase-space variable only, the forward expression
of `G · ψ` differs from `ψ · (forward expression of G)` by an error that is controlled by the
first and second velocity partials of `ψ` and the transport term `v · ∇_z ψ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem fderiv_apply_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (q w : E) :
    fderiv ℝ (fun q => f q * g q) q w = f q * fderiv ℝ g q w + g q * fderiv ℝ f q w := by
  rw [fderiv_fun_mul (hf q) (hg q)]
  simp

theorem jointVelocityPartial_mul {f g : ℝ × EvolutionAmbientState d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    jointVelocityPartial i (fun q => f q * g q) = fun q =>
      f q * jointVelocityPartial i g q + g q * jointVelocityPartial i f q := by
  funext q
  exact fderiv_apply_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)) q _

theorem jointPositionPartial_mul {f g : ℝ × EvolutionAmbientState d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    jointPositionPartial i (fun q => f q * g q) = fun q =>
      f q * jointPositionPartial i g q + g q * jointPositionPartial i f q := by
  funext q
  exact fderiv_apply_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)) q _

theorem jointTimePartial_mul {f g : ℝ × EvolutionAmbientState d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    jointTimePartial (fun q => f q * g q) = fun q =>
      f q * jointTimePartial g q + g q * jointTimePartial f q := by
  funext q
  exact fderiv_apply_mul (hf.differentiable (by simp)) (hg.differentiable (by simp)) q _

/-- Directional derivatives of a function of the phase-space variable only. -/
theorem fderiv_comp_snd_apply {F : EvolutionAmbientState d → ℝ} (hF : Differentiable ℝ F)
    (q : ℝ × EvolutionAmbientState d) (w : ℝ × EvolutionAmbientState d) :
    fderiv ℝ (fun q : ℝ × EvolutionAmbientState d => F q.2) q w = fderiv ℝ F q.2 w.2 := by
  have h : HasFDerivAt (fun q : ℝ × EvolutionAmbientState d => F q.2)
      ((fderiv ℝ F q.2).comp (ContinuousLinearMap.snd ℝ ℝ (EvolutionAmbientState d))) q :=
    (hF q.2).hasFDerivAt.comp q hasFDerivAt_snd
  rw [h.fderiv]
  rfl

theorem jointTimePartial_comp_snd {F : EvolutionAmbientState d → ℝ} (hF : Differentiable ℝ F)
    (q : ℝ × EvolutionAmbientState d) :
    jointTimePartial (fun q : ℝ × EvolutionAmbientState d => F q.2) q = 0 := by
  unfold jointTimePartial
  rw [fderiv_comp_snd_apply hF]
  simp

theorem jointVelocityPartial_comp_snd {F : EvolutionAmbientState d → ℝ} (hF : Differentiable ℝ F)
    (i : Fin d) (q : ℝ × EvolutionAmbientState d) :
    jointVelocityPartial i (fun q : ℝ × EvolutionAmbientState d => F q.2) q =
      velocityPartial i F q.2 := by
  unfold jointVelocityPartial velocityPartial
  rw [fderiv_comp_snd_apply hF]

theorem jointPositionPartial_comp_snd {F : EvolutionAmbientState d → ℝ} (hF : Differentiable ℝ F)
    (i : Fin d) (q : ℝ × EvolutionAmbientState d) :
    jointPositionPartial i (fun q : ℝ × EvolutionAmbientState d => F q.2) q =
      positionPartial i F q.2 := by
  unfold jointPositionPartial positionPartial
  rw [fderiv_comp_snd_apply hF]

theorem jointVelocityPartial_velocityPartial_comp_snd {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i j : Fin d) (q : ℝ × EvolutionAmbientState d) :
    jointVelocityPartial i (jointVelocityPartial j (fun q : ℝ × EvolutionAmbientState d =>
      F q.2)) q = velocityPartial i (velocityPartial j F) q.2 := by
  have hfun : jointVelocityPartial j (fun q : ℝ × EvolutionAmbientState d => F q.2) =
      fun q => velocityPartial j F q.2 := by
    funext q
    exact jointVelocityPartial_comp_snd (hF.differentiable (by simp)) j q
  have hd : Differentiable ℝ (velocityPartial j F) :=
    (contDiff_fderiv_apply hF _).differentiable (by simp)
  rw [hfun]
  exact jointVelocityPartial_comp_snd hd i q

/-- The defect of the product rule for the forward expression of `G · ψ`. -/
theorem forwardReprAt_mul_cutoff_sub (B : FullKineticCoefficient d) (σ₀ : ℝ)
    {G : ℝ × EvolutionAmbientState d → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {ψ : EvolutionAmbientState d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (q : ℝ × EvolutionAmbientState d) :
    forwardReprAt B σ₀ (fun q => G q * ψ q.2) q - ψ q.2 * forwardReprAt B σ₀ G q =
      ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j *
        (G q * velocityPartial i (velocityPartial j ψ) q.2 +
          velocityPartial j ψ q.2 * jointVelocityPartial i G q +
            jointVelocityPartial j G q * velocityPartial i ψ q.2) +
      ∑ i, q.2.1 i * (G q * positionPartial i ψ q.2) := by
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d => ψ q.2) :=
    hψ.comp contDiff_snd
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have ht := congrFun (jointTimePartial_mul hG hψ') q
  have hv : ∀ j, jointVelocityPartial j (fun q => G q * ψ q.2) = fun q =>
      G q * velocityPartial j ψ q.2 + ψ q.2 * jointVelocityPartial j G q := by
    intro j
    rw [jointVelocityPartial_mul hG hψ']
    funext q
    rw [jointVelocityPartial_comp_snd hψd]
  have hvv : ∀ i j, jointVelocityPartial i (jointVelocityPartial j (fun q => G q * ψ q.2)) q =
      G q * velocityPartial i (velocityPartial j ψ) q.2 +
        velocityPartial j ψ q.2 * jointVelocityPartial i G q +
          (ψ q.2 * jointVelocityPartial i (jointVelocityPartial j G) q +
            jointVelocityPartial j G q * velocityPartial i ψ q.2) := by
    intro i j
    rw [hv j]
    have hA : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
        velocityPartial j ψ q.2) :=
      (contDiff_fderiv_apply hψ _).comp contDiff_snd
    have h1 := congrFun (jointVelocityPartial_mul hG hA i) q
    have h2 := congrFun (jointVelocityPartial_mul hψ' (contDiff_jointVelocityPartial hG j) i) q
    have hsum : jointVelocityPartial i (fun q => G q * velocityPartial j ψ q.2 +
        ψ q.2 * jointVelocityPartial j G q) q =
        jointVelocityPartial i (fun q => G q * velocityPartial j ψ q.2) q +
          jointVelocityPartial i (fun q => ψ q.2 * jointVelocityPartial j G q) q := by
      unfold jointVelocityPartial
      rw [fderiv_fun_add]
      · rfl
      · exact ((hG.mul hA).differentiable (by simp)) q
      · exact ((hψ'.mul (contDiff_jointVelocityPartial hG j)).differentiable (by simp)) q
    have hdj : Differentiable ℝ (velocityPartial j ψ) :=
      (contDiff_fderiv_apply hψ _).differentiable (by simp)
    rw [hsum, h1, h2, jointVelocityPartial_comp_snd hdj i q,
      jointVelocityPartial_comp_snd hψd i q]
  have hz : ∀ i, jointPositionPartial i (fun q => G q * ψ q.2) q =
      G q * positionPartial i ψ q.2 + ψ q.2 * jointPositionPartial i G q := by
    intro i
    have := congrFun (jointPositionPartial_mul hG hψ' i) q
    rw [this, jointPositionPartial_comp_snd hψd]
  have ht' : jointTimePartial (fun q => G q * ψ q.2) q = ψ q.2 * jointTimePartial G q := by
    rw [ht, jointTimePartial_comp_snd hψd]
    ring
  have S1 : ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j *
      jointVelocityPartial i (jointVelocityPartial j (fun q => G q * ψ q.2)) q =
      ψ q.2 * ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j *
        jointVelocityPartial i (jointVelocityPartial j G) q +
      ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j *
        (G q * velocityPartial i (velocityPartial j ψ) q.2 +
          velocityPartial j ψ q.2 * jointVelocityPartial i G q +
            jointVelocityPartial j G q * velocityPartial i ψ q.2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hvv]
    ring
  have S2 : ∑ i, q.2.1 i * jointPositionPartial i (fun q => G q * ψ q.2) q =
      ψ q.2 * ∑ i, q.2.1 i * jointPositionPartial i G q +
        ∑ i, q.2.1 i * (G q * positionPartial i ψ q.2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz]
    ring
  unfold forwardReprAt
  rw [ht', S1, S2]
  ring

/-- The product-rule defect of the forward expression of `G · ψ` is `O(ε)`. -/
theorem forwardReprAt_mul_cutoff_error_le (B : FullKineticCoefficient d) (σ₀ Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hB : ∀ σ y z i j, |B σ y z i j| ≤ Λ)
    {G : ℝ × EvolutionAmbientState d → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {ψ : EvolutionAmbientState d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (C ε : ℝ) (hε : 0 ≤ ε)
    (hGb : ∀ q, |G q| ≤ C) (hGv : ∀ i q, |jointVelocityPartial i G q| ≤ C)
    (hψ1 : ∀ i y, |velocityPartial i ψ y| ≤ ε)
    (hψ2 : ∀ i j y, |velocityPartial i (velocityPartial j ψ) y| ≤ ε)
    (hψ3 : ∀ i y, |y.1 i * positionPartial i ψ y| ≤ ε) (q : ℝ × EvolutionAmbientState d) :
    |forwardReprAt B σ₀ (fun q => G q * ψ q.2) q - ψ q.2 * forwardReprAt B σ₀ G q| ≤
      ((d : ℝ) * d * (Λ * (3 * C * ε)) + d * (C * ε)) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hGb q)
  rw [forwardReprAt_mul_cutoff_sub B σ₀ hG hψ]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j *
          (G q * velocityPartial i (velocityPartial j ψ) q.2 +
            velocityPartial j ψ q.2 * jointVelocityPartial i G q +
              jointVelocityPartial j G q * velocityPartial i ψ q.2)|
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, Λ * (3 * C * ε) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          have a1 : |G q * velocityPartial i (velocityPartial j ψ) q.2| ≤ C * ε := by
            rw [abs_mul]; exact mul_le_mul (hGb q) (hψ2 i j _) (abs_nonneg _) hC
          have a2 : |velocityPartial j ψ q.2 * jointVelocityPartial i G q| ≤ ε * C := by
            rw [abs_mul]; exact mul_le_mul (hψ1 j _) (hGv i q) (abs_nonneg _) hε
          have a3 : |jointVelocityPartial j G q * velocityPartial i ψ q.2| ≤ C * ε := by
            rw [abs_mul]; exact mul_le_mul (hGv j q) (hψ1 i _) (abs_nonneg _) hC
          have a4 : |G q * velocityPartial i (velocityPartial j ψ) q.2 +
              velocityPartial j ψ q.2 * jointVelocityPartial i G q +
                jointVelocityPartial j G q * velocityPartial i ψ q.2| ≤ 3 * C * ε :=
            ((abs_add_three _ _ _).trans (add_le_add (add_le_add a1 a2) a3)).trans (by linarith)
          exact mul_le_mul (hB _ _ _ _ _) a4 (abs_nonneg _) hΛ
      _ = (d : ℝ) * d * (Λ * (3 * C * ε)) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |q.2.1 i * (G q * positionPartial i ψ q.2)|
        ≤ ∑ _i : Fin d, C * ε := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : q.2.1 i * (G q * positionPartial i ψ q.2) =
              G q * (q.2.1 i * positionPartial i ψ q.2) := by ring
          rw [this, abs_mul]
          exact mul_le_mul (hGb q) (hψ3 i _) (abs_nonneg _) hC
      _ = (d : ℝ) * (C * ε) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
