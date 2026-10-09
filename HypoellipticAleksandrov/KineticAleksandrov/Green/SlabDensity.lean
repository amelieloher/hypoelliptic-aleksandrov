module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabTransport

/-!
# Density on one elapsed-time slab, from the outputs of Lemma 5.1 (case W)

Conditional form of the companion paper, Proposition 5.3 (case W).  The premise is exactly the
conjunction `SlabFourierBounds` of the conclusions of Lemma 5.1; the proof applies the
`Reconstruction.reconstruction` (Lemma 5.2) with `Y = (0,∞) × ℝ^d`,
`m = Lebesgue on (T,2T) × ℝ^d`, `γ = (q + γ₀)/2` and `q₁` from `(q-1)/γ + 1/q₁ = 1`, and then
computes the power of `T`.  The Green measure enters only through its finiteness on the slab
((2.6), mass `≤ M T`).

The theorem is named `slab_density_of_fourier_marginals`, not Proposition 5.3: it gives
Proposition 5.3 once Lemma 5.1 discharges the premise `hbounds`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

/-- The intermediate exponent `γ = (q + γ₀)/2` chosen in the proof of Proposition 5.3. -/
def slabGamma (d : ℕ) (q : ℝ) : ℝ := (q + slabGamma0 d) / 2

/-- The dual exponent `q₁` with `(q-1)/γ + 1/q₁ = 1`. -/
def slabQ1 (d : ℕ) (q : ℝ) : ℝ := slabGamma d q / (slabGamma d q - q + 1)

/-- The constant of Proposition 5.3, in terms of the constants `C_γ` of Lemma 5.1. -/
def slabConstant (d : ℕ) (q : ℝ) (C : ℝ → ℝ≥0) : ℝ≥0 :=
  C (slabGamma d q) ^ (q - 1) * C (slabQ1 d q)

section Numerics

variable {d : ℕ} {q : ℝ}

lemma slab_d_pos (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) : 0 < (d : ℝ) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    simp at hqd
    linarith
  · exact_mod_cast h

lemma slabGamma0_eq {d : ℕ} (hd : 0 < (d : ℝ)) : slabGamma0 d = 1 + 1 / (d : ℝ) := by
  unfold slabGamma0
  field_simp

lemma slab_q_lt_gamma (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) :
    q < slabGamma d q ∧ slabGamma d q < slabGamma0 d := by
  have hd := slab_d_pos hq hqd
  unfold slabGamma
  rw [slabGamma0_eq hd]
  constructor <;> linarith [hqd]

lemma slab_gamma_one_lt (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) : 1 < slabGamma d q :=
  hq.trans (slab_q_lt_gamma hq hqd).1

lemma slab_hq₁ (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) :
    (q - 1) / slabGamma d q + 1 / slabQ1 d q = 1 := by
  have hγ := slab_gamma_one_lt hq hqd
  have h0 : slabGamma d q - q + 1 ≠ 0 := by linarith [(slab_q_lt_gamma hq hqd).1]
  unfold slabQ1
  field_simp
  ring

lemma slab_q1_bounds (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) :
    1 ≤ slabQ1 d q ∧ slabQ1 d q ≤ slabGamma0 d := by
  have hd := slab_d_pos hq hqd
  have hγ := slab_gamma_one_lt hq hqd
  have hlt := (slab_q_lt_gamma hq hqd).1
  have hpos : 0 < slabGamma d q - q + 1 := by linarith
  unfold slabQ1
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos, slabGamma0_eq hd]
    have h1 : (d : ℝ) * (q - 1) < 1 := by
      have := mul_lt_mul_of_pos_left (sub_lt_sub_right hqd 1) hd
      rw [show 1 + 1 / (d : ℝ) - 1 = 1 / (d : ℝ) by ring, mul_one_div_cancel hd.ne'] at this
      exact this
    have h2 : (d : ℝ) * (1 + 1 / (d : ℝ)) = d + 1 := by field_simp
    have h3 : slabGamma d q ≤ (1 + 1 / (d : ℝ)) * (slabGamma d q - q + 1) := by
      have : (d : ℝ) * slabGamma d q ≤ (d + 1) * (slabGamma d q - q + 1) := by
        nlinarith
      have h4 : (1 + 1 / (d : ℝ)) * (slabGamma d q - q + 1) =
          ((d : ℝ) + 1) * (slabGamma d q - q + 1) / d := by field_simp
      rw [h4, le_div_iff₀ hd]
      linarith
    exact h3

/-- The power of `T` in Proposition 5.3. -/
lemma slab_exponent (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) :
    (q - 1) * (slabBeta d (slabGamma d q) - 3 * (d : ℝ) / 2) +
        slabBeta d (slabQ1 d q) = 1 - 2 * d * (q - 1) := by
  have hγ0 : slabGamma d q ≠ 0 := by linarith [slab_gamma_one_lt hq hqd]
  have hq1 := slab_hq₁ hq hqd
  have hq10 : slabQ1 d q ≠ 0 := by
    intro h; rw [h] at hq1; simp at hq1
    have : (q - 1) / slabGamma d q < 1 := by
      rw [div_lt_one (by linarith [slab_gamma_one_lt hq hqd])]
      linarith [(slab_q_lt_gamma hq hqd).1]
    linarith
  unfold slabBeta
  have key : ((d : ℝ) + 2) / (2 * slabGamma d q) * (q - 1) +
      ((d : ℝ) + 2) / (2 * slabQ1 d q) = ((d : ℝ) + 2) / 2 := by
    have : ((d : ℝ) + 2) / (2 * slabGamma d q) * (q - 1) +
        ((d : ℝ) + 2) / (2 * slabQ1 d q) =
        ((d : ℝ) + 2) / 2 * ((q - 1) / slabGamma d q + 1 / slabQ1 d q) := by
      field_simp
    rw [this, hq1, mul_one]
  nlinarith [key]

end Numerics

/-- Exact `ℝ≥0∞` arithmetic of the final step of Proposition 5.3. -/
lemma slab_arith (a b : ℝ≥0) (M : ℝ≥0∞) {T e₁ e₂ s q : ℝ} (hT : 0 < T) (hq : 1 < q)
    (hs : (q - 1) * e₁ + e₂ = s) :
    ((a : ℝ≥0∞) * M * ENNReal.ofReal (T ^ e₁)) ^ (q - 1) *
        ((b : ℝ≥0∞) * M * ENNReal.ofReal (T ^ e₂)) =
      ((a ^ (q - 1) * b : ℝ≥0) : ℝ≥0∞) * M ^ q * ENNReal.ofReal (T ^ s) := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have hT1 : 0 ≤ T ^ e₁ := (Real.rpow_pos_of_pos hT _).le
  have hT2 : 0 ≤ T ^ e₂ := (Real.rpow_pos_of_pos hT _).le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.mul_rpow_of_nonneg _ _ hq0,
    ← ENNReal.coe_rpow_of_nonneg _ hq0, ENNReal.ofReal_rpow_of_nonneg hT1 hq0,
    ← Real.rpow_mul hT.le, ENNReal.coe_mul]
  have hMq : M ^ q = M ^ (q - 1) * M := by
    conv_lhs => rw [show q = (q - 1) + 1 by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ hq0 zero_le_one, ENNReal.rpow_one]
  have hTs : ENNReal.ofReal (T ^ (e₁ * (q - 1))) * ENNReal.ofReal (T ^ e₂) =
      ENNReal.ofReal (T ^ s) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hT _).le, ← Real.rpow_add hT]
    congr 2
    linarith
  rw [hMq, ← hTs]
  ring

/-- **Conditional Proposition 5.3 (case W).**  If the Green measure `Γ_μ^∞` has the outputs
`SlabFourierBounds` of Lemma 5.1 on the slab `(T,2T)`, then for `1 < q < 1 + 1/d` it has
a Lebesgue density `G` on `(T,2T) × ℝ^d × ℝ^d` with
`‖G‖_{L^q}^q ≤ C_q M^q T^{1-2d(q-1)}`, where `C_q = slabConstant d q C` depends only on `d`, `q`
and the constants `C_γ` of Lemma 5.1.  The only premise besides the Green measure
`hΓ` ((2.6)) is `hbounds`, which Lemma 5.1 must discharge. -/
theorem slab_density_of_fourier_marginals {d : ℕ} (C : ℝ → ℝ≥0) (c : ℝ)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {q T : ℝ} (hq : 1 < q) (hqd : q < 1 + 1 / (d : ℝ)) (hT : 0 < T)
    (hbounds : SlabFourierBounds d C c (μ univ) T Γ) :
    ∃ G : GreenCarrier d → ℝ≥0∞, Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue d).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue d ≤
        (slabConstant d q C : ℝ≥0∞) * μ univ ^ q *
          ENNReal.ofReal (T ^ (1 - 2 * (d : ℝ) * (q - 1))) := by
  obtain ⟨⟨g, hgm, hgmarg, hgnorm⟩, ⟨k, hk, hkb⟩⟩ := hbounds
  have hq0 : 0 ≤ q - 1 := by linarith
  obtain ⟨hqγ, hγ0⟩ := slab_q_lt_gamma hq hqd
  obtain ⟨hq1a, hq1b⟩ := slab_q1_bounds hq hqd
  have hγ1 : 1 ≤ slabGamma d q := (slab_gamma_one_lt hq hqd).le
  have hMfin : μ univ < ⊤ := measure_lt_top μ _
  have hfin : IsFiniteMeasure (slabMeasure d T Γ) := ⟨by
    rw [slabMeasure_univ]
    exact (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top hMfin ENNReal.ofReal_lt_top)⟩
  have hgn := hgnorm (slabQ1 d q) hq1a hq1b
  have hgL : eLpNorm g (ENNReal.ofReal (slabQ1 d q)) (slabBase d T) < ⊤ :=
    hgn.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hMfin)
      ENNReal.ofReal_lt_top)
  obtain ⟨-, hkγ⟩ := hkb (slabGamma d q) hγ1 hγ0.le
  have hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal (slabGamma d q)) (slabBase d T) < ⊤ :=
    hkγ.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hMfin)
      ENNReal.ofReal_lt_top)
  obtain ⟨G', hG'm, hΓG', hbd, -⟩ := Reconstruction.reconstruction (m := slabBase d T)
    (slabMeasure d T Γ) hgm (slabMeasure_fst T Γ g hgmarg) hq hqγ (slab_hq₁ hq hqd) hgL k
    (fun ξ => ⟨(hk ξ).1, slabMeasure_fourier T Γ ξ (k ξ) (hk ξ).2⟩) hH
  refine ⟨fun p => G' (slabRegroup d p), hG'm.comp (slabRegroup d).measurable,
    eq_withDensity_of_map_eq (slabRegroup d) (measurePreserving_slabRegroup d T) hΓG', ?_⟩
  calc ∫⁻ p in slabSet T, G' (slabRegroup d p) ^ q ∂greenLebesgue d
      = ∫⁻ y, G' y ^ q ∂((slabBase d T).prod volume) :=
        (measurePreserving_slabRegroup d T).lintegral_comp_emb
          (slabRegroup d).measurableEmbedding (fun y => G' y ^ q)
    _ ≤ _ := hbd
    _ ≤ ((C (slabGamma d q) : ℝ≥0∞) * μ univ *
          ENNReal.ofReal (T ^ (slabBeta d (slabGamma d q) - 3 * (d : ℝ) / 2))) ^ (q - 1) *
        ((C (slabQ1 d q) : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ slabBeta d (slabQ1 d q))) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hkγ hq0) hgn
    _ = _ := by
        rw [slab_arith _ _ _ hT hq (slab_exponent hq hqd)]
        rfl

end HypoellipticAleksandrov.KineticAleksandrov.Green
