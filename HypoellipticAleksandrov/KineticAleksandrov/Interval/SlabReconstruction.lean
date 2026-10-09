module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabDensity

/-! # Reconstruction on an interval slab retaining exponential killing -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal

/-- Reconstruction arithmetic retains the killing factor raised to `q-1`. -/
theorem killed_slab_arith (a b : ℝ≥0) (M : ℝ≥0∞) {T k q : ℝ}
    (hT : 0 < T) (hq : 1 < q) (hq2 : q < 2) :
    ((a : ℝ≥0∞) * M * ENNReal.ofReal
        (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2) * Real.exp (-k * T))) ^ (q - 1) *
      ((b : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta 1 (slabQ1 1 q))) =
    ((a ^ (q - 1) * b : ℝ≥0) : ℝ≥0∞) * M ^ q *
      ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-(k * (q - 1)) * T)) := by
  have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq2
  have he := slab_exponent (d := 1) hq hqd
  norm_num only [Nat.cast_one, mul_one] at he
  have he' : (q - 1) * (slabBeta 1 (slabGamma 1 q) - 3 / 2) +
      slabBeta 1 (slabQ1 1 q) = 3 - 2 * q := by linarith
  have hq0 : 0 ≤ q - 1 := by linarith
  let X : ℝ≥0∞ := (a : ℝ≥0∞) * M *
    ENNReal.ofReal (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2))
  let Y : ℝ≥0∞ := (b : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta 1 (slabQ1 1 q))
  let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-k * T))
  calc
    _ = (X * E) ^ (q - 1) * Y := by
      dsimp only [X, Y, E]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
      congr 2
      ring
    _ = (X ^ (q - 1) * Y) * E ^ (q - 1) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0]
      ring
    _ = _ := by
      dsimp only [X, Y, E]
      rw [slab_arith a b M hT hq he', ENNReal.ofReal_rpow_of_nonneg
        (Real.exp_pos _).le hq0, ← Real.exp_mul,
        ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
      rw [show -k * T * (q - 1) = -(k * (q - 1)) * T by ring]
      ring

/-- The shared reconstruction proof with the interval killing height estimate. -/
theorem killed_slab_reconstruction {Ω : Set (PDE.Vec 1)} {γ : ℝ → PDE.Vec 1}
    (C : ℝ → ℝ≥0) (k : ℝ) (K : MovingFiberKernel Ω γ) (σ : ℝ)
    (μ : Measure (EvolutionState Ω γ σ)) [IsFiniteMeasure μ]
    (Γ : Measure (GreenCarrier 1)) (hΓ : IsGreenMeasure K σ ⊤ μ Γ)
    {q T : ℝ} (hq : 1 < q) (hq2 : q < 2) (hT : 0 < T)
    (g : SlabBase 1 → ℝ≥0∞) (hgm : Measurable g)
    (hgmarg : (slabMeasure 1 T Γ).fst = (slabBase 1 T).withDensity g)
    (hgnorm : ∀ r : ℝ, 1 ≤ r → r ≤ slabGamma0 1 →
      eLpNorm g (ENNReal.ofReal r) (slabBase 1 T) ≤
      (C r : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ slabBeta 1 r))
    (f : PDE.Vec 1 → SlabBase 1 → ℂ)
    (hf : ∀ ξ, Integrable (f ξ) (slabBase 1 T) ∧
      ∀ E : Set (SlabBase 1), MeasurableSet E → ∫ y in E, f ξ y ∂slabBase 1 T =
        ∫ p in {p : GreenCarrier 1 | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ)
    (hheight : ENNReal.ofReal ((2 * Real.pi)⁻¹) *
      ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal (slabGamma 1 q)) (slabBase 1 T) ≤
      (C (slabGamma 1 q) : ℝ≥0∞) * μ univ * ENNReal.ofReal
        (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2) * Real.exp (-k * T))) :
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
        (slabConstant 1 q C : ℝ≥0∞) * μ univ ^ q *
          ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-(k * (q - 1)) * T)) := by
  have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq2
  have hq0 : 0 ≤ q - 1 := by linarith
  obtain ⟨hqγ, hγ0⟩ := slab_q_lt_gamma (d := 1) hq hqd
  obtain ⟨hq1a, hq1b⟩ := slab_q1_bounds (d := 1) hq hqd
  have hγ1 : 1 ≤ slabGamma 1 q := (slab_gamma_one_lt (d := 1) hq hqd).le
  have hMfin : μ univ < ⊤ := measure_lt_top μ _
  have : IsFiniteMeasure (slabMeasure 1 T Γ) := ⟨by
    rw [slabMeasure_univ]
    exact (green_slab_le K σ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top hMfin ENNReal.ofReal_lt_top)⟩
  have hgn := hgnorm (slabQ1 1 q) hq1a hq1b
  have hgL : eLpNorm g (ENNReal.ofReal (slabQ1 1 q)) (slabBase 1 T) < ⊤ :=
    hgn.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hMfin)
      ENNReal.ofReal_lt_top)
  have hH : ENNReal.ofReal (((2 * Real.pi) ^ 1)⁻¹) *
      ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal (slabGamma 1 q)) (slabBase 1 T) < ⊤ := by
    simpa only [pow_one] using hheight.trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hMfin)
        ENNReal.ofReal_lt_top)
  obtain ⟨G', hG'm, hΓG', hbd, -⟩ := Reconstruction.reconstruction (m := slabBase 1 T)
    (slabMeasure 1 T Γ) hgm.aemeasurable hgmarg hq hqγ (slab_hq₁ (d := 1) hq hqd) hgL f
    (fun ξ => ⟨(hf ξ).1, slabMeasure_fourier T Γ ξ (f ξ) (hf ξ).2⟩) hH
  refine ⟨fun p => G' (slabRegroup 1 p), hG'm.comp (slabRegroup 1).measurable,
    eq_withDensity_of_map_eq (slabRegroup 1) (measurePreserving_slabRegroup 1 T) hΓG', ?_⟩
  calc ∫⁻ p in slabSet T, G' (slabRegroup 1 p) ^ q ∂greenLebesgue 1
      = ∫⁻ y, G' y ^ q ∂((slabBase 1 T).prod volume) :=
        (measurePreserving_slabRegroup 1 T).lintegral_comp_emb
          (slabRegroup 1).measurableEmbedding (fun y => G' y ^ q)
    _ ≤ _ := hbd
    _ ≤ ((C (slabGamma 1 q) : ℝ≥0∞) * μ univ * ENNReal.ofReal
          (T ^ (slabBeta 1 (slabGamma 1 q) - 3 / 2) * Real.exp (-k * T))) ^ (q - 1) *
        ((C (slabQ1 1 q) : ℝ≥0∞) * μ univ *
          ENNReal.ofReal (T ^ slabBeta 1 (slabQ1 1 q))) := by
        apply mul_le_mul' (ENNReal.rpow_le_rpow _ hq0) hgn
        simpa only [pow_one] using hheight
    _ = _ := killed_slab_arith _ _ _ hT hq hq2

end HypoellipticAleksandrov.KineticAleksandrov.Interval
