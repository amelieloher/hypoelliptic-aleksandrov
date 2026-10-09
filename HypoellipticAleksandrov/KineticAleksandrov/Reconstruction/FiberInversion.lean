module

public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberHeight

/-!
# Fourier inversion on a fibre

Step Lemma 5.2 of the reconstruction lemma.  For `m`-almost every `y`
with `g(y) < ∞` and `H(y) < ∞`, the finite measure `g(y) π_y` on `ℝ^d` has the integrable Fourier
transform `ξ ↦ k̃^ξ(y)`, hence (Fourier inversion, `eq_withDensity_vecInvDensity`) the nonnegative
density `G(y, ·)` bounded by `H(y)`, with integral `g(y)`; consequently
`∫ G(y, z)^q dz ≤ H(y)^{q-1} g(y)`.  The inverse integral is jointly measurable, and
`Γ` has the density `G` with respect to `m ⊗ Leb`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The fibre density `G(y, z) = (2π)^{-d} Re ∫ e^{i ξ·z} k̃^ξ(y) dξ` obtained by Fourier
inversion. -/
def fiberInversionDensity (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (p : Y × PDE.Vec d) :
    ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹ *
    (vecInvIntegral (fun ξ => fiberDensity g κ ξ p.1) p.2).re)

/-- The Fourier transform of `g(y) • κ y` is the fibre representative `k̃^ξ(y)`. -/
lemma vecFourier_smul_kernel (κ : Kernel Y (PDE.Vec d)) (g : Y → ℝ≥0∞) (y : Y)
    (ξ : PDE.Vec d) : vecFourier ((g y) • κ y) ξ = fiberDensity g κ ξ y := by
  unfold vecFourier fiberDensity fiberFourier
  rw [integral_smul_measure, Complex.real_smul]

/-- Fibre inversion at a single `y`: the measure `g(y) π_y` equals the Lebesgue measure with
density `G(y, ·)`, and `G(y, ·) ≤ H(y)`. -/
lemma fiber_inversion_at (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (g : Y → ℝ≥0∞) (y : Y)
    (hy : g y < ∞) (hint : Integrable (fun ξ => fiberDensity g κ ξ y)) :
    (volume : Measure (PDE.Vec d)).withDensity (fun z => fiberInversionDensity g κ (y, z)) =
        (g y) • κ y ∧
      ∀ z, fiberInversionDensity g κ (y, z) ≤ fiberHeight g κ y := by
  have : IsFiniteMeasure ((g y) • κ y) :=
    ⟨by simp [Measure.smul_apply, hy]⟩
  have hfun : vecFourier ((g y) • κ y) = fun ξ => fiberDensity g κ ξ y :=
    funext (vecFourier_smul_kernel κ g y)
  have hφ : Integrable (vecFourier ((g y) • κ y)) := by rw [hfun]; exact hint
  have hG : ∀ z, fiberInversionDensity g κ (y, z) =
      ENNReal.ofReal (vecInvDensity ((g y) • κ y) z) := by
    intro z
    simp only [fiberInversionDensity, vecInvDensity, hfun]
  refine ⟨?_, fun z => ?_⟩
  · calc (volume : Measure (PDE.Vec d)).withDensity (fun z => fiberInversionDensity g κ (y, z))
        = (volume : Measure (PDE.Vec d)).withDensity
            (fun z => ENNReal.ofReal (vecInvDensity ((g y) • κ y) z)) := by
          simp only [hG]
      _ = (g y) • κ y := (eq_withDensity_vecInvDensity ((g y) • κ y) hφ).symm
  · rw [hG]
    have hle := vecInvDensity_le ((g y) • κ y) hφ z
    refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
    rw [fiberHeight, ENNReal.ofReal_mul (by positivity), hfun]
    congr 1
    rw [ofReal_integral_norm_eq_lintegral_enorm hint]


/-- The fibre inversion density is jointly measurable in `(y, z)`. -/
lemma measurable_fiberInversionDensity {g : Y → ℝ≥0∞} (hg : Measurable g)
    (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ] : Measurable (fiberInversionDensity g κ) := by
  unfold fiberInversionDensity
  refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Complex.measurable_re.comp ?_))
  have hc : Continuous fun q : PDE.Vec d × PDE.Vec d =>
      cexp (I * ((PDE.vecDot q.1 q.2 : ℝ) : ℂ)) := by
    unfold PDE.vecDot
    fun_prop
  have hf : Measurable fun q : (Y × PDE.Vec d) × PDE.Vec d =>
      cexp (I * ((PDE.vecDot q.2 q.1.2 : ℝ) : ℂ)) * fiberDensity g κ q.2 q.1.1 :=
    (hc.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
      ((measurable_fiberDensity hg κ).comp (measurable_snd.prodMk
        (measurable_fst.comp measurable_fst)))
  exact (StronglyMeasurable.integral_prod_right (f := fun (p : Y × PDE.Vec d) (ξ : PDE.Vec d) =>
    cexp (I * ((PDE.vecDot ξ p.2 : ℝ) : ℂ)) * fiberDensity g κ ξ p.1)
    hf.stronglyMeasurable).measurable


/-- Pointwise `L^q` bound on a fibre from `G ≤ H` and `∫ G = g`. -/
lemma lintegral_rpow_le_of_le {μ : Measure (PDE.Vec d)} {G : PDE.Vec d → ℝ≥0∞} {H a : ℝ≥0∞}
    {q : ℝ} (hq : 1 < q) (hHT : H ≠ ∞) (hG : ∀ z, G z ≤ H) (hint : ∫⁻ z, G z ∂μ = a) :
    ∫⁻ z, G z ^ q ∂μ ≤ H ^ (q - 1) * a := by
  calc ∫⁻ z, G z ^ q ∂μ ≤ ∫⁻ z, H ^ (q - 1) * G z ∂μ := by
        refine lintegral_mono fun z => ?_
        calc G z ^ q = G z ^ (q - 1) * G z := by
              conv_lhs => rw [show q = (q - 1) + 1 by ring]
              rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith), ENNReal.rpow_one]
          _ ≤ H ^ (q - 1) * G z :=
              mul_le_mul_left (ENNReal.rpow_le_rpow (hG z) (by linarith)) _
    _ = H ^ (q - 1) * a := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hHT), hint]


/-- **Step Lemma 5.2.**  Under the hypotheses of the reconstruction
lemma, the fibre inversion density `G` is jointly measurable, `Γ` has density `G` with respect to
`m ⊗ Leb`, and for `m`-almost every `y` one has `G(y, ·) ≤ H(y)`, `∫ G(y, z) dz = g(y)` and
`∫ G(y, z)^q dz ≤ H(y)^{q-1} g(y)`. -/
theorem fiber_inversion {m : Measure Y} [SigmaFinite m] (Γ : Measure (Y × PDE.Vec d))
    [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g) (hΓ : Γ.fst = m.withDensity g)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    {γ q : ℝ} (hγ : 1 < γ) (hq : 1 < q)
    (hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞) :
    Measurable (fiberInversionDensity g Γ.condKernel) ∧
      Γ = (m.prod volume).withDensity (fiberInversionDensity g Γ.condKernel) ∧
      ∀ᵐ y ∂m, (∀ z, fiberInversionDensity g Γ.condKernel (y, z) ≤ fiberHeight g Γ.condKernel y) ∧
        ∫⁻ z, fiberInversionDensity g Γ.condKernel (y, z) = g y ∧
        ∫⁻ z, fiberInversionDensity g Γ.condKernel (y, z) ^ q ≤
          fiberHeight g Γ.condKernel y ^ (q - 1) * g y := by
  obtain ⟨hdis, -⟩ := fiber_disintegration Γ hg hΓ k hk
  have hfin := (fiber_height_minkowski Γ hg hΓ k hk hγ).2 hH
  have hgtop : ∀ᵐ y ∂m, g y < ∞ := ae_lt_top hg (lintegral_ne_top_of_fst_eq Γ hΓ)
  set κ := Γ.condKernel with hκ
  have hGm := measurable_fiberInversionDensity hg κ
  have hfib : ∀ᵐ y ∂m, (volume : Measure (PDE.Vec d)).withDensity
        (fun z => fiberInversionDensity g κ (y, z)) = (g y) • κ y ∧
      ∀ z, fiberInversionDensity g κ (y, z) ≤ fiberHeight g κ y ∧ fiberHeight g κ y < ∞ := by
    filter_upwards [hgtop, hfin] with y hy hy2
    obtain ⟨h1, h2⟩ := fiber_inversion_at κ g y hy hy2.2
    exact ⟨h1, fun z => ⟨h2 z, hy2.1⟩⟩
  refine ⟨hGm, ?_, ?_⟩
  · ext S hS
    have hS' : ∀ y, MeasurableSet (Prod.mk y ⁻¹' S) := fun y => measurable_prodMk_left hS
    have hL : Γ S = ∫⁻ y, g y * κ y (Prod.mk y ⁻¹' S) ∂m := by
      have h := congrArg (fun μ : Measure (Y × PDE.Vec d) => μ S) hdis
      rw [h, Measure.compProd_apply hS,
        lintegral_withDensity_eq_lintegral_mul _ hg (Kernel.measurable_kernel_prodMk_left hS)]
      rfl
    have hR : ((m.prod volume).withDensity (fiberInversionDensity g κ)) S =
        ∫⁻ y, ∫⁻ z in Prod.mk y ⁻¹' S, fiberInversionDensity g κ (y, z) ∂volume ∂m := by
      rw [withDensity_apply _ hS, ← lintegral_indicator hS,
        lintegral_prod _ ((hGm.indicator hS).aemeasurable)]
      refine lintegral_congr fun y => ?_
      rw [← lintegral_indicator (hS' y)]
      refine lintegral_congr fun z => ?_
      by_cases h : (y, z) ∈ S <;> simp [Set.indicator, h]
    rw [hL, hR]
    refine lintegral_congr_ae ?_
    filter_upwards [hfib] with y ⟨h1, _⟩
    have := congrArg (fun μ : Measure (PDE.Vec d) => μ (Prod.mk y ⁻¹' S)) h1
    simp only [withDensity_apply _ (hS' y), Measure.smul_apply, smul_eq_mul] at this
    exact this.symm
  · filter_upwards [hfib] with y ⟨h1, h2⟩
    have hint : ∫⁻ z, fiberInversionDensity g κ (y, z) = g y := by
      have := congrArg (fun μ => μ univ) h1
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
      exact this
    exact ⟨fun z => (h2 z).1, hint, lintegral_rpow_le_of_le hq (h2 0).2.ne (fun z => (h2 z).1) hint⟩

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction
