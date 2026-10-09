module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Admissible
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.CutoffFamily
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Product
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# Extension of the forward equation to smooth admissible tests

The admissible test functions, smooth case: the product cut-off `ψ_R(v, z) = ζ(v/R) ζ(z/R²)` turns a
smooth admissible `φ` into a smooth compactly supported test function, to which the forward
equation (`Forward/Elapsed.lean`) applies.  The cut-off error is `O(1/R)` times a bounded
function and vanishes in the limit against the finite Green measure.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology

variable {d : ℕ}

/-- A finite family of functions, each with a uniform bound, has one uniform bound. -/
theorem exists_uniform_bound {ι α : Type*} [Fintype ι] (f : ι → α → ℝ)
    (h : ∀ i, ∃ C : ℝ, ∀ x, |f i x| ≤ C) : ∃ C : ℝ, ∀ i x, |f i x| ≤ C := by
  choose C hC using h
  exact ⟨∑ i, |C i|, fun i x => (hC i x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))⟩

/-- The forward expression of a smooth function is continuous. -/
theorem continuous_forwardReprAt {B : FullKineticCoefficient d}
    (hB : IsSmoothFullKineticCoefficient B) (σ₀ : ℝ) {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) : Continuous (forwardReprAt B σ₀ G) := by
  unfold forwardReprAt
  refine ((contDiff_jointTimePartial hG).continuous.add (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)).add (continuous_finsetSum _ fun i _ => ?_)
  · have hc : Continuous (fun q : ℝ × EvolutionAmbientState d => B (σ₀ + q.1) q.2.1 q.2.2 i j) :=
      (hB i j).continuous.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)
    exact hc.mul (contDiff_jointVelocityPartial (contDiff_jointVelocityPartial hG j) i).continuous
  · exact ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
      (contDiff_jointPositionPartial hG i).continuous

/-- Uniform bound of the forward integrand of an admissible function. -/
theorem exists_bound_forwardIntegrand (B : FullKineticCoefficient d) (σ₀ Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hB : ∀ σ y z i j, |B σ y z i j| ≤ Λ) {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}
    (hφ : IsAdmissibleTest T φ) :
    ∃ C : ℝ, ∀ τ y, |forwardIntegrand B σ₀ φ τ y| ≤ C := by
  obtain ⟨Ct, hCt⟩ := hφ.timeDeriv.2
  obtain ⟨Ch, hCh⟩ := exists_uniform_bound (fun (ij : Fin d × Fin d)
    (q : ℝ × EvolutionAmbientState d) =>
    velocityPartial ij.1 (velocityPartial ij.2 (φ q.1)) q.2) (fun ij => (hφ.velocityHess _ _).2)
  obtain ⟨Cw, hCw⟩ := exists_uniform_bound (fun (i : Fin d) (q : ℝ × EvolutionAmbientState d) =>
    q.2.1 i * positionPartial i (φ q.1) q.2) (fun i => (hφ.weightedTransport i i).2)
  refine ⟨Ct + (d : ℝ) * d * (Λ * Ch) + d * Cw, fun τ y => ?_⟩
  let q : ℝ × EvolutionAmbientState d := (τ, y)
  unfold forwardIntegrand velocityHessianContraction transportDerivative
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hCt q) ?_)) ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, B (σ₀ + τ) y.1 y.2 i j * velocityPartial i (velocityPartial j (φ τ)) y|
        ≤ ∑ _i : Fin d, ∑ _j : Fin d, Λ * Ch := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hB _ _ _ _ _) (hCh (i, j) q) (abs_nonneg _) hΛ
      _ = (d : ℝ) * d * (Λ * Ch) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |y.1 i * positionPartial i (φ τ) y| ≤ ∑ _i : Fin d, Cw :=
          Finset.sum_le_sum fun i _ => hCw i q
      _ = (d : ℝ) * Cw := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Uniform bound of the forward expression of a smooth admissible function. -/
theorem exists_bound_forwardReprAt (B : FullKineticCoefficient d) (σ₀ Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hB : ∀ σ y z i j, |B σ y z i j| ≤ Λ) {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}
    (hφ : IsAdmissibleTest T φ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d => φ q.1 q.2)) :
    ∃ C : ℝ, ∀ q, |forwardReprAt B σ₀ (fun q => φ q.1 q.2) q| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_forwardIntegrand B σ₀ Λ hΛ hB hφ
  refine ⟨C, fun q => ?_⟩
  have key : forwardReprAt B σ₀ (fun q => φ q.1 q.2) q = forwardIntegrand B σ₀ φ q.1 q.2 :=
    (forwardIntegrand_eq_forwardReprAt B σ₀ hsm q.1 q.2).symm
  rw [key]
  exact hC _ _

/-- **Forward equation for smooth admissible tests**:
all integrands are `Γ`-integrable and the forward equation holds. -/
theorem integral_forwardIntegrand_green_eq_zero_of_smooth {lam Lam : ℝ} (hd : 1 ≤ d)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (B : FullKineticCoefficient d)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ T : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {φ : ℝ → EvolutionAmbientState d → ℝ} (hφ : IsAdmissibleTest T φ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d => φ q.1 q.2)) :
    Integrable (fun q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      forwardIntegrand B σ₀ φ q.1.1 q.2) Γ ∧
    ∫ q, forwardIntegrand B σ₀ φ q.1.1 q.2 ∂Γ = 0 := by
  set G : ℝ × EvolutionAmbientState d → ℝ := fun q => φ q.1 q.2 with hGdef
  have hd' : Differentiable ℝ G := hsm.differentiable (by simp)
  have hΛ0 : 0 ≤ Lam := hlam.le.trans hLam
  have hBΛ : ∀ σ y z i j, |B σ y z i j| ≤ Lam := fun σ y z i j =>
    HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hell σ y z).1 (hell σ y z).2 i j
  have : IsFiniteMeasure Γ := ⟨lt_of_le_of_lt (greenMeasure_mass_le K σ₀ T hT
    (Measure.dirac p) Γ hΓ) (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)⟩
  obtain ⟨CL, hCL⟩ := exists_bound_forwardReprAt B σ₀ Lam hΛ0 hBΛ hφ hsm
  obtain ⟨C0, hC0⟩ := hφ.value.2
  obtain ⟨Cv, hCv⟩ := exists_uniform_bound (fun (i : Fin d) (q : ℝ × EvolutionAmbientState d) =>
    velocityPartial i (φ q.1) q.2) (fun i => (hφ.velocityGrad i).2)
  have hGv : ∀ i q, |jointVelocityPartial i G q| ≤ Cv := fun i q => by
    rw [← velocityPartial_slice G q.1 q.2 (hd' _) i]
    exact hCv i q
  -- the integrand on the Green space
  let Lf : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ :=
    fun q => forwardReprAt B σ₀ G (q.1.1, q.2)
  have hLc : Continuous Lf := (continuous_forwardReprAt hB σ₀ hsm).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hLint : Integrable Lf Γ :=
    Integrable.of_bound hLc.aestronglyMeasurable CL
      (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hCL _)
  have hLeq : (fun q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      forwardIntegrand B σ₀ φ q.1.1 q.2) = Lf := by
    funext q
    exact forwardIntegrand_eq_forwardReprAt B σ₀ hsm _ _
  rw [hLeq]
  refine ⟨hLint, ?_⟩
  obtain ⟨M, ψ, hM0, hψ⟩ := exists_cutoff_family (d := d)
  obtain ⟨a, b, ha, hab, hbT, hz⟩ := hφ.support
  have hR1 : ∀ n : ℕ, 1 ≤ (n : ℝ) + 1 := fun n => by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  -- the cut-off test functions
  let Gn : ℕ → ℝ × EvolutionAmbientState d → ℝ := fun n q => G q * ψ ((n : ℝ) + 1) q.2
  have hGn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Gn n) := fun n =>
    hsm.mul ((hψ _ (hR1 n)).1.comp contDiff_snd)
  have hGn_zero : ∀ n q, q.1 ∉ Icc a b → Gn n q = 0 := fun n q h => by
    show G q * _ = 0
    rw [hGdef]
    simp only [hz q.1 h]
    simp
  have hGn_supp : ∀ n, HasCompactSupport (Gn n) := fun n => by
    refine HasCompactSupport.intro (K := Icc a b ×ˢ tsupport (ψ ((n : ℝ) + 1)))
      (isCompact_Icc.prod (hψ _ (hR1 n)).2.1) fun q hq => ?_
    by_cases h : q.1 ∈ Icc a b
    · have h2 : q.2 ∉ tsupport (ψ ((n : ℝ) + 1)) := fun h2 => hq ⟨h, h2⟩
      show G q * ψ _ q.2 = 0
      rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · exact hGn_zero n q h
  have hGn_ts : ∀ n, tsupport (Gn n) ⊆ Ioo 0 T ×ˢ univ := fun n => by
    have hsub : Function.support (Gn n) ⊆ Icc a b ×ˢ (univ : Set (EvolutionAmbientState d)) :=
      fun q hq => Set.mem_prod.2 ⟨by_contra fun h => hq (hGn_zero n q h), mem_univ _⟩
    exact (closure_minimal hsub (isClosed_Icc.prod isClosed_univ)).trans
      (prod_mono (Icc_subset_Ioo ha hbT) subset_rfl)
  have hGn_zeroint : ∀ n, ∫ q, forwardReprAt B σ₀ (Gn n) (q.1.1, q.2) ∂Γ = 0 := fun n =>
    integral_forwardReprAt_green_eq_zero hd hlam hLam B hB hBs hell S K hreal σ₀ T hT p Γ hΓ
      (hGn_smooth n) (hGn_supp n) (hGn_ts n)
  -- the cut-off error
  let C1 : ℝ := max C0 Cv
  let Kc : ℝ := (d : ℝ) * d * (Lam * (3 * C1)) + d * C1
  let Fn : ℕ → ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ :=
    fun n q => ψ ((n : ℝ) + 1) q.2 * Lf q
  let fr : ℕ → ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ :=
    fun n q => forwardReprAt B σ₀ (Gn n) (q.1.1, q.2)
  have hmeas : ∀ n, Continuous (Fn n) := fun n =>
    (((hψ _ (hR1 n)).1.continuous).comp continuous_snd).mul hLc
  have herr : ∀ n q, |fr n q - Fn n q| ≤ Kc * (M / ((n : ℝ) + 1)) := by
    intro n q
    have hψn := hψ _ (hR1 n)
    have hε : 0 ≤ M / ((n : ℝ) + 1) := div_nonneg hM0 (by linarith [hR1 n])
    have := forwardReprAt_mul_cutoff_error_le B σ₀ Lam hΛ0 hBΛ hsm hψn.1 C1 _ hε
      (fun q => (hC0 q).trans (le_max_left _ _))
      (fun i q => (hGv i q).trans (le_max_right _ _)) hψn.2.2.2.2.1 hψn.2.2.2.2.2.1
      hψn.2.2.2.2.2.2 (q.1.1, q.2)
    calc |fr n q - Fn n q| ≤ _ := this
      _ = Kc * (M / ((n : ℝ) + 1)) := by simp only [Kc]; ring
  have hFnb : ∀ n q, |Fn n q| ≤ CL := by
    intro n q
    have h := (hψ _ (hR1 n)).2.2.1 q.2
    simp only [Fn, abs_mul]
    rw [abs_of_nonneg h.1]
    calc ψ ((n : ℝ) + 1) q.2 * |Lf q| ≤ 1 * CL :=
          mul_le_mul h.2 (hCL _) (abs_nonneg _) zero_le_one
      _ = CL := one_mul _
  have hFnint : ∀ n, Integrable (Fn n) Γ := fun n =>
    Integrable.of_bound (hmeas n).aestronglyMeasurable CL
      (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hFnb n q)
  have hfrint : ∀ n, Integrable (fr n) Γ := fun n => by
    refine Integrable.of_bound ?_ (Kc * (M / ((n : ℝ) + 1)) + CL)
      (Filter.Eventually.of_forall fun q => ?_)
    · exact ((continuous_forwardReprAt hB σ₀ (hGn_smooth n)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h3 : fr n q = (fr n q - Fn n q) + Fn n q := by ring
      rw [h3]
      exact (abs_add_le _ _).trans (add_le_add (herr n q) (hFnb n q))
  have hbound : ∀ n, ‖∫ q, Fn n q ∂Γ‖ ≤ Kc * (M / ((n : ℝ) + 1)) * Γ.real univ := by
    intro n
    have h0 : ∫ q, fr n q ∂Γ = 0 := hGn_zeroint n
    have h1 : ∫ q, Fn n q ∂Γ = ∫ q, (Fn n q - fr n q) ∂Γ := by
      rw [integral_sub (hFnint n) (hfrint n), h0, sub_zero]
    rw [h1]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact herr n q
  have hlim0 : Tendsto (fun n : ℕ => ∫ q, Fn n q ∂Γ) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Kc * M * Γ.real univ))
    simp only [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [div_eq_mul_one_div M]
    ring
  have hlimL : Tendsto (fun n : ℕ => ∫ q, Fn n q ∂Γ) atTop (𝓝 (∫ q, Lf q ∂Γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => CL)
      (fun n => (hmeas n).aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun q => by
        simpa [Real.norm_eq_abs] using hFnb n q) (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨N, hN⟩ := exists_nat_ge (max ‖q.2.1‖ ‖q.2.2‖)
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hnN : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    have hR : max ‖q.2.1‖ ‖q.2.2‖ ≤ (n : ℝ) + 1 := by linarith
    have hone := (hψ _ (hR1 n)).2.2.2.1 q.2 ((le_max_left _ _).trans hR)
      (((le_max_right _ _).trans hR).trans (by nlinarith [hR1 n]))
    simp only [Fn, hone, one_mul]
  exact tendsto_nhds_unique hlimL hlim0

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
