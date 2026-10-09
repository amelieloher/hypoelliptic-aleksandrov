module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.PackageProof

/-!
# Uniformity of the smoothing bounds in `m` and locally in `h`

The smoothing estimates: the bounds of (iv) depend on `m` only through
its mass `M` and are uniform for `h` in compact subsets of `(0, ∞)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {q : ℝ}

theorem smoothDensity_le_of_kernel_le {h Cs : ℝ} (hh : 0 < h) (hCs : ∀ z, Φ.kernel h z ≤ Cs)
    (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m] (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ≤ Cs * m.real Set.univ := by
  unfold smoothDensity
  calc ∫ a, Φ.kernel h (y - a) ∂m ≤ ∫ _a, Cs ∂m :=
        integral_mono (integrable_kernel_translate Φ m hh y) (integrable_const _)
          fun a => hCs _
    _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]

/-- The smoothing estimates: for `1 < q`, a compact set `K ⊆ (0, ∞)` of parameters and a mass
bound `M`, there is a constant `C` such that for all `h ∈ K`, all finite measures of mass at most
`M` and all admissible `F`, the ten integrands are integrable with integral at most `C`. -/
theorem package_uniform (hlam : 0 < lam) (hLam' : lam ≤ Lam) (hq : 1 < q) {K : Set ℝ}
    (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ (m : Measure (EvolutionAmbientState d)), IsFiniteMeasure m →
      m.real Set.univ ≤ M → ∀ F : EvolutionAmbientState d → PDE.Mat d,
        IsAdmissibleCoefficient lam Lam F → PackageIntegrable Φ h F m q C := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  obtain ⟨C1, C2, Cfi, hCfi, hk⟩ := exists_kernelConsts (Φ := Φ) hK hsub
  obtain ⟨Cs, hCs0, hCs⟩ := Φ.exists_sup_bound hK hsub
  obtain ⟨Wint, hW⟩ := Φ.weight_integral_le 2 hK hsub
  set R : ℝ := Cs * M with hR
  set W : ℝ := max Wint 0 with hWdef
  have hRn : 0 ≤ R := by positivity
  have hcs : 0 ≤ pkgCoefSum d Lam q C1 C2 Cfi R := by unfold pkgCoefSum; positivity
  refine ⟨pkgCoefSum d Lam q C1 C2 Cfi R * (M * W), by positivity, ?_⟩
  intro h hhK m hfin hmM F hF
  have := hfin
  have hh : 0 < h := hsub hhK
  by_cases hm : m = 0
  · subst hm
    exact packageIntegrable_zero hq (by positivity)
  · have hmr : 0 ≤ m.real Set.univ := measureReal_nonneg
    have hint : ∫ z, weight2 Φ h z ≤ W := (hW h hhK).trans (le_max_left _ _)
    have hint0 : 0 ≤ ∫ z, weight2 Φ h z := integral_nonneg fun z => weight2_nonneg hh z
    have hRm : ∀ y, smoothDensity Φ h m y ≤ R := fun y =>
      (smoothDensity_le_of_kernel_le Φ hh (fun z => hCs h hhK z) m y).trans
        (mul_le_mul_of_nonneg_left hmM hCs0)
    refine (packageIntegrable_of_ne_zero hlam hLam' hF hh hm (hk h hhK) hq hCfi hRm).mono ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul hmM (hint.trans le_rfl) hint0 hM) hcs

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
