module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import Mathlib.Tactic

/-! # Restriction and elementary consequences of source admissibility -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- A function smooth near a set is smooth near every subset. -/
theorem IsSmoothNear.mono {d : ℕ} {psi : KineticPoint d → ℝ}
    {E F : Set (KineticPoint d)} (h : IsSmoothNear psi F) (hEF : E ⊆ F) :
    IsSmoothNear psi E := by
  obtain ⟨U, hU, hFU, hpsi⟩ := h
  exact ⟨U, hU, hEF.trans hFU, hpsi⟩

/-- Smooth-near functions are continuous on the indicated set. -/
theorem IsSmoothNear.continuousOn {d : ℕ} {psi : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (h : IsSmoothNear psi E) : ContinuousOn psi E := by
  obtain ⟨U, _, hEU, hpsi⟩ := h
  have hc := hpsi.continuousOn.comp
    (KineticPoint.homeomorphProd d).continuous.continuousOn
    (fun P hP => mem_image_of_mem _ hP)
  exact (hc.mono hEU).congr (fun P _ =>
    congrArg psi ((KineticPoint.equivProd d).symm_apply_apply P))

/-- Constants are source-smooth near every set. -/
theorem isSmoothNear_const {d : ℕ} (c : ℝ) (E : Set (KineticPoint d)) :
    IsSmoothNear (fun _ => c) E :=
  ⟨univ, isOpen_univ, subset_univ E, contDiffOn_const⟩

/-- Restriction preserves source admissibility without changing the constants. -/
theorem IsAdmissibleSupersolution.mono {d : ℕ} {A : FullKineticCoefficient d}
    {O U : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (hUO : U ⊆ O) :
    IsAdmissibleSupersolution A U p C_A u :=
  ⟨hu.1.mono hUO, fun P R hR hQU psi hpsi =>
    hu.2 P R hR (hQU.trans hUO) psi hpsi⟩

/-- Both signs of an admissible solution restrict to the same smaller set. -/
theorem IsAdmissibleSolution.mono {d : ℕ} {A : FullKineticCoefficient d}
    {O U : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSolution A O p C_A u) (hUO : U ⊆ O) :
    IsAdmissibleSolution A U p C_A u := ⟨hu.1.mono hUO, hu.2.mono hUO⟩

/-- Increasing the comparison constant preserves the source inequality. -/
theorem IsAdmissibleSupersolution.mono_constant {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A C_B : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (hAB : C_A ≤ C_B) :
    IsAdmissibleSupersolution A O p C_B u := by
  refine ⟨hu.1, fun P R hR hQ psi hpsi => (hu.2 P R hR hQ psi hpsi).trans ?_⟩
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hR.le _)) ENNReal.toReal_nonneg

/-- The source norm may use a nonnegative majorant even for signed comparison data. -/
theorem IsAdmissibleSupersolution.nonnegative_constant {d : ℕ}
    {A : FullKineticCoefficient d} {O : Set (KineticPoint d)} {p C_A : ℝ}
    {u : KineticPoint d → ℝ} (hu : IsAdmissibleSupersolution A O p C_A u) :
    IsAdmissibleSupersolution A O p (max C_A 0) u :=
  hu.mono_constant (le_max_left _ _)

/-- The full backward operator annihilates a constant test. -/
theorem backwardOperator_const {d : ℕ} (A : FullKineticCoefficient d)
    (c : ℝ) (P : KineticPoint d) : backwardOperator A (fun _ => c) P = 0 := by
  obtain ⟨ht, hx, _, hv⟩ := comparison_const_formulas c P
  rw [backwardOperator_apply, ht, hx, hv]
  simp [PDE.vecDot, matrixContraction]

/-- The zero-barrier comparison is the exact minimum principle used by the source. -/
theorem admissible_zero_comparison {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (hQ : closure (backwardCylinder P₀ R) ⊆ O) :
    sSup ((fun P => -u P) '' closure (backwardCylinder P₀ R)) ≤
      sSup ((fun P => max (-u P) 0) '' kineticBoundary P₀ R) := by
  have h := hu.2 P₀ R hR hQ (fun _ => 0) (isSmoothNear_const 0 _)
  have hs : localizedSource A (fun _ => 0) u = 0 := by
    funext P
    unfold localizedSource
    simp only [backwardOperator_const, max_self, indicator_zero, Pi.zero_apply]
  simpa only [hs, eLpNorm_zero, ENNReal.toReal_zero, mul_zero, add_zero, zero_sub] using h

end HypoellipticAleksandrov.KineticAleksandrov.Holder
