module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullSourceNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullScaling
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Tactic

/-! # The source nearly-full superlevel estimate with uniform constants -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- The source near-full estimate, with the nonnegative constant needed by its threshold. -/
theorem near_full_with_nonneg_constant (d : ℕ) (Lam p C_A : ℝ) (hp : 1 ≤ p) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell eta : ℝ),
        0 < R → 0 ≤ ell → 0 < eta → eta < 1 →
      ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
          (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
      ∀ P ∈ kineticAffine P₀ R '' cap d, (1 - C₁ * eta ^ (1 / p)) * ell ≤ u P := by
  obtain ⟨f, hf, hrange, hcap, _, hsupport⟩ := exists_unit_cutoff d
  obtain ⟨C₀, hC₀, hop⟩ := exists_scaledUnitCutoff_operator_bound hf Lam
  let V := (volume (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)).toReal
  let C₁ := max C_A 0 * C₀ * V ^ (1 / p)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hCA : 0 ≤ max C_A 0 := le_max_right _ _
  refine ⟨C₁, mul_nonneg (mul_nonneg hCA hC₀) (Real.rpow_nonneg hV _), ?_⟩
  intro lam hlam hLam A hA P₀ R ell eta hR hell heta heta1 O hO hQO u hu0 hu hdensity P hP
  let Q := backwardCylinder P₀ R
  let psi := scaledUnitCutoff f P₀ R ell
  have hQU : Q ⊆ O := subset_closure.trans hQO
  have hEll : 0 < lam ∧ lam ≤ Lam := ⟨hlam, hLam⟩
  have hEta : eta ∈ Ioo (0 : ℝ) 1 := ⟨heta, heta1⟩
  have hB : 0 ≤ C₀ * ell * (R ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg hC₀ hell) (inv_nonneg.mpr (sq_nonneg R))
  have hopQ := hop lam hEll.1 A hA P₀ R ell hR hell
  have hsmooth := scaledUnitCutoff_isSmoothNear hf P₀ R ell (closure Q)
  have hpsi := hsmooth.continuousOn
  have huQ := hu.1.mono hQU
  have hnorm := localizedSource_norm_le_sublevel_volume A
    (isOpen_backwardCylinder P₀ R hR) (volume_backwardCylinder_lt_top P₀ hR).ne
    (hpsi.mono subset_closure) huQ
    (measurable_scaledUnitCutoff_backwardOperator hf hA.1 P₀ R ell)
    ell (C₀ * ell * (R ^ 2)⁻¹) p hB hp
    (fun T _ => (scaledUnitCutoff_bounds hrange P₀ R ell hell T).2) hopQ
  have hdens := near_full_sublevel_volume hO hu.1 P₀ hR hQU ell eta hdensity
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hrpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hdens
    (one_div_nonneg.mpr hp0.le)
  have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_left hrpow hB)
  rw [volume_backwardCylinder_toReal P₀ hR,
    Real.mul_rpow hEta.1.le (mul_nonneg (pow_pos hR _).le hV),
    Real.mul_rpow (pow_pos hR _).le hV] at hnorm'
  have hscale := near_full_radius_cancellation d hR p
  have hmul : max C_A 0 * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
      (eLpNorm (localizedSource A psi u) (ENNReal.ofReal p) (volume.restrict Q)).toReal ≤
        C₁ * eta ^ (1 / p) * ell := by
    calc
      _ ≤ max C_A 0 * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (C₀ * ell * (R ^ 2)⁻¹ *
            (eta ^ (1 / p) * ((R ^ (4 * d + 2)) ^ (1 / p) * V ^ (1 / p)))) :=
        mul_le_mul_of_nonneg_left hnorm' (mul_nonneg hCA (Real.rpow_nonneg hR.le _))
      _ = C₁ * eta ^ (1 / p) * ell := by
        calc
          _ = (max C_A 0 * C₀ * V ^ (1 / p)) * eta ^ (1 / p) * ell *
              (R ^ (2 - (4 * (d : ℝ) + 2) / p) * (R ^ 2)⁻¹ *
                (R ^ (4 * d + 2)) ^ (1 / p)) := by ring
          _ = _ := by rw [hscale, mul_one]
  have hboundary : sSup ((fun T => max (psi T - u T) 0) '' kineticBoundary P₀ R) ≤ 0 := by
    apply csSup_le ((kineticBoundary_nonempty P₀ hR).image _)
    rintro _ ⟨T, hT, rfl⟩
    have hz := scaledUnitCutoff_boundary_eq_zero hsupport P₀ hR ell hT
    have hn := hu0 T (hQO hT.1)
    change max (scaledUnitCutoff f P₀ R ell T - u T) 0 ≤ 0
    rw [hz, zero_sub]
    exact max_le (neg_nonpos.mpr hn) le_rfl
  have hPunit : P ∈ Q := by
    obtain ⟨T, hT, rfl⟩ := hP
    exact (kineticAffine_mem_cylinder P₀ T hR).mpr
      ((cap_compact_inside d).2 (subset_closure hT))
  have hbounded := (isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image
    (hpsi.sub (hu.1.mono hQO))
  have hpoint := (le_csSup hbounded (mem_image_of_mem (fun T => psi T - u T)
    (subset_closure hPunit))).trans (hu.nonnegative_constant.2 P₀ R hR hQO psi hsmooth)
  have hplateau : psi P = ell := scaledUnitCutoff_eq_level hcap P₀ hR ell hP
  rw [hplateau] at hpoint
  change ell - u P ≤ _ at hpoint
  have hlast := hpoint.trans (add_le_add hboundary hmul)
  simp only [zero_add] at hlast
  linarith only [hlast]

/-- The exact source near-full conditions, with its constant fixed before ellipticity data. -/
theorem near_full (d : ℕ) (hd : 1 ≤ d) (Lam p C_A : ℝ) (hp : 1 ≤ p) :
    ∃ C₁ : ℝ, ∀ lam : ℝ, 0 < lam → lam ≤ Lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell eta : ℝ),
        0 < R → 0 ≤ ell → 0 < eta → eta < 1 →
      ∀ O : Set (KineticPoint d), IsOpen O → closure (backwardCylinder P₀ R) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
          (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal →
      ∀ P ∈ kineticAffine P₀ R '' cap d, (1 - C₁ * eta ^ (1 / p)) * ell ≤ u P := by
  cases d with
  | zero => omega
  | succ n =>
    obtain ⟨C₁, _, hC₁⟩ := near_full_with_nonneg_constant (n + 1) Lam p C_A hp
    exact ⟨C₁, hC₁⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
