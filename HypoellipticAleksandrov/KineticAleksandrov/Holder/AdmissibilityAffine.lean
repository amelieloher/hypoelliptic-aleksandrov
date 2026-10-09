module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-! # Positive affine invariance of source comparison -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- Positive affine transformations preserve precisely the same Aleksandrov data. -/
theorem admissible_pos_affine {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (a b : ℝ) (ha : 0 < a) :
    IsAdmissibleSupersolution A O p C_A (fun P => a * u P + b) := by
  refine ⟨continuousOn_const.mul hu.1 |>.add continuousOn_const, ?_⟩
  intro P₀ R hR hQ psi hpsi
  let phi : KineticPoint d → ℝ := fun P => a⁻¹ * psi P + (-b/a)
  have hphi : IsSmoothNear phi (closure (backwardCylinder P₀ R)) :=
    hpsi.affine _ _
  have heq : psi = fun P => a * phi P + b := by
    funext P
    dsimp [phi]
    field_simp
    ring
  have hd : (fun P => psi P - (a*u P+b)) = fun P => a*(phi P-u P) := by
    funext P
    rw [heq]
    ring
  have hm : (fun P => max (psi P-(a*u P+b)) 0) =
      fun P => a * max (phi P-u P) 0 := by
    funext P
    rw [show psi P-(a*u P+b) = a*(phi P-u P) from congrFun hd P]
    rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
  have hcompact := isCompact_closure_backwardCylinder P₀ R hR
  have hcont := hphi.continuousOn.sub (hu.1.mono hQ)
  have hab := hcompact.bddAbove_image hcont
  have hB : kineticBoundary P₀ R ⊆ closure (backwardCylinder P₀ R) := fun _ h => h.1
  have habB := (hcompact.bddAbove_image (hcont.sup (continuousOn_const (c := (0 : ℝ))))).mono
    (image_mono hB)
  have hne := (backwardCylinder_nonempty P₀ hR).mono subset_closure
  have hneB := kineticBoundary_nonempty P₀ hR
  have hs : sSup ((fun P => psi P-(a*u P+b)) '' closure (backwardCylinder P₀ R)) =
      a * sSup ((fun P => phi P-u P) '' closure (backwardCylinder P₀ R)) := by
    rw [hd]
    simpa only [add_zero, Pi.sub_apply] using sup_values_pos_affine hne hab a 0 ha
  have hsB : sSup ((fun P => max (psi P-(a*u P+b)) 0) '' kineticBoundary P₀ R) =
      a * sSup ((fun P => max (phi P-u P) 0) '' kineticBoundary P₀ R) := by
    rw [hm]
    simpa only [add_zero, Pi.sub_apply] using sup_values_pos_affine hneB habB a 0 ha
  have hsource : localizedSource A psi (fun P => a*u P+b) =ᵐ[
      volume.restrict (backwardCylinder P₀ R)] a • localizedSource A phi u := by
    filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P hP
    have hop : backwardOperator A psi P = a * backwardOperator A phi P := by
      rw [heq]
      exact backwardOperator_affine A hphi (subset_closure hP) a b
    have hlt : a*u P+b < psi P ↔ u P < phi P := by
      rw [heq]
      exact (add_lt_add_iff_right b).trans (mul_lt_mul_iff_right₀ ha)
    simp only [localizedSource, indicator_apply, mem_ofPred_eq, hlt, hop, Pi.smul_apply,
      smul_eq_mul]
    split_ifs
    · rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
    · simp only [mul_zero]
  have hn : (eLpNorm (localizedSource A psi (fun P => a*u P+b)) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R))).toReal =
      a * (eLpNorm (localizedSource A phi u) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))).toReal := by
    rw [eLpNorm_congr_ae hsource, eLpNorm_const_smul, ENNReal.toReal_mul]
    simp [Real.norm_eq_abs, abs_of_pos ha]
  rw [hs, hsB, hn]
  have h := mul_le_mul_of_nonneg_left (hu.2 P₀ R hR hQ phi hphi) ha.le
  convert h using 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
