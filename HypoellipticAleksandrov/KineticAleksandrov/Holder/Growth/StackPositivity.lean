module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullThreshold
import Mathlib.Tactic

/-! # Uniform propagation from the source cap to an entire forward stack -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- A common dimensionless propagation constant works for every physical cap-to-stack path. -/
theorem exists_stack_positivity_constant (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (m : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ (p C_A : ℝ), 1 ≤ p → ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P0 : KineticPoint d) (r ell : ℝ), 0 < r → 0 ≤ ell →
      ∀ O : Set (KineticPoint d), IsOpen O →
        closure (kineticAffine P0 r '' stackComparisonRegion d m) ⊆ O →
      ∀ u : KineticPoint d → ℝ, (∀ P ∈ O, 0 ≤ u P) →
        IsAdmissibleSupersolution A O p C_A u →
        (∀ Z ∈ kineticAffine P0 r '' cap d, (3 / 4 : ℝ) * ell ≤ u Z) →
        ∀ P ∈ forwardStack P0 r m, delta * ell ≤ u P := by
  let M := (m : ℝ) + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hacc : 0 < stackAcceleration m := by unfold stackAcceleration; positivity
  obtain ⟨c, hc, hc1, hprop⟩ := propagation_dimensionless d hd lam Lam
    (1 / (32 * M)) (stackAcceleration m * Real.sqrt M)
    (1 / (1024 * M ^ (3 / 2 : ℝ))) (1 / (16 * Real.sqrt M))
    hlam hLam (by positivity) (by
      apply (div_le_one (by positivity : 0 < 32 * M)).mpr
      dsimp only [M]
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith only [hm]) (by positivity) (by positivity) (by positivity)
  refine ⟨(3 / 4 : ℝ) * c, by positivity, by linarith only [hc1], ?_⟩
  intro p C_A hp A hA P0 r ell hr hell O hO hregion u hnonneg hu hcap P hP
  obtain ⟨x, v, hsk, _, _, hxP, hvP, hTlo, hThi, hcapCorr, hfullCorr⟩ :=
    exists_stack_corridors P0 P hr m hP
  obtain ⟨hscaleTime, hscaleH, hscaleX, hscaleV⟩ := stack_propagation_scaling m hr
  have hT1 : 0 < M * r ^ 2 := mul_pos hM (sq_pos_of_pos hr)
  have hPO : P ∈ O := by
    have hpoint : P ∈ corridor (stackStartTime P0 r) (-(r ^ 2 / 32))
        (P.time - stackStartTime P0 r) (r ^ 3 / (2 * 8 ^ 3)) (r / 16) x v := by
      refine ⟨⟨by linarith only [hTlo, sq_pos_of_pos hr], le_rfl⟩, ?_, ?_⟩
      · rw [hxP, sub_self]
        norm_num [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
        positivity
      · rw [hvP, sub_self]
        norm_num [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
        positivity
    exact hregion (subset_closure (hfullCorr hpoint))
  have hprop' := hprop (M * r ^ 2) hT1 p C_A hp A hA O hO
    (stackStartTime P0 r) P hPO
  rw [neg_mul, hscaleTime, hscaleH, hscaleX, hscaleV] at hprop'
  have htlo : r ^ 2 / 32 ≤ P.time - stackStartTime P0 r := by
    linarith only [hTlo, sq_pos_of_pos hr]
  have hbound := hprop' htlo hThi x v (by simpa only [stackAcceleration] using hsk) hxP hvP
    (fun Q hQ => hregion (subset_closure (hfullCorr hQ))) ((3 / 4 : ℝ) * ell)
    (mul_nonneg (by norm_num) hell) u hnonneg hu
    (fun Q hQ ht => hcap Q (hcapCorr ⟨⟨hQ.1.1, sub_nonpos.mpr ht⟩, hQ.2⟩))
  convert hbound using 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
