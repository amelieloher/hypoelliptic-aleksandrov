module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatchModulus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatchRadius
import Mathlib.Tactic

/-! # A positive value yields the nonlinear return-patch height estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder

/-- The pointwise height estimate obtained from Holder continuity and power propagation. -/
theorem return_holder_patch_point (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
      ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
      1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
      ∀ z zStar : Point, z ∈ returnBox v a → zStar ∈ returnFutureRegion →
      0 < sSup (u '' returnBox v b) →
      c₀ * (b - a) ^ beta * (u z) ^ (1 + beta / alpha) *
        sSup (u '' returnBox v b) ^ (-beta / alpha) ≤ u zStar := by
  obtain ⟨alpha, D, ha, ha1, hD, hmod⟩ := return_holder_modulus lam Lam hlam hLam hp6
  obtain ⟨beta, cp, hb, hcp, hpatch⟩ := return_patch_power lam Lam hlam hLam hp6
  let δ := returnHolderRadiusFactor alpha D
  let c₀ := (cp * δ ^ beta / 2) / (8192 : ℝ) ^ beta
  have hδ := returnHolderRadiusFactor_bounds alpha D ha hD
  have hδpos : 0 < δ := hδ.1
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨alpha, beta, c₀, ha, ha1, hb, hc₀, ?_⟩
  intro A u hu a b v habase hab hb1 hv z zStar hz hstar hMb
  have hzref := returnBox_subset_reference v a hv (by linarith) hz
  have huz0 := hu.2.1 z (by linarith [hzref.1.1])
  by_cases huz : u z = 0
  · rw [huz, Real.zero_rpow (by positivity : (1 + beta / alpha) ≠ 0), mul_zero, zero_mul]
    exact hu.2.1 zStar (by linarith [hstar.1.1])
  have huzpos : 0 < u z := lt_of_le_of_ne huz0 (Ne.symm huz)
  let M := sSup (u '' returnBox v b)
  let h := (b - a) / 8192
  let ell := δ * h * (u z / M) ^ (1 / alpha)
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by dsimp [h]; linarith
  have hOpos : returnBox v b ⊆ {q | 0 < q.time} := by
    intro q hq
    have hqref := returnBox_subset_reference v b hv hb1 hq
    change 0 < q.time
    linarith [hqref.1.1]
  obtain ⟨B, hB⟩ := hu.1
  have hbounded : BddAbove (u '' returnBox v b) := ⟨B, by
    rintro _ ⟨q, hq, rfl⟩
    exact (le_abs_self _).trans (hB q (hOpos hq))⟩
  have huzM : u z ≤ M := le_csSup hbounded
    (mem_image_of_mem u (returnBox_mono v hab.le hz))
  have hradius := return_holder_radius alpha D h (u z) M ha hD hh huzpos hMb huzM
  change 0 < ell ∧ ell ≤ h ∧ D * M * (ell / h) ^ alpha ≤ u z / 2 at hradius
  have hlower : ∀ q ∈ backwardCylinder z ell, u z / 2 ≤ u q := by
    intro q hq
    have hc := hmod A u hu a b v habase hab hb1 hv z q ell hz
      hradius.1 hradius.2.1 (subset_closure hq)
    have hdiff := hc.trans hradius.2.2
    linarith [(abs_le.mp hdiff).2]
  have hheight := hpatch A u hu ell (u z / 2) z zStar hradius.1
    (hradius.2.1.trans hh1) (by positivity) hzref hstar hlower
  have he := return_holder_height_factor alpha beta cp δ h (u z) M
    hδ.1.le hh.le huzpos hMb
  have hhpower : h ^ beta = (b - a) ^ beta / (8192 : ℝ) ^ beta :=
    Real.div_rpow (by linarith) (by norm_num) beta
  change cp * (δ * h * (u z / M) ^ (1 / alpha)) ^ beta * (u z / 2) ≤ u zStar at hheight
  rw [he, hhpower] at hheight
  convert hheight using 1; dsimp [c₀, M]; ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
