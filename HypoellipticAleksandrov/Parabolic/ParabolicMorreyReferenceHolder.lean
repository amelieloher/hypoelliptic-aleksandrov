module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffine
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicNearbyAffineIncrement

/-!
# Reference-carrier parabolic Morrey Holder estimate

This module combines the affine-modulo nearby decay with the full-norm
anchoring of the common affine projection on the exact dyadic reference
carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators ENNReal

private theorem parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ParabolicSmoothJetMemLp d u) :
    parabolicMorreyDerivativeLpNorm d u <= parabolicSmoothJetLpNorm d u := by
  let E : ENNReal := parabolicELpNorm d (timeDerivative u) +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => velocityHessian u z i j)
  have hE : E <= parabolicSmoothJetELpNorm d u := by
    dsimp only [E, parabolicSmoothJetELpNorm]
    calc
      parabolicELpNorm d (timeDerivative u) +
          ∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNorm d (fun z => velocityHessian u z i j) <=
          (parabolicELpNorm d u + parabolicELpNorm d (timeDerivative u) +
            ∑ i : Fin d, parabolicELpNorm d (fun z => velocityGradient u z i)) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicELpNorm d (fun z => velocityHessian u z i j) := by
              apply add_le_add_left
              exact (self_le_add_left _ _).trans (self_le_add_right _ _)
      _ = _ := by ac_rfl
  have hreal : E.toReal <= (parabolicSmoothJetELpNorm d u).toReal :=
    ENNReal.toReal_mono (parabolicSmoothJetELpNorm_ne_top hu) hE
  have htoadd : E.toReal = (parabolicELpNorm d (timeDerivative u)).toReal +
      (∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
    apply ENNReal.toReal_add
    · exact hu.2.1.eLpNorm_ne_top
    · apply ENNReal.sum_ne_top.mpr
      intro i _
      apply ENNReal.sum_ne_top.mpr
      intro j _
      exact (hu.2.2.2 i j).eLpNorm_ne_top
  have htosum : (∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
      ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
    calc
      (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal =
          ∑ i : Fin d, (∑ j : Fin d,
            parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
              apply ENNReal.toReal_sum
              intro i _
              apply ENNReal.sum_ne_top.mpr
              intro j _
              exact (hu.2.2.2 i j).eLpNorm_ne_top
      _ = ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
            apply Finset.sum_congr rfl
            intro i _
            apply ENNReal.toReal_sum
            intro j _
            exact (hu.2.2.2 i j).eLpNorm_ne_top
  have hleft : E.toReal = parabolicMorreyDerivativeLpNorm d u := by
    calc
      E.toReal = (parabolicELpNorm d (timeDerivative u)).toReal +
          (∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := htoadd
      _ = (parabolicELpNorm d (timeDerivative u)).toReal +
          ∑ i : Fin d, ∑ j : Fin d,
            (parabolicELpNorm d (fun z => velocityHessian u z i j)).toReal := by
              rw [htosum]
      _ = parabolicMorreyDerivativeLpNorm d u := rfl
  calc
    parabolicMorreyDerivativeLpNorm d u = E.toReal := hleft.symm
    _ <= parabolicSmoothJetLpNorm d u := hreal

/-- Compactly supported smooth data satisfy the local parabolic Holder estimate
on the exact dyadic reference carrier. -/
theorem exists_parabolicMorreyReferenceHolderFullNormConst
    (d : Nat) (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (z : TimeVelocity d)
        (_hz : z ∈ parabolicDyadicReferenceCell d)
        (w : TimeVelocity d)
        (_hw : w ∈ parabolicDyadicReferenceCell d),
        parabolicCoordinateDist z w <= 1 ->
        ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
          HasCompactSupport u ->
          |u z - u w| <=
            C * (parabolicCoordinateDist z w) ^ parabolicMorreyExponent d *
              parabolicSmoothJetLpNorm d u := by
  obtain ⟨C4, hC4_pos, hmodulo⟩ :=
    exists_parabolicMorreyDyadicNearbyAffineModuloDecayConst d hd
  obtain ⟨CI, hCI_pos, hincrement⟩ :=
    exists_parabolicMorreyDyadicNearbyAffineIncrementFullNormConst d hd
  refine ⟨C4 + CI, add_pos hC4_pos hCI_pos, ?_⟩
  intro z hz w hw hrho_one u hu huc
  by_cases hzw : z = w
  · subst w
    have hjet_nonneg : 0 <= parabolicSmoothJetLpNorm d u := ENNReal.toReal_nonneg
    have hpow_nonneg : 0 <=
        (parabolicCoordinateDist z z) ^ parabolicMorreyExponent d :=
      Real.rpow_nonneg (parabolicCoordinateDist_nonneg z z) _
    simpa only [sub_self, abs_zero] using
      mul_nonneg (mul_nonneg (add_pos hC4_pos hCI_pos).le hpow_nonneg) hjet_nonneg
  · obtain ⟨n, hn_lower, hn_upper⟩ :=
      exists_parabolicDyadicGeneration_radius_le_coordinateDist_lt_two_mul_radius
        d z hz w hw hzw
    let rho : Real := parabolicCoordinateDist z w
    let alpha : Real := parabolicMorreyExponent d
    let D : Real := parabolicMorreyDerivativeLpNorm d u
    let J : Real := parabolicSmoothJetLpNorm d u
    let P : TimeVelocity d -> Real := fun x =>
      parabolicMorreyBoxAffineProjection
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) (3 * parabolicCoordinateDist z w) u x
    have hmodulo_bound :
        |(u z - P z) - (u w - P w)| <= C4 * rho ^ alpha * D := by
      simpa only [P, rho, alpha, D] using
        hmodulo z hz w hw n hn_lower hn_upper u hu huc
    have hincrement_bound : |P z - P w| <= CI * rho ^ alpha * J := by
      simpa only [P, rho, alpha, J] using
        hincrement z hz w hw n hn_lower hn_upper hrho_one u hu huc
    have hujet : ParabolicSmoothJetMemLp d u :=
      parabolicSmoothJetMemLp_of_contDiff_hasCompactSupport hu huc
    have hderivative_le_jet : D <= J := by
      simpa only [D, J] using
        parabolicMorreyDerivativeLpNorm_le_parabolicSmoothJetLpNorm hujet
    have hrho_nonneg : 0 <= rho := by
      dsimp only [rho]
      exact parabolicCoordinateDist_nonneg z w
    have hC4rho_nonneg : 0 <= C4 * rho ^ alpha :=
      mul_nonneg hC4_pos.le (Real.rpow_nonneg hrho_nonneg alpha)
    calc
      |u z - u w| = |((u z - P z) - (u w - P w)) + (P z - P w)| := by
        congr 1
        ring
      _ <= |(u z - P z) - (u w - P w)| + |P z - P w| := abs_add_le _ _
      _ <= C4 * rho ^ alpha * D + CI * rho ^ alpha * J :=
        add_le_add hmodulo_bound hincrement_bound
      _ <= C4 * rho ^ alpha * J + CI * rho ^ alpha * J :=
        add_le_add (mul_le_mul_of_nonneg_left hderivative_le_jet hC4rho_nonneg) le_rfl
      _ = (C4 + CI) * rho ^ alpha * J := by ring
      _ = _ := by simp only [rho, alpha, J]

end HypoellipticAleksandrov.Parabolic
