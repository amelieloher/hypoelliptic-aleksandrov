module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionSecond
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionWeakSupport

/-! # No derivative mass outside the literal profile domain -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- The selected first and second weak representatives vanish almost everywhere outside
`H < 1`, including the profile boundary. An open zero collar avoids any level-set premise. -/
theorem construction_extended_jets_zero_outside_profile {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m) (t : ℝ) :
    ∀ᵐ x ∂volume, 1 ≤ profileFunction h (spatialCoordinateCLE d x) →
      (∀ i, constructionExtendedPackedGradient h r mu R m t x i = 0) ∧
      (∀ i k, constructionExtendedPackedHessian h r mu R m t x i k = 0) := by
  let s := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x) -
    spatialPackedBarrier d mu R t x
  let D : Set (PDE.Vec (d + d)) := {x | s x < 0} ∪
    {x | R ^ 2 < PDE.vecNormSq (spatialCoordinateCLE d x).2}
  let u := fun x => zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩
  have hD : IsOpen D :=
    (isOpen_lt (((continuous_selectedFlatProfile h r).comp
      (spatialCoordinateCLE d).continuous).sub
        (contDiff_spatialPackedBarrier d mu R t).continuous) continuous_const).union
      (isOpen_lt continuous_const (PDE.contDiff_vecNormSq.continuous.comp
        (spatialCoordinateCLE d).continuous.snd))
  have hu : u =ᵐ[volume.restrict D] 0 := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    change zeroExtendedProfile (profileFunction h) alpha r mu R
      ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩ = 0
    rw [construction_zero_extension_eq_cutoff h r mu R m hr hmu hR hm hscale hmargin]
    rcases hx with hs | hv
    · change constructionVelocityCutoff m R (spatialCoordinateCLE d x) * timeCutoffTheta (s x) = 0
      rw [timeCutoffTheta_eq_zero _ hs.le, mul_zero]
    · rw [constructionVelocityCutoff_eq_zero m R hm _ hv.le, zero_mul]
  have hsub : ∀ x, 1 ≤ profileFunction h (spatialCoordinateCLE d x) → x ∈ D := by
    intro x hx
    by_cases hv : PDE.vecNormSq (spatialCoordinateCLE d x).2 ≤ R ^ 2
    · left
      have hf := flatProfile_eq_one_sub (profileFunction h) alpha r hr
        (spatialCoordinateCLE d x) (hscale.trans hx)
      have hb : 0 < spatialPackedBarrier d mu R t x := by
        unfold spatialPackedBarrier barrier
        have he := (div_le_one (sq_pos_of_pos hR)).mpr hv
        exact mul_pos (Real.exp_pos _) (by linarith only [he])
      change selectedFlatProfile h r (spatialCoordinateCLE d x) -
        spatialPackedBarrier d mu R t x < 0
      change flatProfile (profileFunction h) flatteningPsi flatteningOffset alpha r
        (spatialCoordinateCLE d x) - _ < 0
      rw [hf]
      linarith only [hx, hb]
    · exact Or.inr (lt_of_not_ge hv)
  have hg (i : Fin (d + d)) :
      (fun x => constructionExtendedPackedGradient h r mu R m t x i) =ᵐ[volume.restrict D] 0 := by
    apply construction_weak_derivative_zero_on_open D hD i u _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m t i) hu
    exact weakPartial_on_of_global D i u _
      (construction_zero_extension_weak_first hd ha ha1 h r mu R m hr hmu hR hm
        hscale hmargin t i)
  have hh (i k : Fin d) :
      (fun x => constructionExtendedPackedHessian h r mu R m t x i k) =ᵐ[volume.restrict D] 0 := by
    apply construction_weak_derivative_zero_on_open D hD (Fin.natAdd d i) _ _
      (construction_extendedHessian_locallyIntegrable h r hr mu R m t i k)
      (hg (Fin.natAdd d k))
    exact weakPartial_on_of_global D (Fin.natAdd d i) _ _
      (construction_extended_velocityJet_weak hd ha ha1 h r hr mu R m t i k)
  have hga := ae_all_iff.mpr hg
  have hha := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hh i))
  have hga' := (ae_restrict_iff' hD.measurableSet).mp hga
  have hha' := (ae_restrict_iff' hD.measurableSet).mp hha
  filter_upwards [hga', hha'] with x hx hy
  intro hprof
  exact ⟨hx (hsub x hprof), hy (hsub x hprof)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
