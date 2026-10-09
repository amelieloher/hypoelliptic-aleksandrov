module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization

/-!
# Globalization of compactly supported weak-derivative families

A finite parabolic weak-derivative family whose selected representatives are
supported in its open carrier extends to the ambient time--velocity space.
The ambient family retains those representatives literally and is rooted at
the selected zero representative.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

/-- Globalize a finite weak-derivative family whose selected representatives
have topological support in the open local carrier. The ambient root is the
selected zero representative, not the supplied local root. -/
def ParabolicWeakDerivativeFamily.compactSupportGlobalize
    {d L : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) {f : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U f)
    (hsupp : ∀ beta, tsupport (F.representative beta) ⊆ U) :
    ParabolicWeakDerivativeFamily d L Set.univ
      (F.representative (ParabolicDerivativeIndex.zero d L)) where
  representative := F.representative
  memLp beta := by
    simpa only [ParabolicMemLpOn, timeVelocityVolumeOn, Measure.restrict_univ] using
      (F.memLp beta).memLp_of_support_subset hU.measurableSet
        ((subset_tsupport _).trans (hsupp beta))
  zero_ae := Filter.Eventually.of_forall fun _ ↦ rfl
  hasWeakTimeSucc beta h :=
    (F.hasWeakTimeSucc beta h).univ_of_tsupport_subset hU
      (hsupp beta) (hsupp (ParabolicDerivativeIndex.timeSucc beta h))
  hasWeakVelocitySucc beta i h :=
    (F.hasWeakVelocitySucc beta i h).univ_of_tsupport_subset hU
      (hsupp beta) (hsupp (ParabolicDerivativeIndex.velocitySucc beta i h))

/-- Compact-support globalization preserves every selected representative
literally. -/
@[simp] theorem ParabolicWeakDerivativeFamily.compactSupportGlobalize_representative
    {d L : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) {f : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U f)
    (hsupp : ∀ beta, tsupport (F.representative beta) ⊆ U)
    (beta : ParabolicDerivativeIndex d L) :
    (F.compactSupportGlobalize hU hsupp).representative beta =
      F.representative beta := rfl

/-- If both the selected zero representative and the supplied local root
vanish off a measurable carrier, their local almost-everywhere equality
extends to ambient volume. -/
theorem ParabolicWeakDerivativeFamily.zero_representative_ae_eq_of_support_subset
    {d L : ℕ} {U : Set (TimeVelocity d)}
    (hU : MeasurableSet U) {f : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U f)
    (hFzero : tsupport
      (F.representative (ParabolicDerivativeIndex.zero d L)) ⊆ U)
    (hf : Function.support f ⊆ U) :
    F.representative (ParabolicDerivativeIndex.zero d L)
      =ᵐ[(volume : Measure (TimeVelocity d))] f := by
  refine ae_of_ae_restrict_of_ae_restrict_compl U F.zero_ae ?_
  apply ae_restrict_of_forall_mem hU.compl
  intro z hz
  show F.representative (ParabolicDerivativeIndex.zero d L) z = f z
  have hzU : z ∉ U := hz
  have hFz : F.representative (ParabolicDerivativeIndex.zero d L) z = 0 := by
    by_contra hne
    exact hzU (hFzero (subset_tsupport _ (Function.mem_support.mpr hne)))
  have hfz : f z = 0 := by
    by_contra hne
    exact hzU (hf (Function.mem_support.mpr hne))
  rw [hFz, hfz]

end HypoellipticAleksandrov.Parabolic
