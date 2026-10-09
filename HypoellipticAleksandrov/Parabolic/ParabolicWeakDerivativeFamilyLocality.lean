module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndexBoundCoherence
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal

/-!
# Locality for coherent parabolic weak-derivative families

This module restricts the raw domain of a coherent family and truncates its
parabolic derivative bound while preserving its selected representatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open MeasureTheory

/-- Restrict a coherent weak-derivative family to a smaller raw domain,
without changing its selected representatives. -/
def restrict
    {d L : ℕ} {U V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (hVU : V ⊆ U) :
    ParabolicWeakDerivativeFamily d L V u where
  representative := F.representative
  memLp beta := (F.memLp beta).mono hVU
  zero_ae := F.zero_ae.filter_mono <|
    ae_mono <| Measure.restrict_mono_set volume hVU
  hasWeakTimeSucc beta h := (F.hasWeakTimeSucc beta h).restrict hVU
  hasWeakVelocitySucc beta i h :=
    (F.hasWeakVelocitySucc beta i h).restrict hVU

/-- Domain restriction preserves every selected representative literally. -/
@[simp] theorem restrict_representative
    {d L : ℕ} {U V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (hVU : V ⊆ U) (beta : ParabolicDerivativeIndex d L) :
    (restrict F hVU).representative beta = F.representative beta :=
  rfl

/-- Truncate a coherent weak-derivative family to a lower parabolic bound,
using the bound cast to retain the same representatives. -/
def truncate
    {d M L : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (hML : M ≤ L) :
    ParabolicWeakDerivativeFamily d M U u where
  representative := fun beta => F.representative
    (ParabolicDerivativeIndex.castLE hML beta)
  memLp beta := F.memLp (ParabolicDerivativeIndex.castLE hML beta)
  zero_ae := by
    simpa only [ParabolicDerivativeIndex.castLE_zero] using F.zero_ae
  hasWeakTimeSucc beta h := by
    simpa only [ParabolicDerivativeIndex.castLE_timeSucc] using
      F.hasWeakTimeSucc (ParabolicDerivativeIndex.castLE hML beta) (h.trans hML)
  hasWeakVelocitySucc beta i h := by
    simpa only [ParabolicDerivativeIndex.castLE_velocitySucc] using
      F.hasWeakVelocitySucc
        (ParabolicDerivativeIndex.castLE hML beta) i (h.trans hML)

/-- Bound truncation selects the representative at the corresponding
enlarged-bound index literally. -/
@[simp] theorem truncate_representative
    {d M L : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (hML : M ≤ L) (beta : ParabolicDerivativeIndex d M) :
    (truncate F hML).representative beta =
      F.representative (ParabolicDerivativeIndex.castLE hML beta) :=
  rfl

end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
