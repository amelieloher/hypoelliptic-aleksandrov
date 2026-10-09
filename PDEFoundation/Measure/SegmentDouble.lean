module

public import PDEFoundation.Measure.Segment
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Double-integral bounds along convex segments

A nonnegative continuous function sampled along every segment in a bounded
open convex domain satisfies a dimensionally explicit double-integral bound.
The first half of the parameter interval follows from the one-sided segment
estimate. The second half follows by reversing the segment and applying
Fubini.
-/

@[expose] public section

namespace PDE

open MeasureTheory

private theorem segmentBlend_swap {d : ℕ}
    (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = segmentBlend y (1 - t) x := by
  simpa only [segmentBlend] using
    (AffineMap.lineMap_apply_one_sub x y t).symm

/-- Double integration along convex segments costs at most `2 ^ d` times the
volume of the domain.

All integrability hypotheses are consequences of continuity and boundedness:
the proof first integrates on the compact closure of `U`. -/
theorem setIntegral_setIntegral_comp_segmentBlend_le_two_pow_mul
    {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hφ : Continuous φ) (hφNonneg : ∀ z, 0 ≤ φ z)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in U, ∫ y in U,
        φ (segmentBlend x t y) ∂volume ∂volume) ≤
      (2 : ℝ) ^ d * (volume U).toReal *
        ∫ z in U, φ z ∂volume := by
  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  have hφIntegrable : IntegrableOn φ U volume :=
    (hφ.continuousOn.integrableOn_compact
      hclosureCompact).mono_set subset_closure
  have hPairContinuous (s : ℝ) :
      Continuous (fun q : Vec d × Vec d =>
        φ (segmentBlend q.1 s q.2)) := by
    apply hφ.comp
    simpa only [segmentBlend_eq_smul_add] using!
      (((continuous_const_smul (1 - s)).comp
          continuous_snd).add
        ((continuous_const_smul s).comp continuous_fst))
  have hPairIntegrable (s : ℝ) :
      Integrable
        (Function.uncurry fun x y : Vec d =>
          φ (segmentBlend x s y))
        ((volumeOn U).prod (volumeOn U)) := by
    have hOnClosure :
        IntegrableOn
          (fun q : Vec d × Vec d =>
            φ (segmentBlend q.1 s q.2))
          (closure U ×ˢ closure U) (volume.prod volume) :=
      (hPairContinuous s).continuousOn.integrableOn_compact
        (hclosureCompact.prod hclosureCompact)
    have hOnProduct :
        IntegrableOn
          (fun q : Vec d × Vec d =>
            φ (segmentBlend q.1 s q.2))
          (U ×ˢ U) (volume.prod volume) :=
      hOnClosure.mono_set
        (Set.prod_mono subset_closure subset_closure)
    change Integrable
      (fun q : Vec d × Vec d =>
        φ (segmentBlend q.1 s q.2))
      ((volume.restrict U).prod (volume.restrict U))
    rw [Measure.prod_restrict]
    exact hOnProduct
  have hFirstHalf (s : ℝ) (hs0 : 0 ≤ s)
      (hsHalf : s ≤ (1 / 2 : ℝ)) :
      (∫ x in U, ∫ y in U,
          φ (segmentBlend x s y) ∂volume ∂volume) ≤
        (2 : ℝ) ^ d * (volume U).toReal *
          ∫ z in U, φ z ∂volume := by
    have hInnerIntegrable :
        IntegrableOn
          (fun x => ∫ y in U,
            φ (segmentBlend x s y) ∂volume)
          U volume := by
      change Integrable
        (fun x => ∫ y,
          φ (segmentBlend x s y) ∂volumeOn U)
        (volumeOn U)
      exact (hPairIntegrable s).integral_prod_left
    have hConstIntegrable :
        IntegrableOn
          (fun _ : Vec d =>
            (2 : ℝ) ^ d * ∫ z in U, φ z ∂volume)
          U volume :=
      integrableOn_const hU.volume_ne_top
    calc
      (∫ x in U, ∫ y in U,
          φ (segmentBlend x s y) ∂volume ∂volume) ≤
          ∫ _x in U,
            (2 : ℝ) ^ d * ∫ z in U, φ z ∂volume
              ∂volume := by
        exact setIntegral_mono_on hInnerIntegrable
          hConstIntegrable hU.measurableSet fun x hx =>
            setIntegral_comp_segmentBlend_le_two_pow_mul
              hU.convex hx hs0 hsHalf hφIntegrable hφNonneg
      _ = (2 : ℝ) ^ d * (volume U).toReal *
          ∫ z in U, φ z ∂volume := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
        ring
  rcases le_total t (1 / 2 : ℝ) with htHalf | hHalfT
  · exact hFirstHalf t ht.1 htHalf
  · have hOneSubNonneg : 0 ≤ 1 - t :=
      sub_nonneg.mpr ht.2
    have hOneSubHalf : 1 - t ≤ (1 / 2 : ℝ) := by
      linarith
    calc
      (∫ x in U, ∫ y in U,
          φ (segmentBlend x t y) ∂volume ∂volume) =
          ∫ x in U, ∫ y in U,
            φ (segmentBlend y (1 - t) x)
              ∂volume ∂volume := by
        apply setIntegral_congr_fun hU.measurableSet
        intro x _hx
        apply setIntegral_congr_fun hU.measurableSet
        intro y _hy
        change φ (segmentBlend x t y) =
          φ (segmentBlend y (1 - t) x)
        rw [segmentBlend_swap]
      _ = ∫ x in U, ∫ y in U,
          φ (segmentBlend x (1 - t) y)
            ∂volume ∂volume := by
        simpa only [volumeOn] using
          (integral_integral_swap
            (hPairIntegrable (1 - t))).symm
      _ ≤ (2 : ℝ) ^ d * (volume U).toReal *
          ∫ z in U, φ z ∂volume :=
        hFirstHalf (1 - t) hOneSubNonneg hOneSubHalf

end PDE
