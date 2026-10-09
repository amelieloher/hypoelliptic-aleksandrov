module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Bochner integration of measurable measure families -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The actual measure bind obeys Bochner Fubini for an integrable real test. -/
theorem nested_integral_bind {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) [IsFiniteMeasure nu] (k : X → Measure Y) (hk : Measurable k)
    (f : Y → ℝ) (hf : Integrable f (nu.bind k)) :
    (∫ y, f y ∂nu.bind k) = ∫ x, ∫ y, f y ∂k x ∂nu := by
  let K : Kernel X Y := ⟨k, hk⟩
  have heq : (K ∘ₖ Kernel.const Unit nu) () = nu.bind k := by
    rw [Kernel.comp_apply, Kernel.const_apply]
    rfl
  have hi : Integrable f ((K ∘ₖ Kernel.const Unit nu) ()) := heq.symm ▸ hf
  have h := Kernel.integral_comp hi
  rw [heq] at h
  exact h

/-- Mapping starting points before an actual measurable mixture equals precomposing its family. -/
theorem nested_bind_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (nu : Measure X) (f : X → Y) (hf : Measurable f)
    (k : Y → Measure Z) (hk : Measurable k) :
    (nu.map f).bind k = nu.bind (k ∘ f) := by
  ext B hB
  rw [Measure.bind_apply hB hk.aemeasurable,
    Measure.bind_apply hB (hk.comp hf).aemeasurable]
  exact lintegral_map' ((Measure.measurable_coe hB).comp hk).aemeasurable hf.aemeasurable

/-- Restricting an actual measurable measure family remains measurable. -/
theorem nested_measurable_family_restrict {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (k : X → Measure Y) (hk : Measurable k) (S : Set Y) (hS : MeasurableSet S) :
    Measurable (fun x => (k x).restrict S) := by
  apply Measure.measurable_measure.mpr
  intro B hB
  have heq : (fun x => (k x).restrict S B) = fun x => k x (B ∩ S) :=
    funext (fun x => Measure.restrict_apply hB)
  rw [heq]
  exact (Measure.measurable_coe (hB.inter hS)).comp hk

/-- Restriction commutes with the actual measurable measure integral. -/
theorem nested_bind_restrict {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) (k : X → Measure Y) (hk : Measurable k)
    (S : Set Y) (hS : MeasurableSet S) :
    (nu.bind k).restrict S = nu.bind (fun x => (k x).restrict S) := by
  ext B hB
  rw [Measure.restrict_apply hB, Measure.bind_apply (hB.inter hS) hk.aemeasurable,
    Measure.bind_apply hB (nested_measurable_family_restrict k hk S hS).aemeasurable]
  exact lintegral_congr_ae (Filter.Eventually.of_forall
    (fun x => (Measure.restrict_apply hB).symm))

/-- Subtype pullback of a measurable physical family remains measurable on a Borel carrier. -/
theorem nested_measurable_family_comap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (k : X → Measure Y) (hk : Measurable k) (S : Set Y) (hS : MeasurableSet S) :
    Measurable (fun x => (k x).comap (Subtype.val : S → Y)) := by
  apply Measure.measurable_measure.mpr
  intro B hB
  have heq : (fun x => (k x).comap (Subtype.val : S → Y) B) =
      fun x => k x (Subtype.val '' B) := funext (fun x =>
        (MeasurableEmbedding.subtype_coe hS).comap_apply (k x) B)
  rw [heq]
  exact (Measure.measurable_coe
    ((MeasurableEmbedding.subtype_coe hS).measurableSet_image.mpr hB)).comp hk

/-- Subtype pullback commutes with genuine measurable mixtures on a Borel carrier. -/
theorem nested_comap_bind {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) (k : X → Measure Y) (hk : Measurable k)
    (S : Set Y) (hS : MeasurableSet S) :
    (nu.bind k).comap (Subtype.val : S → Y) =
      nu.bind (fun x => (k x).comap (Subtype.val : S → Y)) := by
  ext B hB
  rw [(MeasurableEmbedding.subtype_coe hS).comap_apply]
  rw [Measure.bind_apply ((MeasurableEmbedding.subtype_coe hS).measurableSet_image.mpr hB)
    hk.aemeasurable, Measure.bind_apply hB
      (nested_measurable_family_comap k hk S hS).aemeasurable]
  exact lintegral_congr_ae (Filter.Eventually.of_forall (fun x =>
    ((MeasurableEmbedding.subtype_coe hS).comap_apply (k x) B).symm))

/-- Sums of actual measurable measure families are measurable. -/
theorem nested_measurable_family_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (k l : X → Measure Y) (hk : Measurable k) (hl : Measurable l) :
    Measurable (fun x => k x + l x) := by
  apply Measure.measurable_measure.mpr
  intro B hB
  have heq : (fun x => (k x + l x) B) = fun x => k x B + l x B :=
    funext (fun x => Measure.add_apply _ _ _)
  rw [heq]
  exact ((Measure.measurable_coe hB).comp hk).add ((Measure.measurable_coe hB).comp hl)

/-- Actual measure mixtures distribute over sums of measurable measure families. -/
theorem nested_bind_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) (k l : X → Measure Y) (hk : Measurable k) (hl : Measurable l) :
    nu.bind (fun x => k x + l x) = nu.bind k + nu.bind l := by
  ext B hB
  rw [Measure.bind_apply hB (nested_measurable_family_add k l hk hl).aemeasurable,
    Measure.add_apply, Measure.bind_apply hB hk.aemeasurable,
    Measure.bind_apply hB hl.aemeasurable]
  simp only [Measure.add_apply]
  exact lintegral_add_left ((Measure.measurable_coe hB).comp hk) _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
