module

public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Conjugation of kernels by measurable equivalences

`kernelConj e f κ` is the kernel `x ↦ (κ (e x)).map f.symm`.  It is compatible with the
identity kernel and with kernel composition (`map_map` and Fubini for the bind).  `depMap`
pushes a kernel forward by a family of measurable equivalences that depends on the source
point, again as a kernel.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory ProbabilityTheory

variable {α β γ α' β' γ' : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace α'] [MeasurableSpace β'] [MeasurableSpace γ']

/-- Conjugate a kernel `κ : α' → β'` by measurable equivalences `e : α ≃ᵐ α'`, `f : β ≃ᵐ β'`:
`x ↦ (κ (e x)).map f.symm`. -/
def kernelConj (e : α ≃ᵐ α') (f : β ≃ᵐ β') (κ : Kernel α' β') : Kernel α β :=
  (κ.comap e e.measurable).map f.symm

theorem kernelConj_apply (e : α ≃ᵐ α') (f : β ≃ᵐ β') (κ : Kernel α' β') (a : α) :
    kernelConj e f κ a = (κ (e a)).map f.symm := by
  rw [kernelConj, Kernel.map_apply _ f.symm.measurable, Kernel.comap_apply]

theorem kernelConj_id (e : α ≃ᵐ α') :
    kernelConj e e (Kernel.id : Kernel α' α') = Kernel.id := by
  ext a : 1
  rw [kernelConj_apply, Kernel.id_apply, Kernel.id_apply]
  exact (Measure.map_dirac' e.symm.measurable (e a)).trans (by rw [e.symm_apply_apply])

theorem kernelConj_comp (e : α ≃ᵐ α') (f : β ≃ᵐ β') (g : γ ≃ᵐ γ')
    (κ : Kernel α' β') (η : Kernel β' γ') :
    kernelConj e g (η ∘ₖ κ) = kernelConj f g η ∘ₖ kernelConj e f κ := by
  ext a S hS
  rw [kernelConj_apply, Kernel.comp_apply, Kernel.comp_apply, kernelConj_apply,
    Measure.map_apply g.symm.measurable hS,
    Measure.bind_apply (g.symm.measurable hS) η.measurable.aemeasurable,
    Measure.bind_apply hS (kernelConj f g η).measurable.aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hS) f.symm.measurable]
  refine lintegral_congr fun y => ?_
  rw [kernelConj_apply, f.apply_symm_apply, Measure.map_apply g.symm.measurable hS]

/-- Push a kernel forward by a family of measurable equivalences depending on the source. -/
def depMap (κ : Kernel α β) [IsSFiniteKernel κ] (g : α → β ≃ᵐ β')
    (_hg : Measurable fun p : α × β => g p.1 p.2) : Kernel α β' :=
  (Kernel.id ×ₖ κ).map (fun p : α × β => g p.1 p.2)

theorem depMap_apply (κ : Kernel α β) [IsSFiniteKernel κ] (g : α → β ≃ᵐ β')
    (hg : Measurable fun p : α × β => g p.1 p.2) (a : α) :
    depMap κ g hg a = (κ a).map (g a) := by
  rw [depMap, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hg measurable_prodMk_left]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
