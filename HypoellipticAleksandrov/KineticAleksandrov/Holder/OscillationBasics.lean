module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! # Finite real oscillation on bounded value sets -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Values on a bounded image lie below its real supremum. -/
theorem le_sup_values {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hE : BddAbove (u '' E)) {P : KineticPoint d}
    (hP : P ∈ E) : u P ≤ sSup (u '' E) := le_csSup hE (mem_image_of_mem u hP)

/-- Values on a bounded image lie above its real infimum. -/
theorem inf_values_le {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hE : BddBelow (u '' E)) {P : KineticPoint d}
    (hP : P ∈ E) : sInf (u '' E) ≤ u P := csInf_le hE (mem_image_of_mem u hP)

/-- Nonempty bounded value sets have nonnegative oscillation. -/
theorem oscillationOn_nonneg {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty)
    (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E)) : 0 ≤ oscillationOn u E := by
  obtain ⟨P, hP⟩ := hne
  exact sub_nonneg.mpr ((inf_values_le hbb hP).trans (le_sup_values hab hP))

/-- Any difference of values is controlled by the literal oscillation. -/
theorem abs_sub_le_oscillationOn {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E))
    {P Q : KineticPoint d} (hP : P ∈ E) (hQ : Q ∈ E) :
    |u P - u Q| ≤ oscillationOn u E := by
  rw [abs_le, oscillationOn]
  constructor
  · linarith only [le_sup_values hab hQ, inf_values_le hbb hP]
  · exact sub_le_sub (le_sup_values hab hP) (inf_values_le hbb hQ)

/-- Passing to a smaller nonempty set cannot increase finite oscillation. -/
theorem oscillationOn_mono {d : ℕ} {u : KineticPoint d → ℝ}
    {E F : Set (KineticPoint d)} (hne : E.Nonempty) (hEF : E ⊆ F)
    (hab : BddAbove (u '' F)) (hbb : BddBelow (u '' F)) :
    oscillationOn u E ≤ oscillationOn u F := by
  exact sub_le_sub (csSup_le_csSup hab (hne.image u) (image_mono hEF))
    (csInf_le_csInf hbb (hne.image u) (image_mono hEF))

/-- Uniform upper and lower bounds control the real oscillation. -/
theorem oscillationOn_le {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty) {a b : ℝ}
    (hlo : ∀ P ∈ E, a ≤ u P) (hhi : ∀ P ∈ E, u P ≤ b) :
    oscillationOn u E ≤ b - a := by
  apply sub_le_sub
  · exact csSup_le (hne.image u) (by rintro _ ⟨P, hP, rfl⟩; exact hhi P hP)
  · exact le_csInf (hne.image u) (by rintro _ ⟨P, hP, rfl⟩; exact hlo P hP)

/-- Zero oscillation forces equality of all values on a bounded set. -/
theorem eq_of_oscillationOn_eq_zero {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E))
    (hz : oscillationOn u E = 0) {P Q : KineticPoint d} (hP : P ∈ E) (hQ : Q ∈ E) :
    u P = u Q := by
  have h := abs_sub_le_oscillationOn hab hbb hP hQ
  rw [hz] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- Compact closures and continuity provide both boundedness conditions. -/
theorem bounded_values_of_compact {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hE : IsCompact E) (hu : ContinuousOn u E) :
    BddAbove (u '' E) ∧ BddBelow (u '' E) :=
  ⟨hE.bddAbove_image hu, hE.bddBelow_image hu⟩

/-- Positive affine transformations transport a finite real supremum exactly. -/
theorem sup_values_pos_affine {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty) (hab : BddAbove (u '' E))
    (a b : ℝ) (ha : 0 < a) :
    sSup ((fun P => a * u P + b) '' E) = a * sSup (u '' E) + b := by
  have h := ((OrderIso.mulLeft₀ a ha).trans (OrderIso.addRight b)).map_csSup'
    (hne.image u) hab
  simpa only [OrderIso.trans_apply, OrderIso.mulLeft₀_apply, OrderIso.addRight_apply,
    image_image, Function.comp_def] using h.symm

/-- Positive affine transformations transport a finite real infimum exactly. -/
theorem inf_values_pos_affine {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty) (hbb : BddBelow (u '' E))
    (a b : ℝ) (ha : 0 < a) :
    sInf ((fun P => a * u P + b) '' E) = a * sInf (u '' E) + b := by
  have h := ((OrderIso.mulLeft₀ a ha).trans (OrderIso.addRight b)).map_csInf'
    (hne.image u) hbb
  simpa only [OrderIso.trans_apply, OrderIso.mulLeft₀_apply, OrderIso.addRight_apply,
    image_image, Function.comp_def] using h.symm

/-- Positive affine transformations scale the literal oscillation. -/
theorem oscillationOn_pos_affine {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty)
    (hab : BddAbove (u '' E)) (hbb : BddBelow (u '' E))
    (a b : ℝ) (ha : 0 < a) :
    oscillationOn (fun P => a * u P + b) E = a * oscillationOn u E := by
  unfold oscillationOn
  rw [sup_values_pos_affine hne hab a b ha, inf_values_pos_affine hne hbb a b ha]
  ring

/-- Continuity preserves the upper value bound on the closure. -/
theorem closure_values_le_sup {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hu : ContinuousOn u (closure E))
    (hab : BddAbove (u '' E)) {P : KineticPoint d} (hP : P ∈ closure E) :
    u P ≤ sSup (u '' E) := by
  have hsub : u '' E ⊆ Iic (sSup (u '' E)) := fun _ hv => le_csSup hab hv
  exact (closure_minimal hsub isClosed_Iic) (hu.image_closure (mem_image_of_mem u hP))

/-- Continuity preserves the lower value bound on the closure. -/
theorem inf_le_closure_values {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hu : ContinuousOn u (closure E))
    (hbb : BddBelow (u '' E)) {P : KineticPoint d} (hP : P ∈ closure E) :
    sInf (u '' E) ≤ u P := by
  have hsub : u '' E ⊆ Ici (sInf (u '' E)) := fun _ hv => csInf_le hbb hv
  exact (closure_minimal hsub isClosed_Ici) (hu.image_closure (mem_image_of_mem u hP))

/-- Compact closure and continuity make closure oscillation equal open-set oscillation. -/
theorem oscillationOn_closure {d : ℕ} {u : KineticPoint d → ℝ}
    {E : Set (KineticPoint d)} (hne : E.Nonempty) (hE : IsCompact (closure E))
    (hu : ContinuousOn u (closure E)) : oscillationOn u (closure E) = oscillationOn u E := by
  have hab := hE.bddAbove_image hu
  have hbb := hE.bddBelow_image hu
  have habe := hab.mono (image_mono subset_closure)
  have hbbe := hbb.mono (image_mono subset_closure)
  have hs : sSup (u '' closure E) = sSup (u '' E) := by
    apply le_antisymm
    · apply csSup_le ((hne.mono subset_closure).image u)
      rintro _ ⟨P, hP, rfl⟩
      exact closure_values_le_sup hu habe hP
    · exact csSup_le_csSup hab (hne.image u) (image_mono subset_closure)
  have hi : sInf (u '' closure E) = sInf (u '' E) := by
    apply le_antisymm
    · exact csInf_le_csInf hbb (hne.image u) (image_mono subset_closure)
    · apply le_csInf ((hne.mono subset_closure).image u)
      rintro _ ⟨P, hP, rfl⟩
      exact inf_le_closure_values hu hbbe hP
  simp only [oscillationOn, hs, hi]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
