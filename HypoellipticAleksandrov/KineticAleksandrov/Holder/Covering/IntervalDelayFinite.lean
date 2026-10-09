module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.T5
import Mathlib.Tactic

/-! # Interval components and the finite delayed-interval estimate

A bounded open set is decomposed into its countable disjoint order components. Each
forward interval is contained in one component; its preceding interval fits in a left
extension of that component. This avoids any assumption that the forward intervals
are disjoint.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- A bounded nonempty open order-connected real set is its open endpoint interval. -/
theorem open_ordConnected_eq_Ioo {s : Set ℝ} (hs : IsOpen s) (hn : s.Nonempty)
    (hbelow : BddBelow s) (habove : BddAbove s) (hc : s.OrdConnected) :
    s = Ioo (sInf s) (sSup s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, b, hax, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hx)
    rcases hax with ⟨hax, hxb⟩
    have ha : (a+x)/2 ∈ s := hsub ⟨by linarith only [hax], by linarith only [hax, hxb]⟩
    have hb : (x+b)/2 ∈ s := hsub ⟨by linarith only [hax, hxb], by linarith only [hxb]⟩
    exact ⟨lt_of_le_of_lt (csInf_le hbelow ha) (by linarith only [hax, hxb]),
      lt_of_lt_of_le (by linarith only [hxb]) (le_csSup habove hb)⟩
  · intro hx
    obtain ⟨a, ha, hax⟩ := exists_lt_of_csInf_lt hn hx.1
    obtain ⟨b, hb, hxb⟩ := exists_lt_of_lt_csSup hn hx.2
    exact hc.out ha hb ⟨hax.le, hxb.le⟩

/-- The order component of a point in an open real set is open. -/
theorem isOpen_ordConnectedComponent {U : Set ℝ} (hU : IsOpen U) (x : ℝ) :
    IsOpen (ordConnectedComponent U x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [ordConnectedComponent_eq hy]
  exact ordConnectedComponent_mem_nhds.mpr (hU.mem_nhds (ordConnectedComponent_subset hy))

/-- A bounded open real set is a countable disjoint union of nonempty open intervals.
Every nonempty open interval in the set is contained in one of these components. -/
theorem bounded_open_interval_components {U : Set ℝ} (hU : IsOpen U)
    (hbelow : BddBelow U) (habove : BddAbove U) :
    ∃ C : Set (Set ℝ), C.Countable ∧ C.PairwiseDisjoint id ∧
      (∀ s ∈ C, s.Nonempty ∧ s = Ioo (sInf s) (sSup s)) ∧
      (⋃ s ∈ C, s) = U ∧
      (∀ a b : ℝ, a < b → Ioo a b ⊆ U → ∃ s ∈ C, Ioo a b ⊆ s) := by
  let C : Set (Set ℝ) := {s | ∃ x ∈ U, s = ordConnectedComponent U x}
  have hnonempty : ∀ s ∈ C, s.Nonempty := by
    rintro s ⟨x, hx, rfl⟩
    exact nonempty_ordConnectedComponent.mpr hx
  have hopen : ∀ s ∈ C, IsOpen s := by
    rintro s ⟨x, _, rfl⟩
    exact isOpen_ordConnectedComponent hU x
  have hdisj : C.PairwiseDisjoint id := by
    rintro s ⟨x, _, rfl⟩ t ⟨y, _, rfl⟩ hne
    change Disjoint (ordConnectedComponent U x) (ordConnectedComponent U y)
    rw [disjoint_left]
    intro z hxz hyz
    exact hne ((ordConnectedComponent_eq hxz).trans (ordConnectedComponent_eq hyz).symm)
  have hcount : C.Countable := hdisj.countable_of_nonempty_interior fun s hs => by
    change (interior s).Nonempty
    rw [(hopen s hs).interior_eq]
    exact hnonempty s hs
  refine ⟨C, hcount, hdisj, ?_, ?_, ?_⟩
  · rintro s hs
    rcases hs with ⟨x, hx, rfl⟩
    refine ⟨nonempty_ordConnectedComponent.mpr hx, ?_⟩
    exact open_ordConnected_eq_Ioo (isOpen_ordConnectedComponent hU x)
      (nonempty_ordConnectedComponent.mpr hx)
      (hbelow.mono ordConnectedComponent_subset) (habove.mono ordConnectedComponent_subset)
      inferInstance
  · ext x
    constructor
    · intro hx
      obtain ⟨s, ⟨y, _, rfl⟩, hx⟩ := mem_iUnion₂.mp hx
      exact ordConnectedComponent_subset hx
    · intro hx
      exact mem_iUnion₂.mpr ⟨ordConnectedComponent U x, ⟨x, hx, rfl⟩,
        self_mem_ordConnectedComponent.mpr hx⟩
  · intro a b hab hsub
    let x := (a+b)/2
    have hx : x ∈ Ioo a b := ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
    refine ⟨ordConnectedComponent U x, ⟨x, hsub hx, rfl⟩, ?_⟩
    exact subset_ordConnectedComponent hx hsub

/-- The backward interval lies in the left extension of any interval containing its delay. -/
theorem backwardInterval_subset_component_extension {a h m l b : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hsub : Ioo a (a+m*h) ⊆ Ioo l b) :
    Ioo (a-h) a ⊆ Ioo (l-(b-l)/m) b := by
  have hab : a < a+m*h := by nlinarith only [hh, hm]
  obtain ⟨hla, hright⟩ := (Ioo_subset_Ioo_iff hab).mp hsub
  have hlen : h ≤ (b-l)/m := (le_div_iff₀ hm).mpr (by nlinarith only [hla, hright])
  intro x hx
  exact ⟨by linarith only [hx.1, hla, hlen],
    lt_of_lt_of_le hx.2 (le_trans hab.le hright)⟩

/-- The left extension has precisely the delayed-union length multiplier. -/
theorem volume_component_extension {l b m : ℝ} (hm : 0 < m) :
    volume (Ioo (l-(b-l)/m) b) =
      ENNReal.ofReal ((m+1)/m) * volume (Ioo l b) := by
  rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
