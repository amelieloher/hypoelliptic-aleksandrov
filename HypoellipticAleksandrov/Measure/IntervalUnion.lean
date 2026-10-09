module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.OrdConnectedComponent
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Monotone enlargements of families of real intervals

This file formalizes the one-dimensional measure lemma used in the
Krylov--Safonov crawling-of-ink-spots argument.  The family of intervals may
be uncountable: countability is obtained from the disjoint open connected
components of its union.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- A nonempty open order-connected subinterval of an ambient interval. -/
def IsOpenSubinterval (J I : Set ℝ) : Prop :=
  I.Nonempty ∧ IsOpen I ∧ I.OrdConnected ∧ I ⊆ J

private theorem connectedComponentIn_eq_ordConnectedComponent_of_mem
    (U : Set ℝ) {x : ℝ} (hx : x ∈ U) :
    connectedComponentIn U x = ordConnectedComponent U x := by
  apply Subset.antisymm
  · letI : OrdConnected (connectedComponentIn U x) :=
      isPreconnected_connectedComponentIn.ordConnected
    exact Set.subset_ordConnectedComponent (mem_connectedComponentIn hx)
      (connectedComponentIn_subset U x)
  · have hpre : IsPreconnected (ordConnectedComponent U x) :=
      Set.OrdConnected.isPreconnected
        (show OrdConnected (ordConnectedComponent U x) from inferInstance)
    exact IsPreconnected.subset_connectedComponentIn hpre
      (self_mem_ordConnectedComponent.mpr hx) ordConnectedComponent_subset

/-- Krylov--Safonov Lemma 2.2, including the bounded-union extension needed
for the source's later whole-line application. -/
theorem volume_sUnion_monotone_interval_enlargement
    (kappa : ℝ) (hkappa : 1 < kappa)
    (J : Set ℝ) (hJopen : IsOpen J) (hJord : J.OrdConnected)
    (B : Set (Set ℝ)) (g : Set ℝ → Set ℝ)
    (hB : ∀ I ∈ B, IsOpenSubinterval J I)
    (hUbounded : Bornology.IsBounded (⋃₀ B))
    (hg : ∀ I, IsOpenSubinterval J I → IsOpenSubinterval J (g I))
    (hmeasure : ∀ I, IsOpenSubinterval J I → Bornology.IsBounded I →
      volume (g I) < ENNReal.ofReal kappa * volume I)
    (hmono : ∀ I₁ I₂, IsOpenSubinterval J I₁ → IsOpenSubinterval J I₂ →
      I₁ ⊆ I₂ → g I₁ ⊆ g I₂) :
    volume (⋃₀ (g '' B)) ≤ ENNReal.ofReal kappa * volume (⋃₀ B) := by
  have _hkappa : 0 < kappa := lt_trans zero_lt_one hkappa
  have _hJopen : IsOpen J := hJopen
  have _hJord : J.OrdConnected := hJord
  have _hg : ∀ I, IsOpenSubinterval J I → IsOpenSubinterval J (g I) := hg
  let U : Set ℝ := ⋃₀ B
  have hUopen : IsOpen U := by
    exact isOpen_sUnion fun I hI => (hB I hI).2.1
  have hUJ : U ⊆ J := by
    exact sUnion_subset fun I hI => (hB I hI).2.2.2
  let R : Set ℝ := ordConnectedSection U
  have hRsub : R ⊆ U := by
    simpa only [R] using (ordConnectedSection_subset (s := U))
  let C : ℝ → Set ℝ := fun x => connectedComponentIn U x
  have hCeligible : ∀ r ∈ R, IsOpenSubinterval J (C r) := by
    intro r hr
    constructor
    · exact connectedComponentIn_nonempty_iff.mpr (hRsub hr)
    constructor
    · exact hUopen.connectedComponentIn
    constructor
    · exact isPreconnected_connectedComponentIn.ordConnected
    · exact (connectedComponentIn_subset U r).trans hUJ
  have hCbounded : ∀ r ∈ R, Bornology.IsBounded (C r) := by
    intro r hr
    exact hUbounded.subset (connectedComponentIn_subset U r)
  have hRdisjoint : R.PairwiseDisjoint C := by
    intro r hr s hs hrs
    refine disjoint_left.2 fun z hzr hzs => ?_
    have hCeq : C r = C s :=
      (connectedComponentIn_eq hzr).trans (connectedComponentIn_eq hzs).symm
    have hsCs : s ∈ C s := mem_connectedComponentIn (hRsub hs)
    have hsCr : s ∈ C r := by
      rw [hCeq]
      exact hsCs
    exact hrs (eq_of_mem_ordConnectedSection_of_uIcc_subset hr hs
      ((isPreconnected_connectedComponentIn.ordConnected.uIcc_subset
        (mem_connectedComponentIn (hRsub hr)) hsCr).trans
        (connectedComponentIn_subset U r)))
  have hRcountable : R.Countable :=
    hRdisjoint.countable_of_isOpen
      (fun r hr => hUopen.connectedComponentIn)
      (fun r hr => connectedComponentIn_nonempty_iff.mpr (hRsub hr))
  have hUeq : U = ⋃ r : R, C r := by
    apply Subset.antisymm
    · intro x hx
      let r : ℝ := ordConnectedProj U ⟨x, hx⟩
      have hrR : r ∈ R := by
        exact ⟨⟨x, hx⟩, rfl⟩
      have hxOrd : x ∈ ordConnectedComponent U r := by
        exact mem_ordConnectedComponent_ordConnectedProj U ⟨x, hx⟩
      have hxCr : x ∈ C r := by
        change x ∈ connectedComponentIn U r
        rw [connectedComponentIn_eq_ordConnectedComponent_of_mem U (hRsub hrR)]
        exact hxOrd
      exact mem_iUnion.2 ⟨⟨r, hrR⟩, hxCr⟩
    · exact iUnion_subset fun r => connectedComponentIn_subset U r
  have htarget_subset : (⋃₀ (g '' B)) ⊆ ⋃ r : R, g (C r) := by
    refine sUnion_subset fun T hT => ?_
    rcases hT with ⟨I, hIB, rfl⟩
    have hI : IsOpenSubinterval J I := hB I hIB
    obtain ⟨x, hxI⟩ := hI.1
    have hxU : x ∈ U := subset_sUnion_of_mem hIB hxI
    let r : ℝ := ordConnectedProj U ⟨x, hxU⟩
    have hrR : r ∈ R := by
      exact ⟨⟨x, hxU⟩, rfl⟩
    have hxOrd : x ∈ ordConnectedComponent U r := by
      exact mem_ordConnectedComponent_ordConnectedProj U ⟨x, hxU⟩
    have hxCr : x ∈ C r := by
      change x ∈ connectedComponentIn U r
      rw [connectedComponentIn_eq_ordConnectedComponent_of_mem U (hRsub hrR)]
      exact hxOrd
    have hCrCx : C r = C x := connectedComponentIn_eq hxCr
    have hIinCx : I ⊆ C x :=
      hI.2.2.1.isPreconnected.subset_connectedComponentIn hxI
        (subset_sUnion_of_mem hIB)
    have hIinCr : I ⊆ C r := by
      simpa only [hCrCx] using hIinCx
    exact (hmono I (C r) hI (hCeligible r hrR) hIinCr).trans
      (subset_iUnion (fun r : R => g (C r)) ⟨r, hrR⟩)
  letI : Countable R := hRcountable.to_subtype
  have hCpairwise : Pairwise (Disjoint on fun r : R => C r) := by
    intro r s hrs
    exact hRdisjoint r.property s.property (Subtype.coe_ne_coe.mpr hrs)
  have hmeasureU : volume U = ∑' r : R, volume (C r) := by
    rw [hUeq]
    exact measure_iUnion hCpairwise fun r => (hCeligible r r.property).2.1.measurableSet
  calc
    volume (⋃₀ (g '' B)) ≤ volume (⋃ r : R, g (C r)) := measure_mono htarget_subset
    _ ≤ ∑' r : R, volume (g (C r)) := measure_iUnion_le _
    _ ≤ ∑' r : R, ENNReal.ofReal kappa * volume (C r) :=
      ENNReal.tsum_le_tsum fun r =>
        (hmeasure (C r) (hCeligible r r.property) (hCbounded r r.property)).le
    _ = ENNReal.ofReal kappa * ∑' r : R, volume (C r) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal kappa * volume U := by rw [hmeasureU]

/-- The literal finite-ambient form of Krylov--Safonov Lemma 2.2. -/
theorem volume_sUnion_monotone_interval_enlargement_Ioo
    (kappa : ℝ) (hkappa : 1 < kappa) (t1 t2 : ℝ) (ht : t1 < t2)
    (B : Set (Set ℝ)) (g : Set ℝ → Set ℝ)
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo t1 t2) I)
    (hg : ∀ I, IsOpenSubinterval (Ioo t1 t2) I →
      IsOpenSubinterval (Ioo t1 t2) (g I))
    (hmeasure : ∀ I, IsOpenSubinterval (Ioo t1 t2) I →
      volume (g I) < ENNReal.ofReal kappa * volume I)
    (hmono : ∀ I₁ I₂, IsOpenSubinterval (Ioo t1 t2) I₁ →
      IsOpenSubinterval (Ioo t1 t2) I₂ → I₁ ⊆ I₂ → g I₁ ⊆ g I₂) :
    volume (⋃₀ (g '' B)) ≤ ENNReal.ofReal kappa * volume (⋃₀ B) := by
  have hIoo : IsOpenSubinterval (Ioo t1 t2) (Ioo t1 t2) :=
    ⟨nonempty_Ioo.mpr ht, isOpen_Ioo, ordConnected_Ioo, subset_rfl⟩
  apply volume_sUnion_monotone_interval_enlargement kappa hkappa (Ioo t1 t2)
    hIoo.2.1 hIoo.2.2.1 B g hB
  · exact (Metric.isBounded_Ioo t1 t2).subset
      (sUnion_subset fun I hI => (hB I hI).2.2.2)
  · exact hg
  · intro I hI _
    exact hmeasure I hI
  · exact hmono

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

/-- Non-strict local-measure companion to
`volume_sUnion_monotone_interval_enlargement`. -/
theorem volume_sUnion_monotone_interval_enlargement_of_le
    (kappa : ℝ) (hkappa : 1 < kappa)
    (J : Set ℝ) (hJopen : IsOpen J) (hJord : J.OrdConnected)
    (B : Set (Set ℝ)) (g : Set ℝ → Set ℝ)
    (hB : ∀ I ∈ B, IsOpenSubinterval J I)
    (hUbounded : Bornology.IsBounded (⋃₀ B))
    (hg : ∀ I, IsOpenSubinterval J I → IsOpenSubinterval J (g I))
    (hmeasure : ∀ I, IsOpenSubinterval J I → Bornology.IsBounded I →
      volume (g I) ≤ ENNReal.ofReal kappa * volume I)
    (hmono : ∀ I₁ I₂, IsOpenSubinterval J I₁ → IsOpenSubinterval J I₂ →
      I₁ ⊆ I₂ → g I₁ ⊆ g I₂) :
    volume (⋃₀ (g '' B)) ≤ ENNReal.ofReal kappa * volume (⋃₀ B) := by
  have _hkappa : 0 < kappa := lt_trans zero_lt_one hkappa
  have _hJopen : IsOpen J := hJopen
  have _hJord : J.OrdConnected := hJord
  have _hg : ∀ I, IsOpenSubinterval J I → IsOpenSubinterval J (g I) := hg
  let U : Set ℝ := ⋃₀ B
  have hUopen : IsOpen U := by
    exact isOpen_sUnion fun I hI => (hB I hI).2.1
  have hUJ : U ⊆ J := by
    exact sUnion_subset fun I hI => (hB I hI).2.2.2
  let R : Set ℝ := ordConnectedSection U
  have hRsub : R ⊆ U := by
    simpa only [R] using (ordConnectedSection_subset (s := U))
  let C : ℝ → Set ℝ := fun x => connectedComponentIn U x
  have hCeligible : ∀ r ∈ R, IsOpenSubinterval J (C r) := by
    intro r hr
    constructor
    · exact connectedComponentIn_nonempty_iff.mpr (hRsub hr)
    constructor
    · exact hUopen.connectedComponentIn
    constructor
    · exact isPreconnected_connectedComponentIn.ordConnected
    · exact (connectedComponentIn_subset U r).trans hUJ
  have hCbounded : ∀ r ∈ R, Bornology.IsBounded (C r) := by
    intro r hr
    exact hUbounded.subset (connectedComponentIn_subset U r)
  have hRdisjoint : R.PairwiseDisjoint C := by
    intro r hr s hs hrs
    refine disjoint_left.2 fun z hzr hzs => ?_
    have hCeq : C r = C s :=
      (connectedComponentIn_eq hzr).trans (connectedComponentIn_eq hzs).symm
    have hsCs : s ∈ C s := mem_connectedComponentIn (hRsub hs)
    have hsCr : s ∈ C r := by
      rw [hCeq]
      exact hsCs
    exact hrs (eq_of_mem_ordConnectedSection_of_uIcc_subset hr hs
      ((isPreconnected_connectedComponentIn.ordConnected.uIcc_subset
        (mem_connectedComponentIn (hRsub hr)) hsCr).trans
        (connectedComponentIn_subset U r)))
  have hRcountable : R.Countable :=
    hRdisjoint.countable_of_isOpen
      (fun r hr => hUopen.connectedComponentIn)
      (fun r hr => connectedComponentIn_nonempty_iff.mpr (hRsub hr))
  have hUeq : U = ⋃ r : R, C r := by
    apply Subset.antisymm
    · intro x hx
      let r : ℝ := ordConnectedProj U ⟨x, hx⟩
      have hrR : r ∈ R := by
        exact ⟨⟨x, hx⟩, rfl⟩
      have hxOrd : x ∈ ordConnectedComponent U r := by
        exact mem_ordConnectedComponent_ordConnectedProj U ⟨x, hx⟩
      have hxCr : x ∈ C r := by
        change x ∈ connectedComponentIn U r
        rw [connectedComponentIn_eq_ordConnectedComponent_of_mem U (hRsub hrR)]
        exact hxOrd
      exact mem_iUnion.2 ⟨⟨r, hrR⟩, hxCr⟩
    · exact iUnion_subset fun r => connectedComponentIn_subset U r
  have htarget_subset : (⋃₀ (g '' B)) ⊆ ⋃ r : R, g (C r) := by
    refine sUnion_subset fun T hT => ?_
    rcases hT with ⟨I, hIB, rfl⟩
    have hI : IsOpenSubinterval J I := hB I hIB
    obtain ⟨x, hxI⟩ := hI.1
    have hxU : x ∈ U := subset_sUnion_of_mem hIB hxI
    let r : ℝ := ordConnectedProj U ⟨x, hxU⟩
    have hrR : r ∈ R := by
      exact ⟨⟨x, hxU⟩, rfl⟩
    have hxOrd : x ∈ ordConnectedComponent U r := by
      exact mem_ordConnectedComponent_ordConnectedProj U ⟨x, hxU⟩
    have hxCr : x ∈ C r := by
      change x ∈ connectedComponentIn U r
      rw [connectedComponentIn_eq_ordConnectedComponent_of_mem U (hRsub hrR)]
      exact hxOrd
    have hCrCx : C r = C x := connectedComponentIn_eq hxCr
    have hIinCx : I ⊆ C x :=
      hI.2.2.1.isPreconnected.subset_connectedComponentIn hxI
        (subset_sUnion_of_mem hIB)
    have hIinCr : I ⊆ C r := by
      simpa only [hCrCx] using hIinCx
    exact (hmono I (C r) hI (hCeligible r hrR) hIinCr).trans
      (subset_iUnion (fun r : R => g (C r)) ⟨r, hrR⟩)
  letI : Countable R := hRcountable.to_subtype
  have hCpairwise : Pairwise (Disjoint on fun r : R => C r) := by
    intro r s hrs
    exact hRdisjoint r.property s.property (Subtype.coe_ne_coe.mpr hrs)
  have hmeasureU : volume U = ∑' r : R, volume (C r) := by
    rw [hUeq]
    exact measure_iUnion hCpairwise fun r => (hCeligible r r.property).2.1.measurableSet
  calc
    volume (⋃₀ (g '' B)) ≤ volume (⋃ r : R, g (C r)) := measure_mono htarget_subset
    _ ≤ ∑' r : R, volume (g (C r)) := measure_iUnion_le _
    _ ≤ ∑' r : R, ENNReal.ofReal kappa * volume (C r) :=
      ENNReal.tsum_le_tsum fun r =>
        hmeasure (C r) (hCeligible r r.property) (hCbounded r r.property)
    _ = ENNReal.ofReal kappa * ∑' r : R, volume (C r) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal kappa * volume U := by rw [hmeasureU]

/-- Finite-ambient non-strict local-measure companion to
`volume_sUnion_monotone_interval_enlargement_Ioo`. -/
theorem volume_sUnion_monotone_interval_enlargement_Ioo_of_le
    (kappa : ℝ) (hkappa : 1 < kappa) (t1 t2 : ℝ) (ht : t1 < t2)
    (B : Set (Set ℝ)) (g : Set ℝ → Set ℝ)
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo t1 t2) I)
    (hg : ∀ I, IsOpenSubinterval (Ioo t1 t2) I →
      IsOpenSubinterval (Ioo t1 t2) (g I))
    (hmeasure : ∀ I, IsOpenSubinterval (Ioo t1 t2) I →
      volume (g I) ≤ ENNReal.ofReal kappa * volume I)
    (hmono : ∀ I₁ I₂, IsOpenSubinterval (Ioo t1 t2) I₁ →
      IsOpenSubinterval (Ioo t1 t2) I₂ → I₁ ⊆ I₂ → g I₁ ⊆ g I₂) :
    volume (⋃₀ (g '' B)) ≤ ENNReal.ofReal kappa * volume (⋃₀ B) := by
  have hIoo : IsOpenSubinterval (Ioo t1 t2) (Ioo t1 t2) :=
    ⟨nonempty_Ioo.mpr ht, isOpen_Ioo, ordConnected_Ioo, subset_rfl⟩
  apply volume_sUnion_monotone_interval_enlargement_of_le kappa hkappa (Ioo t1 t2)
    hIoo.2.1 hIoo.2.2.1 B g hB
  · exact (Metric.isBounded_Ioo t1 t2).subset
      (sUnion_subset fun I hI => (hB I hI).2.2.2)
  · exact hg
  · intro I hI _
    exact hmeasure I hI
  · exact hmono

end HypoellipticAleksandrov.Parabolic
