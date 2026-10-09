module

public import HypoellipticAleksandrov.Parabolic.CrossVelocityWeakDerivativeCommutation
public import HypoellipticAleksandrov.Parabolic.GenericParabolicIndexArithmetic
public import HypoellipticAleksandrov.Parabolic.MixedTimeVelocityWeakDerivativeCommutation
public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndexBoundCoherence
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Generic add-two assembly for parabolic weak-derivative families

This module develops the index classification used to assemble supplied
Hessian and time-successor representatives into a coherent family whose
ambient parabolic bound `M + 2` is one larger than the supplied family's bound
`M + 1`.  The supplied Hessian and time entries lie two parabolic weights above
their source index `beta`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

namespace ParabolicDerivativeIndex

/-- An index outside the inherited layer of an add-two construction has exact
top weight. -/
private theorem weight_eq_add_two_of_not_le_add_one
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (h : ¬ alpha.1.parabolicWeight ≤ M + 1) :
    alpha.1.parabolicWeight = M + 2 := by
  omega

/-- Remove one time derivative from an index known to have positive time
order.  Its ambient bound is stated separately because the add-two assembly
uses it at the source bound `M`. -/
private def timePredecessor
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : 0 < alpha.1.timeOrder)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    ParabolicDerivativeIndex d M :=
  ⟨TimeVelocityMultiIndex.ofTimeVelocity
      (alpha.1.timeOrder - 1) alpha.1.velocity, by
    change 2 * (alpha.1.timeOrder - 1) + alpha.1.velocity.order ≤ M
    change 2 * alpha.1.timeOrder + alpha.1.velocity.order = M + 2 at hweight
    omega⟩

@[simp] private theorem timePredecessor_timeOrder
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : 0 < alpha.1.timeOrder)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    (timePredecessor alpha ht hweight).1.timeOrder =
      alpha.1.timeOrder - 1 :=
  rfl

@[simp] private theorem timePredecessor_velocity
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : 0 < alpha.1.timeOrder)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    (timePredecessor alpha ht hweight).1.velocity = alpha.1.velocity :=
  rfl

private theorem timePredecessor_weight
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : 0 < alpha.1.timeOrder)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    (timePredecessor alpha ht hweight).1.parabolicWeight = M := by
  change 2 * (alpha.1.timeOrder - 1) + alpha.1.velocity.order = M
  change 2 * alpha.1.timeOrder + alpha.1.velocity.order = M + 2 at hweight
  omega

/-- Adding the removed time derivative recovers the original bounded index.
This is the exact source-time presentation used by the top-time branch. -/
private theorem sourceTime_timePredecessor
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : 0 < alpha.1.timeOrder)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    sourceTime (L := M + 2) (by omega) (timePredecessor alpha ht hweight) = alpha := by
  apply Subtype.ext
  rw [coe_sourceTime]
  conv_rhs => rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity alpha.1]
  funext c
  rcases c with ⟨⟩ | i
  · simp [timePredecessor, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, timeCoord]
    exact Nat.sub_add_cancel (by
      change 1 ≤ alpha.1.timeOrder
      omega)
  · simp [timePredecessor, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.velocity, timeCoord, velocityCoord]

/-- A top-layer index with no time derivative is purely spatial, and its
velocity order is the full parabolic weight. -/
private theorem velocity_order_eq_of_timeOrder_eq_zero
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    alpha.1.velocity.order = M + 2 := by
  unfold TimeVelocityMultiIndex.parabolicWeight
    VelocityMultiIndex.parabolicWeight at hweight
  omega

/-- Under the induction hypothesis `1 ≤ M`, a pure-spatial top-layer index
has at least two supported velocity units. -/
private theorem two_le_velocity_order_of_top
    {d M : ℕ} (hM : 1 ≤ M)
    (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    2 ≤ alpha.1.velocity.order := by
  rw [velocity_order_eq_of_timeOrder_eq_zero alpha ht hweight]
  omega

/-- Select a coordinate carrying positive velocity order.  The positive-order
certificate is consumed before any inhabitant of `Fin d` is requested, so the
zero-dimensional case is discharged as a contradiction. -/
private noncomputable def supportedCoordinate
    {d : ℕ} (alpha : VelocityMultiIndex d) (horder : 0 < alpha.order) : Fin d := by
  classical
  have hexists : ∃ i : Fin d, 0 < alpha i := by
    rw [VelocityMultiIndex.order, Finset.sum_pos_iff_of_nonneg] at horder
    · obtain ⟨i, _, hi⟩ := horder
      exact ⟨i, hi⟩
    · exact fun _ _ => Nat.zero_le _
  exact Classical.choose hexists

private theorem supportedCoordinate_pos
    {d : ℕ} (alpha : VelocityMultiIndex d) (horder : 0 < alpha.order) :
    0 < alpha (supportedCoordinate alpha horder) := by
  classical
  exact Classical.choose_spec (show ∃ i : Fin d, 0 < alpha i from by
    rw [VelocityMultiIndex.order, Finset.sum_pos_iff_of_nonneg] at horder
    · obtain ⟨i, _, hi⟩ := horder
      exact ⟨i, hi⟩
    · exact fun _ _ => Nat.zero_le _)

/-- Decrement one certified supported velocity coordinate. -/
private def decrementVelocity {d : ℕ} (alpha : VelocityMultiIndex d) (i : Fin d) :
    VelocityMultiIndex d :=
  Function.update alpha i (alpha i - 1)

private theorem decrementVelocity_order_add_one
    {d : ℕ} (alpha : VelocityMultiIndex d) (i : Fin d) (hi : 0 < alpha i) :
    (decrementVelocity alpha i).order + 1 = alpha.order := by
  have hsum :
      (∑ j, Function.update alpha i (alpha i - 1) j) + alpha i =
        (∑ j, alpha j) + (alpha i - 1) := by
    classical
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    have horig := Finset.sum_erase_add Finset.univ alpha (Finset.mem_univ i)
    rw [Finset.sdiff_singleton_eq_erase]
    omega
  change (∑ j, Function.update alpha i (alpha i - 1) j) + 1 = ∑ j, alpha j
  omega

private theorem decrementVelocity_add_single
    {d : ℕ} (alpha : VelocityMultiIndex d) (i : Fin d) (hi : 0 < alpha i) :
    decrementVelocity alpha i + Pi.single i 1 = alpha := by
  classical
  funext k
  by_cases hki : k = i
  · subst k
    simp [decrementVelocity]
    omega
  · simp [decrementVelocity, hki]

/-- The first deterministic decrement of a pure-spatial top index. -/
private noncomputable def firstSpatialCoordinate
    {d M : ℕ} (hM : 1 ≤ M) (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) : Fin d :=
  supportedCoordinate alpha.1.velocity
    (lt_of_lt_of_le (by omega) (two_le_velocity_order_of_top hM alpha ht hweight))

/-- The second deterministic decrement is selected after the first one. -/
private noncomputable def secondSpatialCoordinate
    {d M : ℕ} (hM : 1 ≤ M) (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) : Fin d := by
  let i := firstSpatialCoordinate hM alpha ht hweight
  have hi : 0 < alpha.1.velocity i := supportedCoordinate_pos _ _
  have hfirst :
      (decrementVelocity alpha.1.velocity i).order + 1 = alpha.1.velocity.order :=
    decrementVelocity_order_add_one _ _ hi
  have hremaining : 0 < (decrementVelocity alpha.1.velocity i).order := by
    have htwo := two_le_velocity_order_of_top hM alpha ht hweight
    omega
  exact supportedCoordinate (decrementVelocity alpha.1.velocity i) hremaining

/-- Remove the two deterministically selected velocity derivatives from a
pure-spatial exact-top index. -/
private noncomputable def pureVelocityPredecessor
    {d M : ℕ} (hM : 1 ≤ M) (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    ParabolicDerivativeIndex d M := by
  let i := firstSpatialCoordinate hM alpha ht hweight
  let afterI := decrementVelocity alpha.1.velocity i
  let j := secondSpatialCoordinate hM alpha ht hweight
  let afterJ := decrementVelocity afterI j
  refine ⟨TimeVelocityMultiIndex.ofTimeVelocity 0 afterJ, ?_⟩
  have hi : 0 < alpha.1.velocity i := supportedCoordinate_pos _ _
  have hI : afterI.order + 1 = alpha.1.velocity.order :=
    decrementVelocity_order_add_one _ _ hi
  have hremaining : 0 < afterI.order := by
    have htwo := two_le_velocity_order_of_top hM alpha ht hweight
    omega
  have hj : 0 < afterI j := supportedCoordinate_pos _ hremaining
  have hJ : afterJ.order + 1 = afterI.order :=
    decrementVelocity_order_add_one _ _ hj
  change 2 * 0 + afterJ.order ≤ M
  have htop := velocity_order_eq_of_timeOrder_eq_zero alpha ht hweight
  omega

private theorem pureVelocityPredecessor_weight
    {d M : ℕ} (hM : 1 ≤ M) (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    (pureVelocityPredecessor hM alpha ht hweight).1.parabolicWeight = M := by
  let i := firstSpatialCoordinate hM alpha ht hweight
  let afterI := decrementVelocity alpha.1.velocity i
  let j := secondSpatialCoordinate hM alpha ht hweight
  let afterJ := decrementVelocity afterI j
  have hi : 0 < alpha.1.velocity i := supportedCoordinate_pos _ _
  have hI : afterI.order + 1 = alpha.1.velocity.order :=
    decrementVelocity_order_add_one _ _ hi
  have hremaining : 0 < afterI.order := by
    have htwo := two_le_velocity_order_of_top hM alpha ht hweight
    omega
  have hj : 0 < afterI j := supportedCoordinate_pos _ hremaining
  have hJ : afterJ.order + 1 = afterI.order :=
    decrementVelocity_order_add_one _ _ hj
  simp only [pureVelocityPredecessor, TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity,
    VelocityMultiIndex.parabolicWeight]
  norm_num
  change afterJ.order = M
  have htop := velocity_order_eq_of_timeOrder_eq_zero alpha ht hweight
  omega

/-- Adding back the second-selected and then first-selected velocity units
recovers the original pure-spatial top index, with the public `j`, `i` order. -/
private theorem sourceVelocityTwo_pureVelocityPredecessor
    {d M : ℕ} (hM : 1 ≤ M) (alpha : ParabolicDerivativeIndex d (M + 2))
    (ht : alpha.1.timeOrder = 0)
    (hweight : alpha.1.parabolicWeight = M + 2) :
    sourceVelocityTwo (L := M + 2) (by omega)
      (pureVelocityPredecessor hM alpha ht hweight)
      (secondSpatialCoordinate hM alpha ht hweight)
      (firstSpatialCoordinate hM alpha ht hweight) = alpha := by
  classical
  apply Subtype.ext
  rw [coe_sourceVelocityTwo]
  conv_rhs => rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity alpha.1]
  funext c
  rcases c with ⟨⟩ | k
  · simp [pureVelocityPredecessor, ht, TimeVelocityMultiIndex.ofTimeVelocity,
      velocityCoord]
  · let i := firstSpatialCoordinate hM alpha ht hweight
    let afterI := decrementVelocity alpha.1.velocity i
    let j := secondSpatialCoordinate hM alpha ht hweight
    have hi : 0 < alpha.1.velocity i := supportedCoordinate_pos _ _
    have htop := velocity_order_eq_of_timeOrder_eq_zero alpha ht hweight
    have hremaining : 0 < afterI.order := by
      have hI := decrementVelocity_order_add_one alpha.1.velocity i hi
      change afterI.order + 1 = alpha.1.velocity.order at hI
      have htwo := two_le_velocity_order_of_top hM alpha ht hweight
      omega
    have hj : 0 < afterI j := supportedCoordinate_pos _ hremaining
    have hJ := congrFun (decrementVelocity_add_single afterI j hj) k
    have hI := congrFun (decrementVelocity_add_single alpha.1.velocity i hi) k
    simp only [pureVelocityPredecessor, TimeVelocityMultiIndex.ofTimeVelocity,
      Pi.add_apply, velocityCoord, Pi.single_apply, Sum.inr.injEq]
    simp only [Pi.add_apply, Pi.single_apply] at hJ hI
    dsimp only [i, j, afterI] at hJ hI ⊢
    omega

/-- The selected representative for the add-two family: inherited entries are
literal, while exact-top entries use the selected time or pure-spatial
predecessor. -/
private noncomputable def canonicalRepresentative
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (alpha : ParabolicDerivativeIndex d (M + 2)) : TimeVelocity d → ℝ :=
  if hle : alpha.1.parabolicWeight ≤ M + 1 then
    D.representative (restrictLE alpha hle)
  else if ht : 0 < alpha.1.timeOrder then
    W (timePredecessor alpha ht (weight_eq_add_two_of_not_le_add_one alpha hle))
  else
    let hzero : alpha.1.timeOrder = 0 := Nat.eq_zero_of_not_pos ht
    fun z => H z
      (pureVelocityPredecessor hM alpha hzero
        (weight_eq_add_two_of_not_le_add_one alpha hle))
      (secondSpatialCoordinate hM alpha hzero
        (weight_eq_add_two_of_not_le_add_one alpha hle))
      (firstSpatialCoordinate hM alpha hzero
        (weight_eq_add_two_of_not_le_add_one alpha hle))

private theorem canonicalRepresentative_inherited
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (alpha : ParabolicDerivativeIndex d (M + 1)) :
    canonicalRepresentative hM D H W (castLE (by omega) alpha) =
      D.representative alpha := by
  simp only [canonicalRepresentative]
  have hle : (castLE (by omega) alpha : ParabolicDerivativeIndex d (M + 2)).1.parabolicWeight ≤
      M + 1 := alpha.2
  rw [dif_pos hle]
  rfl

private theorem canonicalRepresentative_time_top
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (alpha : ParabolicDerivativeIndex d (M + 2))
    (hnot : ¬ alpha.1.parabolicWeight ≤ M + 1)
    (ht : 0 < alpha.1.timeOrder) :
    canonicalRepresentative hM D H W alpha =
      W (timePredecessor alpha ht
        (weight_eq_add_two_of_not_le_add_one alpha hnot)) := by
  simp only [canonicalRepresentative]
  rw [dif_neg hnot, dif_pos ht]

private theorem canonicalRepresentative_pure_spatial_top
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (alpha : ParabolicDerivativeIndex d (M + 2))
    (hnot : ¬ alpha.1.parabolicWeight ≤ M + 1)
    (ht : alpha.1.timeOrder = 0) :
    canonicalRepresentative hM D H W alpha =
      fun z => H z
        (pureVelocityPredecessor hM alpha ht
          (weight_eq_add_two_of_not_le_add_one alpha hnot))
        (secondSpatialCoordinate hM alpha ht
          (weight_eq_add_two_of_not_le_add_one alpha hnot))
        (firstSpatialCoordinate hM alpha ht
          (weight_eq_add_two_of_not_le_add_one alpha hnot)) := by
  simp only [canonicalRepresentative]
  rw [dif_neg hnot, dif_neg (not_lt.mpr (Nat.le_of_eq ht))]

private theorem canonicalRepresentative_memLp
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 2)) :
    ParabolicMemLpOn V 2 (canonicalRepresentative hM D H W alpha) := by
  by_cases hle : alpha.1.parabolicWeight ≤ M + 1
  · rw [canonicalRepresentative, dif_pos hle]
    exact D.memLp _
  · by_cases ht : 0 < alpha.1.timeOrder
    · rw [canonicalRepresentative, dif_neg hle, dif_pos ht]
      exact hWmem _
    · rw [canonicalRepresentative, dif_neg hle, dif_neg ht]
      exact hHmem _ _ _

private theorem canonicalRepresentative_zero_ae
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ) :
    canonicalRepresentative hM D H W (zero d (M + 2))
      =ᵐ[timeVelocityVolumeOn V] u := by
  have hz : zero d (M + 2) = castLE (by omega) (zero d (M + 1)) := rfl
  rw [hz, canonicalRepresentative_inherited]
  exact D.zero_ae

private theorem canonicalRepresentative_hasWeakTimeSucc
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 2))
    (hsucc : alpha.1.parabolicWeight + 2 ≤ M + 2) :
    HasWeakTimeDerivOn V (canonicalRepresentative hM D H W alpha)
      (canonicalRepresentative hM D H W (timeSucc alpha hsucc)) := by
  have halpha : alpha.1.parabolicWeight ≤ M := by omega
  have halpha1 : alpha.1.parabolicWeight ≤ M + 1 := by omega
  rw [canonicalRepresentative, dif_pos halpha1]
  by_cases htarget : (timeSucc alpha hsucc).1.parabolicWeight ≤ M + 1
  · rw [canonicalRepresentative, dif_pos htarget]
    have hold : (restrictLE alpha halpha1).1.parabolicWeight + 2 ≤ M + 1 := by
      rw [coe_restrictLE]
      rw [parabolicWeight_timeSucc] at htarget
      exact htarget
    have heq : restrictLE (timeSucc alpha hsucc) htarget =
        timeSucc (restrictLE alpha halpha1) hold := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact D.hasWeakTimeSucc _ hold
  · have htime : 0 < (timeSucc alpha hsucc).1.timeOrder := by
      rw [timeOrder_timeSucc]
      omega
    rw [canonicalRepresentative_time_top hM D H W _ htarget htime]
    let beta : ParabolicDerivativeIndex d M := restrictLE alpha halpha
    have hpred : timePredecessor (timeSucc alpha hsucc) htime
          (weight_eq_add_two_of_not_le_add_one _ htarget) = beta := by
      apply Subtype.ext
      rw [coe_restrictLE]
      conv_rhs => rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity alpha.1]
      funext c
      rcases c with ⟨⟩ | i
      · simp [timePredecessor, timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, timeCoord]
      · simp [timePredecessor, timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.velocity, velocityCoord]
    rw [hpred]
    exact hWweak beta

/-- Coherence of a velocity edge whose target remains in the inherited
layer.  The exact-top collision branches are handled separately. -/
private theorem canonicalRepresentative_hasWeakVelocitySucc_inherited
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (alpha : ParabolicDerivativeIndex d (M + 2)) (i : Fin d)
    (hsucc : alpha.1.parabolicWeight + 1 ≤ M + 2)
    (htarget : (velocitySucc alpha i hsucc).1.parabolicWeight ≤ M + 1) :
    HasWeakVelocityPartialDerivOn V i
      (canonicalRepresentative hM D H W alpha)
      (canonicalRepresentative hM D H W (velocitySucc alpha i hsucc)) := by
  rw [parabolicWeight_velocitySucc] at htarget
  have halpha : alpha.1.parabolicWeight ≤ M + 1 := by omega
  rw [canonicalRepresentative, dif_pos halpha,
    canonicalRepresentative, dif_pos (by
      rw [parabolicWeight_velocitySucc]
      exact htarget)]
  have hold : (restrictLE alpha halpha).1.parabolicWeight + 1 ≤ M + 1 := by
    rw [coe_restrictLE]
    exact htarget
  have heq : restrictLE (velocitySucc alpha i hsucc) (by
        rw [parabolicWeight_velocitySucc]
        exact htarget) =
      velocitySucc (restrictLE alpha halpha) i hold := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact D.hasWeakVelocitySucc _ i hold

private theorem coe_velocitySucc_eq_add_single
    {d L : ℕ} (alpha : ParabolicDerivativeIndex d L) (i : Fin d)
    (h : alpha.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc alpha i h).1 = alpha.1 + Pi.single (velocityCoord i) 1 := by
  classical
  funext c
  rcases c with ⟨⟩ | ell
  · simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, timeCoord, velocityCoord]
  · by_cases hell : ell = i
    · subst ell
      simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.velocity, velocityCoord]
    · simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.velocity, velocityCoord, hell]

/-- When two distinct last velocity directions present the same pure-spatial
top index, removing the canonical final direction gives a common predecessor
for the crossed-derivative argument. -/
private theorem exists_pureSpatial_velocityCommonRoot
    {d M : ℕ} (alpha : ParabolicDerivativeIndex d (M + 2))
    (beta : ParabolicDerivativeIndex d M) (j i k : Fin d)
    (hbetaWeight : beta.1.parabolicWeight = M)
    (hsucc : alpha.1.parabolicWeight + 1 ≤ M + 2)
    (hreconstruct : velocitySucc alpha k hsucc =
      sourceVelocityTwo (L := M + 2) (by omega) beta j i)
    (hki : k ≠ i) :
    ∃ rho : ParabolicDerivativeIndex d M,
      rho.1 + Pi.single (velocityCoord i) 1 = alpha.1 ∧
        rho.1 + Pi.single (velocityCoord k) 1 =
          beta.1 + Pi.single (velocityCoord j) 1 := by
  classical
  have hsuccRaw := coe_velocitySucc_eq_add_single alpha k hsucc
  have hraw : alpha.1 + Pi.single (velocityCoord k) 1 =
      beta.1 + Pi.single (velocityCoord j) 1 +
        Pi.single (velocityCoord i) 1 := by
    have := congrArg Subtype.val hreconstruct
    rw [hsuccRaw] at this
    simpa only [coe_sourceVelocityTwo] using this
  have hpos : 0 < alpha.1.velocity i := by
    have hi := congrFun hraw (velocityCoord i)
    have hsingleK :
        (Pi.single (velocityCoord k) 1 : TimeVelocityCoord d → ℕ) (velocityCoord i) = 0 := by
      rw [Pi.single_eq_of_ne]
      exact fun hik => hki (Sum.inr.inj hik.symm)
    have hsingleI :
        (Pi.single (velocityCoord i) 1 : TimeVelocityCoord d → ℕ) (velocityCoord i) = 1 := by
      exact Pi.single_eq_same _ _
    simp only [Pi.add_apply] at hi
    rw [hsingleK, hsingleI] at hi
    simp only [add_zero] at hi
    change alpha.1.velocity i =
      beta.1.velocity i +
        (Pi.single (velocityCoord j) 1 : TimeVelocityCoord d → ℕ) (velocityCoord i) + 1 at hi
    omega
  let rhoRaw : TimeVelocityMultiIndex d :=
    TimeVelocityMultiIndex.ofTimeVelocity alpha.1.timeOrder
      (decrementVelocity alpha.1.velocity i)
  have hrhoWeight : rhoRaw.parabolicWeight ≤ M := by
    have hdec := decrementVelocity_order_add_one alpha.1.velocity i hpos
    have halphaWeight : alpha.1.parabolicWeight = M + 1 := by
      have hw := congrArg TimeVelocityMultiIndex.parabolicWeight hraw
      simp only [TimeVelocityMultiIndex.parabolicWeight_add,
        TimeVelocityMultiIndex.parabolicWeight_single_velocity] at hw
      rw [hbetaWeight] at hw
      omega
    dsimp only [rhoRaw]
    simp only [TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity,
      VelocityMultiIndex.parabolicWeight]
    unfold TimeVelocityMultiIndex.parabolicWeight
      VelocityMultiIndex.parabolicWeight at halphaWeight
    omega
  let rho : ParabolicDerivativeIndex d M := ⟨rhoRaw, hrhoWeight⟩
  have hrhoAddI : rho.1 + Pi.single (velocityCoord i) 1 = alpha.1 := by
    funext c
    rcases c with ⟨⟩ | ell
    · change alpha.1.timeOrder + 0 = alpha.1.timeOrder
      omega
    · have h := congrFun (decrementVelocity_add_single alpha.1.velocity i hpos) ell
      simpa [rho, rhoRaw, TimeVelocityMultiIndex.ofTimeVelocity,
        velocityCoord, Pi.single_apply, TimeVelocityMultiIndex.velocity] using h
  have hrhoAddK : rho.1 + Pi.single (velocityCoord k) 1 =
      beta.1 + Pi.single (velocityCoord j) 1 := by
    apply add_right_cancel (b := Pi.single (velocityCoord i) 1)
    calc
      (rho.1 + Pi.single (velocityCoord k) 1) +
          Pi.single (velocityCoord i) 1 =
          (rho.1 + Pi.single (velocityCoord i) 1) +
            Pi.single (velocityCoord k) 1 := by
              simp only [add_assoc]
              rw [add_comm (Pi.single (velocityCoord k) 1)
                (Pi.single (velocityCoord i) 1)]
      _ = alpha.1 + Pi.single (velocityCoord k) 1 := by rw [hrhoAddI]
      _ = (beta.1 + Pi.single (velocityCoord j) 1) +
          Pi.single (velocityCoord i) 1 := hraw
  exact ⟨rho, hrhoAddI, hrhoAddK⟩

/-- Coherence of a velocity edge into an exact top index carrying a time
derivative.  Both presentations descend from the index obtained by removing
that time derivative before adjoining the displayed velocity coordinate. -/
private theorem canonicalRepresentative_hasWeakVelocitySucc_time_top
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 2)) (i : Fin d)
    (hsucc : alpha.1.parabolicWeight + 1 ≤ M + 2)
    (htarget : ¬ (velocitySucc alpha i hsucc).1.parabolicWeight ≤ M + 1)
    (htime : 0 < (velocitySucc alpha i hsucc).1.timeOrder) :
    HasWeakVelocityPartialDerivOn V i
      (canonicalRepresentative hM D H W alpha)
      (canonicalRepresentative hM D H W (velocitySucc alpha i hsucc)) := by
  have halphaWeight : alpha.1.parabolicWeight = M + 1 := by
    rw [parabolicWeight_velocitySucc] at htarget
    omega
  have halphaLe : alpha.1.parabolicWeight ≤ M + 1 := by omega
  have halphaTime : 0 < alpha.1.timeOrder := by
    rw [timeOrder_velocitySucc] at htime
    exact htime
  let gamma : ParabolicDerivativeIndex d (M + 1) :=
    ⟨TimeVelocityMultiIndex.ofTimeVelocity
      (alpha.1.timeOrder - 1) alpha.1.velocity, by
      change 2 * (alpha.1.timeOrder - 1) + alpha.1.velocity.order ≤ M + 1
      change 2 * alpha.1.timeOrder + alpha.1.velocity.order = M + 1 at halphaWeight
      omega⟩
  have hgammaTime : gamma.1.parabolicWeight + 2 ≤ M + 1 := by
    dsimp only [gamma]
    simp only [TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity,
      VelocityMultiIndex.parabolicWeight]
    change 2 * alpha.1.timeOrder + alpha.1.velocity.order = M + 1 at halphaWeight
    omega
  have hgammaVelocity : gamma.1.parabolicWeight + 1 ≤ M + 1 := by omega
  let beta : ParabolicDerivativeIndex d M :=
    restrictLE (velocitySucc gamma i hgammaVelocity) (by
      rw [parabolicWeight_velocitySucc]
      omega)
  have htimeLeg : HasWeakTimeDerivOn V (D.representative gamma)
      (D.representative (restrictLE alpha halphaLe)) := by
    have h := D.hasWeakTimeSucc gamma hgammaTime
    have heq : timeSucc gamma hgammaTime = restrictLE alpha halphaLe := by
      apply Subtype.ext
      conv_rhs => rw [coe_restrictLE,
        ← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity alpha.1]
      funext c
      rcases c with ⟨⟩ | k
      · simp [gamma, timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.timeOrder, timeCoord]
        exact Nat.sub_add_cancel halphaTime
      · simp [gamma, timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
          TimeVelocityMultiIndex.velocity, velocityCoord]
    rwa [heq] at h
  have hvelocityLeg : HasWeakVelocityPartialDerivOn V i
      (D.representative gamma)
      (D.representative (castLE (Nat.le_succ M) beta)) := by
    have h := D.hasWeakVelocitySucc gamma i hgammaVelocity
    have heq : velocitySucc gamma i hgammaVelocity =
        castLE (Nat.le_succ M) beta := by
      apply Subtype.ext
      rfl
    rwa [heq] at h
  have hmixed : HasWeakVelocityPartialDerivOn V i
      (D.representative (restrictLE alpha halphaLe)) (W beta) :=
    hasWeakVelocityPartialDerivOn_of_hasWeakTimeDerivOn_velocityDeriv i
      htimeLeg hvelocityLeg (hWweak beta)
  rw [canonicalRepresentative, dif_pos halphaLe,
    canonicalRepresentative_time_top hM D H W _ htarget htime]
  have hpred : timePredecessor (velocitySucc alpha i hsucc) htime
        (weight_eq_add_two_of_not_le_add_one _ htarget) = beta := by
    apply Subtype.ext
    dsimp only [beta, gamma]
    rw [coe_restrictLE]
    funext c
    rcases c with ⟨⟩ | k
    · simp [timePredecessor, velocitySucc,
        TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.timeOrder, timeCoord]
    · simp [timePredecessor, velocitySucc,
        TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.velocity, velocityCoord]
  rwa [hpred]

/-- Coherence of a velocity edge into a pure-spatial exact-top index.  A
noncanonical final direction is reconciled with the canonical Hessian entry by
commuting the two weak velocity derivatives from their common predecessor. -/
private theorem canonicalRepresentative_hasWeakVelocitySucc_pure_spatial_top
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (hVopen : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)) z)
      (fun z => H z beta j i))
    (alpha : ParabolicDerivativeIndex d (M + 2)) (k : Fin d)
    (hsucc : alpha.1.parabolicWeight + 1 ≤ M + 2)
    (htarget : ¬ (velocitySucc alpha k hsucc).1.parabolicWeight ≤ M + 1)
    (htime : (velocitySucc alpha k hsucc).1.timeOrder = 0) :
    HasWeakVelocityPartialDerivOn V k
      (canonicalRepresentative hM D H W alpha)
      (canonicalRepresentative hM D H W (velocitySucc alpha k hsucc)) := by
  let tau := velocitySucc alpha k hsucc
  have htauWeight : tau.1.parabolicWeight = M + 2 :=
    weight_eq_add_two_of_not_le_add_one tau htarget
  have halphaWeight : alpha.1.parabolicWeight = M + 1 := by
    dsimp only [tau] at htauWeight
    rw [parabolicWeight_velocitySucc] at htauWeight
    omega
  have halphaLe : alpha.1.parabolicWeight ≤ M + 1 := by omega
  have htauZero : tau.1.timeOrder = 0 := htime
  let beta := pureVelocityPredecessor hM tau htauZero htauWeight
  let j := secondSpatialCoordinate hM tau htauZero htauWeight
  let i := firstSpatialCoordinate hM tau htauZero htauWeight
  have hbetaWeight : beta.1.parabolicWeight = M :=
    pureVelocityPredecessor_weight hM tau htauZero htauWeight
  have hreconstruct : tau =
      sourceVelocityTwo (L := M + 2) (by omega) beta j i :=
    (sourceVelocityTwo_pureVelocityPredecessor hM tau htauZero htauWeight).symm
  rw [canonicalRepresentative, dif_pos halphaLe,
    canonicalRepresentative_pure_spatial_top hM D H W tau htarget htauZero]
  by_cases hki : k = i
  ·
    have hsource : restrictLE alpha halphaLe =
        velocitySucc (castLE (Nat.le_succ M) beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega) := by
      apply Subtype.ext
      have hraw := congrArg Subtype.val hreconstruct
      rw [coe_velocitySucc_eq_add_single, coe_sourceVelocityTwo, hki] at hraw
      rw [coe_restrictLE, coe_velocitySucc_eq_add_single]
      exact add_right_cancel hraw
    rw [hsource]
    simpa only [hki] using hHweak beta j i
  · obtain ⟨rho, hrhoI, hrhoK⟩ :=
      exists_pureSpatial_velocityCommonRoot alpha beta j i k hbetaWeight
        hsucc hreconstruct hki
    have hrhoIIndex :
        velocitySucc (castLE (Nat.le_succ M) rho) i (by
          change rho.1.parabolicWeight + 1 ≤ M + 1
          omega) =
          restrictLE alpha halphaLe := by
      apply Subtype.ext
      rw [coe_velocitySucc_eq_add_single, coe_restrictLE, coe_castLE]
      exact hrhoI
    have hrhoKIndex :
        velocitySucc (castLE (Nat.le_succ M) rho) k (by
          change rho.1.parabolicWeight + 1 ≤ M + 1
          omega) =
          velocitySucc (castLE (Nat.le_succ M) beta) j (by
            change beta.1.parabolicWeight + 1 ≤ M + 1
            omega) := by
      apply Subtype.ext
      rw [coe_velocitySucc_eq_add_single, coe_velocitySucc_eq_add_single,
        coe_castLE, coe_castLE]
      exact hrhoK
    have hui := D.hasWeakVelocitySucc (castLE (Nat.le_succ M) rho) i (by
      change rho.1.parabolicWeight + 1 ≤ M + 1
      omega)
    have huk := D.hasWeakVelocitySucc (castLE (Nat.le_succ M) rho) k (by
      change rho.1.parabolicWeight + 1 ≤ M + 1
      omega)
    have hcross : (fun z => H z rho i k) =ᵐ[timeVelocityVolumeOn V]
        (fun z => H z beta j i) :=
      HasWeakVelocityPartialDerivOn.cross_ae_eq_of_memLp hVopen i k
        (D.representative (castLE (Nat.le_succ M) rho))
        (D.representative (velocitySucc (castLE (Nat.le_succ M) rho) i (by
          change rho.1.parabolicWeight + 1 ≤ M + 1
          omega)))
        (D.representative (velocitySucc (castLE (Nat.le_succ M) rho) k (by
          change rho.1.parabolicWeight + 1 ≤ M + 1
          omega)))
        (fun z => H z rho i k) (fun z => H z beta j i)
        (hHmem rho i k) (hHmem beta j i) hui huk
        (hHweak rho i k) (by simpa only [hrhoKIndex] using hHweak beta j i)
    have halt := hHweak rho i k
    rw [hrhoIIndex] at halt
    exact halt.congr_ae (Filter.EventuallyEq.rfl) hcross

private theorem canonicalRepresentative_hasWeakVelocitySucc
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (hVopen : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)) z)
      (fun z => H z beta j i))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 2)) (i : Fin d)
    (hsucc : alpha.1.parabolicWeight + 1 ≤ M + 2) :
    HasWeakVelocityPartialDerivOn V i
      (canonicalRepresentative hM D H W alpha)
      (canonicalRepresentative hM D H W (velocitySucc alpha i hsucc)) := by
  by_cases htarget :
      (velocitySucc alpha i hsucc).1.parabolicWeight ≤ M + 1
  · exact canonicalRepresentative_hasWeakVelocitySucc_inherited
      hM D H W alpha i hsucc htarget
  · by_cases htime : 0 < (velocitySucc alpha i hsucc).1.timeOrder
    · exact canonicalRepresentative_hasWeakVelocitySucc_time_top
        hM D H W hWweak alpha i hsucc htarget htime
    · exact canonicalRepresentative_hasWeakVelocitySucc_pure_spatial_top
        hM hVopen D H W hHmem hHweak alpha i hsucc htarget
          (Nat.eq_zero_of_not_pos htime)

/-- The coherent add-two family assembled from the inherited family, supplied
Hessian representatives, and supplied time-successor representatives. -/
private noncomputable def canonicalFamily
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (hVopen : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta)) :
    ParabolicWeakDerivativeFamily d (M + 2) V u where
  representative := canonicalRepresentative hM D H W
  memLp := canonicalRepresentative_memLp hM D H W hHmem hWmem
  zero_ae := canonicalRepresentative_zero_ae hM D H W
  hasWeakTimeSucc := canonicalRepresentative_hasWeakTimeSucc hM D H W hWweak
  hasWeakVelocitySucc := canonicalRepresentative_hasWeakVelocitySucc
    hM hVopen D H W hHmem hHweak hWweak

@[simp] private theorem canonicalFamily_representative
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (hVopen : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 2)) :
    (canonicalFamily hM hVopen D H W hHmem hHweak hWmem hWweak).representative alpha =
      canonicalRepresentative hM D H W alpha := rfl

private theorem canonicalFamily_representative_inherited
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (hVopen : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          change beta.1.parabolicWeight + 1 ≤ M + 1
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 1)) :
    (canonicalFamily hM hVopen D H W hHmem hHweak hWmem hWweak).representative
        (castLE (by omega) alpha) = D.representative alpha := by
  exact canonicalRepresentative_inherited hM D H W alpha

private theorem canonicalFamily_representative_sourceTime_ae
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hV : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          rw [coe_castLE]
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (beta : ParabolicDerivativeIndex d M) :
    (canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak).representative
        (sourceTime (L := M + 2) (by omega) beta) =ᵐ[timeVelocityVolumeOn V] W beta := by
  let F := canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak
  let alpha := castLE (by omega : M + 1 ≤ M + 2) (castLE (Nat.le_succ M) beta)
  have htarget : timeSucc alpha (by
      dsimp only [alpha]
      rw [coe_castLE, coe_castLE]
      omega) = sourceTime (L := M + 2) (by omega) beta := by
    apply Subtype.ext
    rfl
  have hfirst : HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z)
      (F.representative (sourceTime (L := M + 2) (by omega) beta)) := by
    have h := F.hasWeakTimeSucc alpha (by
      dsimp only [alpha]
      rw [coe_castLE, coe_castLE]
      omega)
    dsimp only [alpha] at h
    rw [canonicalFamily_representative_inherited, htarget] at h
    exact h
  exact HasWeakTimeDerivOn.ae_eq_of_memLp hV (by norm_num)
    (F.memLp _) (hWmem beta) hfirst (hWweak beta)

private theorem canonicalFamily_representative_sourceVelocityTwo_ae
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hV : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          rw [coe_castLE]
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (beta : ParabolicDerivativeIndex d M) (j i : Fin d) :
    (canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak).representative
        (sourceVelocityTwo (L := M + 2) (by omega) beta j i)
      =ᵐ[timeVelocityVolumeOn V] fun z => H z beta j i := by
  let F := canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak
  let gamma := velocitySucc (castLE (Nat.le_succ M) beta) j (by
    rw [coe_castLE]
    omega)
  have htarget : velocitySucc (castLE (by omega : M + 1 ≤ M + 2) gamma) i (by
      rw [coe_castLE]
      omega) =
      sourceVelocityTwo (L := M + 2) (by omega) beta j i := by
    apply Subtype.ext
    rw [coe_velocitySucc_eq_add_single, coe_castLE, coe_sourceVelocityTwo]
    dsimp only [gamma]
    rw [coe_velocitySucc_eq_add_single, coe_castLE]
  have hfirst : HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative gamma z)
      (F.representative (sourceVelocityTwo (L := M + 2) (by omega) beta j i)) := by
    have h := F.hasWeakVelocitySucc
      (castLE (by omega : M + 1 ≤ M + 2) gamma) i (by
        rw [coe_castLE]
        omega)
    rw [canonicalFamily_representative_inherited, htarget] at h
    exact h
  exact HasWeakVelocityPartialDerivOn.ae_eq_of_memLp hV (by norm_num)
    (F.memLp _) (hHmem beta j i) hfirst (hHweak beta j i)

private theorem canonicalFamily_component_sq_le_total
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hV : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          rw [coe_castLE]
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta))
    (alpha : ParabolicDerivativeIndex d (M + 2)) :
    (ENNReal.toReal (eLpNorm
      ((canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak).representative alpha)
      2 (timeVelocityVolumeOn V))) ^ 2 ≤
      ParabolicWeakDerivativeFamily.squaredL2Norm D +
        (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d, ∑ i : Fin d,
          (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
            (timeVelocityVolumeOn V))) ^ 2) +
        ∑ beta : ParabolicDerivativeIndex d M,
          (ENNReal.toReal (eLpNorm (W beta) 2 (timeVelocityVolumeOn V))) ^ 2 := by
  by_cases hle : alpha.1.parabolicWeight ≤ M + 1
  · let beta : ParabolicDerivativeIndex d (M + 1) := restrictLE alpha hle
    rw [canonicalFamily_representative, canonicalRepresentative, dif_pos hle]
    exact (ParabolicWeakDerivativeFamily.component_sq_le_squaredL2Norm D beta).trans
      ((le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)))
  · by_cases ht : 0 < alpha.1.timeOrder
    · rw [canonicalFamily_representative,
        canonicalRepresentative_time_top hM D H W alpha hle ht]
      have hsingle := Finset.single_le_sum (fun beta _ => sq_nonneg
        (ENNReal.toReal (eLpNorm (W beta) 2 (timeVelocityVolumeOn V))))
        (Finset.mem_univ (timePredecessor alpha ht
          (weight_eq_add_two_of_not_le_add_one alpha hle)))
      exact hsingle.trans (le_add_of_nonneg_left (add_nonneg
        (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _)))
    · have htzero : alpha.1.timeOrder = 0 := Nat.eq_zero_of_not_pos ht
      rw [canonicalFamily_representative,
        canonicalRepresentative_pure_spatial_top hM D H W alpha hle htzero]
      let beta := pureVelocityPredecessor hM alpha htzero
        (weight_eq_add_two_of_not_le_add_one alpha hle)
      let j := secondSpatialCoordinate hM alpha htzero
        (weight_eq_add_two_of_not_le_add_one alpha hle)
      let i := firstSpatialCoordinate hM alpha htzero
        (weight_eq_add_two_of_not_le_add_one alpha hle)
      have hi := Finset.single_le_sum (fun i _ => sq_nonneg
        (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
          (timeVelocityVolumeOn V)))) (Finset.mem_univ i)
      have hj := Finset.single_le_sum (s := Finset.univ)
        (fun j _ => Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg
        (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
          (timeVelocityVolumeOn V)))) (Finset.mem_univ j)
      have hbeta := Finset.single_le_sum (s := Finset.univ)
        (fun beta _ => Finset.sum_nonneg (s := Finset.univ) fun j _ =>
        Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg
          (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
            (timeVelocityVolumeOn V)))) (Finset.mem_univ beta)
      exact (hi.trans (hj.trans hbeta)).trans
        ((le_add_of_nonneg_left
          (ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D)).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

private theorem canonicalFamily_squaredL2Norm_le
    {d M : ℕ} (hM : 1 ≤ M) {V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hV : IsOpen V)
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2 (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z => D.representative
        (velocitySucc (castLE (Nat.le_succ M) beta) j (by
          rw [coe_castLE]
          omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative (castLE (Nat.le_succ M) beta) z) (W beta)) :
    ParabolicWeakDerivativeFamily.squaredL2Norm
      (canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak) ≤
      (Fintype.card (ParabolicDerivativeIndex d (M + 2)) : ℝ) *
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d, ∑ i : Fin d,
            (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
              (timeVelocityVolumeOn V))) ^ 2) +
          ∑ beta : ParabolicDerivativeIndex d M,
            (ENNReal.toReal (eLpNorm (W beta) 2 (timeVelocityVolumeOn V))) ^ 2) := by
  change (∑ alpha : ParabolicDerivativeIndex d (M + 2),
    (ENNReal.toReal (eLpNorm
      ((canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak).representative alpha)
      2 (timeVelocityVolumeOn V))) ^ 2) ≤ _
  calc
    _ ≤ ∑ _alpha : ParabolicDerivativeIndex d (M + 2),
        (ParabolicWeakDerivativeFamily.squaredL2Norm D +
          (∑ beta : ParabolicDerivativeIndex d M, ∑ j : Fin d, ∑ i : Fin d,
            (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
              (timeVelocityVolumeOn V))) ^ 2) +
          ∑ beta : ParabolicDerivativeIndex d M,
            (ENNReal.toReal (eLpNorm (W beta) 2 (timeVelocityVolumeOn V))) ^ 2) :=
      Finset.sum_le_sum fun alpha _ => canonicalFamily_component_sq_le_total
        hM hV D H W hHmem hHweak hWmem hWweak alpha
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A coherent weak family extends its ambient parabolic bound from `M + 1`
to `M + 2` using supplied representatives two weights above each `beta`. -/
theorem exists_parabolicWeakDerivativeFamily_add_two_of_hessian_timeSuccessors
    (d M : ℕ) (hM : 1 ≤ M)
    {V : Set (TimeVelocity d)} (hV : IsOpen V)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2
      (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z =>
        D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) j
            (by
              change beta.1.parabolicWeight + 1 ≤ M + 1
              omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z)
      (W beta)) :
    ∃ Dnext : ParabolicWeakDerivativeFamily d (M + 2) V u,
      (∀ alpha : ParabolicDerivativeIndex d (M + 1),
        Dnext.representative
          (ParabolicDerivativeIndex.castLE (by omega) alpha) =
            D.representative alpha) ∧
      (∀ beta : ParabolicDerivativeIndex d M,
        Dnext.representative
          (ParabolicDerivativeIndex.sourceTime
            (L := M + 2) (by omega) beta) =ᵐ[timeVelocityVolumeOn V]
              W beta) ∧
      (∀ beta : ParabolicDerivativeIndex d M, ∀ j i : Fin d,
        Dnext.representative
          (ParabolicDerivativeIndex.sourceVelocityTwo
            (L := M + 2) (by omega) beta j i) =ᵐ[timeVelocityVolumeOn V]
              fun z => H z beta j i) ∧
      ParabolicWeakDerivativeFamily.squaredL2Norm Dnext ≤
        (Fintype.card (ParabolicDerivativeIndex d (M + 2)) : ℝ) *
          (ParabolicWeakDerivativeFamily.squaredL2Norm D +
            (∑ beta : ParabolicDerivativeIndex d M,
              ∑ j : Fin d, ∑ i : Fin d,
                (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
                  (timeVelocityVolumeOn V))) ^ 2) +
            ∑ beta : ParabolicDerivativeIndex d M,
              (ENNReal.toReal (eLpNorm (W beta) 2
                (timeVelocityVolumeOn V))) ^ 2) := by
  refine ⟨canonicalFamily hM hV D H W hHmem hHweak hWmem hWweak, ?_, ?_, ?_, ?_⟩
  · exact canonicalFamily_representative_inherited
      hM hV D H W hHmem hHweak hWmem hWweak
  · exact canonicalFamily_representative_sourceTime_ae
      hM hV D H W hHmem hHweak hWmem hWweak
  · exact canonicalFamily_representative_sourceVelocityTwo_ae
      hM hV D H W hHmem hHweak hWmem hWweak
  · exact canonicalFamily_squaredL2Norm_le
      hM hV D H W hHmem hHweak hWmem hWweak

end ParabolicDerivativeIndex

end HypoellipticAleksandrov.Parabolic
