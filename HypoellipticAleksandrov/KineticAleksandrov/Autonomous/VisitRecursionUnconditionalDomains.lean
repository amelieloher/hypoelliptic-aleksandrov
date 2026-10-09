module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomains
import Mathlib.Tactic

/-! # Clipped active and waiting velocity intervals, including empty components -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set
open scoped Classical

/-- An empty finite union, with no artificial nonempty component. -/
def visitEmptyUnion : FiniteIntervalUnion where
  count := 0
  component := Fin.elim0
  disjoint := fun i => Fin.elim0 i

/-- The empty representation has empty physical carrier. -/
theorem visitEmptyUnion_carrier : visitEmptyUnion.carrier = ∅ := by
  ext v
  simp only [FiniteIntervalUnion.carrier, visitEmptyUnion, mem_iUnion, mem_empty_iff_false]
  exact ⟨fun ⟨i, _⟩ => Fin.elim0 i, False.elim⟩

/-- A clipped interval is represented by zero components when its endpoints overlap. -/
def visitIntervalUnion (lo hi : ℝ) : FiniteIntervalUnion :=
  if h : lo < hi then (⟨lo, hi, h⟩ : Interval).toFiniteUnion else visitEmptyUnion

/-- The clipped representation has exactly the scalar open-interval carrier. -/
theorem visitIntervalUnion_carrier (lo hi : ℝ) :
    (visitIntervalUnion lo hi).carrier = Ioo lo hi := by
  unfold visitIntervalUnion
  split
  · rw [Interval.toFiniteUnion_carrier]
    rfl
  · rename_i h
    rw [visitEmptyUnion_carrier, Ioo_eq_empty_of_le (not_lt.mp h)]

/-- Two certified disjoint interval components in the existing finite-union API. -/
def visitPairUnion (L R : Interval) (hd : Disjoint L.carrier R.carrier) :
    FiniteIntervalUnion where
  count := 2
  component := fun i => if i = 0 then L else R
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa using hd
    · simpa using hd.symm
    · exact False.elim (hij rfl)

/-- The pair representation contains precisely its two interval carriers. -/
theorem visitPairUnion_carrier (L R : Interval) (hd : Disjoint L.carrier R.carrier) :
    (visitPairUnion L R hd).carrier = L.carrier ∪ R.carrier := by
  ext v
  simp only [FiniteIntervalUnion.carrier, visitPairUnion, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hv | hv)
    · exact ⟨0, hv⟩
    · exact ⟨1, hv⟩

/-- The active velocity intersection in the original physical coordinate. -/
def visitActiveUnion (c : Clock) (J : Interval) : FiniteIntervalUnion :=
  visitIntervalUnion (max (c.vbar - 3 * c.r / 4) J.lo)
    (min (c.vbar + 3 * c.r / 4) J.hi)

/-- Exact active-domain geometry, with emptiness handled by the existing union carrier. -/
theorem visitActiveUnion_carrier (c : Clock) (J : Interval) :
    (visitActiveUnion c J).carrier = c.active ∩ J.carrier := by
  rw [visitActiveUnion, visitIntervalUnion_carrier]
  ext v
  simp only [Clock.active, Interval.carrier, mem_Ioo, max_lt_iff, lt_min_iff,
    mem_inter_iff]
  tauto

/-- The two possible waiting components are disjoint, even before clipping to the outer strip. -/
theorem visitWaiting_components_disjoint (c : Clock) (J : Interval)
    (hl : J.lo < min J.hi (c.vbar - c.r / 2))
    (hr : max J.lo (c.vbar + c.r / 2) < J.hi) :
    Disjoint (⟨J.lo, min J.hi (c.vbar - c.r / 2), hl⟩ : Interval).carrier
      (⟨max J.lo (c.vbar + c.r / 2), J.hi, hr⟩ : Interval).carrier := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  have hlow := le_max_right J.lo (c.vbar + c.r / 2)
  have hhigh := min_le_right J.hi (c.vbar - c.r / 2)
  change J.lo < v ∧ v < min J.hi (c.vbar - c.r / 2) at hv
  change max J.lo (c.vbar + c.r / 2) < v ∧ v < J.hi at hw
  linarith only [hv.2, hw.1, hlow, hhigh, c.positive]

/-- The waiting domain has zero, one, or two actual nonempty interval components. -/
def visitWaitingUnion (c : Clock) (J : Interval) : FiniteIntervalUnion :=
  if hl : J.lo < min J.hi (c.vbar - c.r / 2) then
    if hr : max J.lo (c.vbar + c.r / 2) < J.hi then
      visitPairUnion ⟨J.lo, min J.hi (c.vbar - c.r / 2), hl⟩
        ⟨max J.lo (c.vbar + c.r / 2), J.hi, hr⟩
        (visitWaiting_components_disjoint c J hl hr)
    else (⟨J.lo, min J.hi (c.vbar - c.r / 2), hl⟩ : Interval).toFiniteUnion
  else visitIntervalUnion (max J.lo (c.vbar + c.r / 2)) J.hi

/-- Literal scalar carriers of the two waiting pieces. -/
theorem visitWaitingUnion_components (c : Clock) (J : Interval) :
    (visitWaitingUnion c J).carrier =
      Ioo J.lo (min J.hi (c.vbar - c.r / 2)) ∪
        Ioo (max J.lo (c.vbar + c.r / 2)) J.hi := by
  unfold visitWaitingUnion
  split
  · split
    · rw [visitPairUnion_carrier]
      rfl
    · rename_i hr
      rw [Interval.toFiniteUnion_carrier, Ioo_eq_empty_of_le (not_lt.mp hr), union_empty]
      rfl
  · rename_i hl
    rw [visitIntervalUnion_carrier, Ioo_eq_empty_of_le (not_lt.mp hl), empty_union]

/-- The waiting carrier is precisely the outer interval minus the closed entrance interval. -/
theorem visitWaitingUnion_carrier (c : Clock) (J : Interval) :
    (visitWaitingUnion c J).carrier = J.carrier \ closure c.entrance := by
  have ho : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
  rw [visitWaitingUnion_components, Clock.entrance, closure_Ioo ho.ne]
  ext v
  simp only [Interval.carrier, mem_union, mem_Ioo, lt_min_iff, max_lt_iff,
    mem_sdiff, mem_Icc, not_and_or, not_le]
  tauto

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
