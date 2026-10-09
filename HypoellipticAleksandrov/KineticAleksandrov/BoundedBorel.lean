module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Bounded Borel functions

This module defines the bounded real Borel-function carrier used by the
kinetic evolution statement.  Bounds are existential witnesses, so the
carrier has extensional equality and inherits its real vector-space API from
a `Submodule` of all real-valued functions.
-/

@[expose] public section

set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Bounded real Borel functions, represented as a submodule of all functions. -/
def boundedBorelSubmodule (α : Type*) [MeasurableSpace α] :
    Submodule ℝ (α → ℝ) where
  carrier := {f | Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, abs (f x) ≤ C}
  zero_mem' := by
    constructor
    · exact measurable_const
    · exact ⟨0, le_rfl, fun x => by simp⟩
  add_mem' := by
    intro f g hf hg
    constructor
    · exact hf.1.add hg.1
    · rcases hf.2 with ⟨Cf, hCf, hf⟩
      rcases hg.2 with ⟨Cg, hCg, hg⟩
      refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
      intro x
      exact (abs_add_le _ _).trans (add_le_add (hf x) (hg x))
  smul_mem' := by
    intro c f hf
    constructor
    · exact measurable_const.smul hf.1
    · rcases hf.2 with ⟨C, hC, hf⟩
      refine ⟨abs c * C, mul_nonneg (abs_nonneg _) hC, ?_⟩
      intro x
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
        mul_le_mul_of_nonneg_left (hf x) (abs_nonneg c)

/-- The literal bounded-Borel real-function carrier. -/
abbrev BoundedBorel (α : Type*) [MeasurableSpace α] :=
  ↥(boundedBorelSubmodule α)

instance {α : Type*} [MeasurableSpace α] :
    CoeFun (BoundedBorel α) (fun _ => α → ℝ) where
  coe f := f.1

namespace BoundedBorel

/-- Bounded-Borel functions are equal when they agree pointwise. -/
@[ext]
theorem ext {α : Type*} [MeasurableSpace α]
    {f g : BoundedBorel α} (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

/-- The underlying function of a bounded-Borel function is measurable. -/
theorem measurable {α : Type*} [MeasurableSpace α]
    (f : BoundedBorel α) : Measurable f := f.property.1

/-- A bounded-Borel function has a finite nonnegative uniform absolute bound. -/
theorem exists_bound {α : Type*} [MeasurableSpace α]
    (f : BoundedBorel α) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, abs (f x) ≤ C :=
  f.property.2

/-- The bounded-Borel constant function with value `c`. -/
def const {α : Type*} [MeasurableSpace α] (c : ℝ) : BoundedBorel α :=
  ⟨fun _ => c, measurable_const, ⟨abs c, abs_nonneg _, fun _ => le_rfl⟩⟩

/-- The constant-one bounded-Borel function. -/
instance {α : Type*} [MeasurableSpace α] : One (BoundedBorel α) :=
  ⟨const 1⟩

@[simp]
theorem zero_apply {α : Type*} [MeasurableSpace α] (x : α) :
    (0 : BoundedBorel α) x = 0 := rfl

@[simp]
theorem one_apply {α : Type*} [MeasurableSpace α] (x : α) :
    (1 : BoundedBorel α) x = 1 := rfl

@[simp]
theorem const_apply {α : Type*} [MeasurableSpace α] (c : ℝ) (x : α) :
    const c x = c := rfl

@[simp]
theorem add_apply {α : Type*} [MeasurableSpace α]
    (f g : BoundedBorel α) (x : α) : (f + g) x = f x + g x := rfl

@[simp]
theorem neg_apply {α : Type*} [MeasurableSpace α]
    (f : BoundedBorel α) (x : α) : (-f) x = -f x := rfl

@[simp]
theorem sub_apply {α : Type*} [MeasurableSpace α]
    (f g : BoundedBorel α) (x : α) : (f - g) x = f x - g x := rfl

@[simp]
theorem smul_apply {α : Type*} [MeasurableSpace α]
    (c : ℝ) (f : BoundedBorel α) (x : α) : (c • f) x = c • f x := rfl

/-- The pointwise maximum of two bounded-Borel functions. -/
def supFn {α : Type*} [MeasurableSpace α]
    (f g : BoundedBorel α) : BoundedBorel α :=
  ⟨fun x => max (f x) (g x), by
    constructor
    · exact f.measurable.max g.measurable
    · rcases f.exists_bound with ⟨Cf, hCf, hf⟩
      rcases g.exists_bound with ⟨Cg, hCg, hg⟩
      refine ⟨max Cf Cg, hCf.trans (le_max_left _ _), ?_⟩
      intro x
      rcases le_total (f x) (g x) with h | h
      · change abs (max (f x) (g x)) ≤ max Cf Cg
        rw [max_eq_right h]
        exact (hg x).trans (le_max_right _ _)
      · change abs (max (f x) (g x)) ≤ max Cf Cg
        rw [max_eq_left h]
        exact (hf x).trans (le_max_left _ _)⟩

/-- The pointwise minimum of two bounded-Borel functions. -/
def infFn {α : Type*} [MeasurableSpace α]
    (f g : BoundedBorel α) : BoundedBorel α :=
  ⟨fun x => min (f x) (g x), by
    constructor
    · exact f.measurable.min g.measurable
    · rcases f.exists_bound with ⟨Cf, hCf, hf⟩
      rcases g.exists_bound with ⟨Cg, hCg, hg⟩
      refine ⟨max Cf Cg, hCf.trans (le_max_left _ _), ?_⟩
      intro x
      rcases le_total (f x) (g x) with h | h
      · change abs (min (f x) (g x)) ≤ max Cf Cg
        rw [min_eq_left h]
        exact (hf x).trans (le_max_left _ _)
      · change abs (min (f x) (g x)) ≤ max Cf Cg
        rw [min_eq_right h]
        exact (hg x).trans (le_max_right _ _)⟩

/-- Pointwise order and lattice operations on bounded-Borel functions. -/
instance {α : Type*} [MeasurableSpace α] : Lattice (BoundedBorel α) where
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_rfl
  le_trans f g h hfg hgh x := (hfg x).trans (hgh x)
  le_antisymm f g hfg hgf := ext (fun x => le_antisymm (hfg x) (hgf x))
  sup := supFn
  le_sup_left f g x := le_max_left _ _
  le_sup_right f g x := le_max_right _ _
  sup_le f g h hfg hgh x := max_le (hfg x) (hgh x)
  inf := infFn
  inf_le_left f g x := min_le_left _ _
  inf_le_right f g x := min_le_right _ _
  le_inf f g h hfg hgh x := le_min (hfg x) (hgh x)

@[simp]
theorem sup_apply {α : Type*} [MeasurableSpace α]
    (f g : BoundedBorel α) (x : α) : (f ⊔ g) x = max (f x) (g x) := rfl

@[simp]
theorem inf_apply {α : Type*} [MeasurableSpace α]
    (f g : BoundedBorel α) (x : α) : (f ⊓ g) x = min (f x) (g x) := rfl

/-- The positive part `max f 0` of a bounded-Borel function. -/
def positivePart {α : Type*} [MeasurableSpace α]
    (f : BoundedBorel α) : BoundedBorel α := f ⊔ 0

@[simp]
theorem positivePart_apply {α : Type*} [MeasurableSpace α]
    (f : BoundedBorel α) (x : α) : f.positivePart x = max (f x) 0 := rfl

/-- Pull a bounded-Borel function back along a measurable map. -/
def pullback {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (g : β → α) (hg : Measurable g) (f : BoundedBorel α) : BoundedBorel β :=
  ⟨fun x => f (g x), by
    constructor
    · exact f.measurable.comp hg
    · rcases f.exists_bound with ⟨C, hC, hf⟩
      exact ⟨C, hC, fun x => hf (g x)⟩⟩

@[simp]
theorem pullback_apply {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (g : β → α) (hg : Measurable g)
    (f : BoundedBorel α) (x : β) : f.pullback g hg x = f (g x) := rfl

/-- Restrict a bounded-Borel function to a subtype. -/
def restrict {α : Type*} [MeasurableSpace α]
    (s : Set α) (f : BoundedBorel α) : BoundedBorel s :=
  pullback ((↑) : s → α) measurable_subtype_coe f

@[simp]
theorem restrict_apply {α : Type*} [MeasurableSpace α]
    (s : Set α) (f : BoundedBorel α) (x : s) : f.restrict s x = f x := rfl

end BoundedBorel
end HypoellipticAleksandrov.KineticAleksandrov
