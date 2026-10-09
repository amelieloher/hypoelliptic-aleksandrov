module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.TransportSlices
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelay
import Mathlib.Tactic

/-! # The sharp delayed-union estimate in kinetic transport coordinates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Open stack interiors avoid any uncountable union of terminal faces. -/
def openForwardStack {d : ℕ} (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    Set (KineticPoint d) :=
  forwardStack P r m ∩ {X | X.time < P.time+(m : ℝ)*r^2}

/-- Open forward stack interiors are open. -/
theorem isOpen_openForwardStack {d : ℕ} (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    IsOpen (openForwardStack P r m) := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have heq : openForwardStack P r m =
      {X | P.time < X.time ∧ X.time < P.time+(m : ℝ)*r^2 ∧
        X.velocity ∈ PDE.euclideanBall P.velocity r ∧
        relativePosition P X ∈ PDE.euclideanBall 0 (((m+2 : ℕ) : ℝ)*r^3)} := by
    ext X
    change (0 < X.time-P.time ∧ X.time-P.time ≤ (m : ℝ)*r^2 ∧ _ ∧ _) ∧ _ ↔ _
    constructor
    · rintro ⟨⟨ht, _, hv, hx⟩, htop⟩
      exact ⟨by linarith, htop, hv, hx⟩
    · rintro ⟨ht, htop, hv, hx⟩
      exact ⟨⟨by linarith, by linarith, hv, hx⟩, htop⟩
  rw [heq]
  exact (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (((PDE.isOpen_euclideanBall _ _).preimage continuous_velocity).inter
        ((PDE.isOpen_euclideanBall _ _).preimage hx)))

/-- Kinetic volume equals integration of time-slice volumes in transport coordinates. -/
theorem volume_transport_slices {d : ℕ} {S : Set (KineticPoint d)}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v : PDE.Vec d, ∫⁻ y : PDE.Vec d,
      volume {t : ℝ | transportChart (v,y,t) ∈ S} := by
  have hs : MeasurableSet (transportChart ⁻¹' S) :=
    hS.preimage (continuous_transportChart d).measurable
  rw [← (measurePreserving_transportChart d).measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hs]
  apply lintegral_congr
  intro v
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurable_prodMk_left hs)]
  rfl

/-- Each transport slice satisfies the sharp one-dimensional delayed-union inequality. -/
theorem delayed_union_slice {d : ℕ} {ι : Type*} [Countable ι]
    (P : ι → KineticPoint d) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (m : ℕ) (hm : 0 < m) (v y : PDE.Vec d) :
    volume {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, backwardCylinder (P i) (r i)} ≤
      ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, openForwardStack (P i) (r i) m} := by
  let A : Set ι := {i | v ∈ PDE.euclideanBall (P i).velocity (r i) ∧
    y ∈ PDE.euclideanBall ((P i).position-(P i).time • v) (2*(r i)^3)}
  have hback : {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, backwardCylinder (P i) (r i)} ⊆
      ⋃ i : A, Ioo ((P i).time-(r i)^2) (P i).time := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨htime, hv, hy⟩ := cylinder_transport_slice (P i) (hr i) v y t hi
    exact mem_iUnion.mpr ⟨⟨i, hv, hy⟩, htime⟩
  have hforward : (⋃ i : A, Ioo (P i).time ((P i).time+(m : ℝ)*(r i)^2)) ⊆
      {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, openForwardStack (P i) (r i) m} := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    apply mem_iUnion.mpr
    exact ⟨i, delayed_transport_slice (P i) (hr i) m v y t hi i.2.1 i.2.2, hi.2⟩
  calc
    _ ≤ volume (⋃ i : A, Ioo ((P i).time-(r i)^2) (P i).time) := measure_mono hback
    _ ≤ ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume (⋃ i : A, Ioo (P i).time ((P i).time+(m : ℝ)*(r i)^2)) :=
      interval_delay_countable (fun i : A => (P i).time) (fun i : A => (r i)^2)
        (by exact_mod_cast hm) (fun i => sq_pos_of_pos (hr i))
    _ ≤ _ := mul_le_mul_right (measure_mono hforward) _

/-- Countable kinetic cylinder families satisfy the sharp delayed-union estimate. -/
theorem delayed_union_countable {d : ℕ} {ι : Type*} [Countable ι]
    (P : ι → KineticPoint d) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (m : ℕ) (hm : 0 < m) :
    volume (⋃ i, backwardCylinder (P i) (r i)) ≤
      ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume (⋃ i, openForwardStack (P i) (r i) m) := by
  rw [volume_transport_slices (isOpen_iUnion (fun i => isOpen_cylinder (P i) (r i))).measurableSet,
    volume_transport_slices
      (isOpen_iUnion (fun i => isOpen_openForwardStack (P i) (r i) m)).measurableSet,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun y => delayed_union_slice P r hr m hm v y

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
