module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Affine

/-!
# Moving cylinders under an affine change of variables

For compatible moving domains (`MapsDomain`), every cylinder, terminal face and lateral
frontier of the hat data is the preimage of the corresponding original set under the change
of variables on kinetic points (resp. raw coordinates).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov

namespace KineticAffineScaling

variable {d : ℕ} (Φ : KineticAffineScaling d)

theorem time_lt_iff {x y : ℝ} : Φ.time x < Φ.time y ↔ x < y := by
  unfold time
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left (by linarith) Φ.a_pos.le
  · intro h
    nlinarith [Φ.a_pos]

theorem time_le_iff {x y : ℝ} : Φ.time x ≤ Φ.time y ↔ x ≤ y := by
  unfold time
  constructor
  · intro h
    exact le_of_mul_le_mul_left (by linarith) Φ.a_pos
  · intro h
    nlinarith [Φ.a_pos]

theorem time_inj {x y : ℝ} : Φ.time x = Φ.time y ↔ x = y := by
  constructor
  · intro h
    exact le_antisymm (Φ.time_le_iff.1 h.le) (Φ.time_le_iff.1 h.ge)
  · intro h
    rw [h]

variable {Ω Ω' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}

/-- Membership in a moving domain, in terms of the subtraction of the curve. -/
theorem mem_movingDomain_iff {y : PDE.Vec d} {σ : ℝ} :
    y ∈ movingDomain Ω γ σ ↔ y - γ σ ∈ Ω := by
  rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
  rfl

/-- The raw interior cylinder of an open domain with continuous curve is open. -/
theorem isOpen_evolutionPastInteriorRaw (hΩ : IsOpen Ω) (hγ : Continuous γ) (τ : ℝ) :
    IsOpen (evolutionPastInteriorRaw Ω γ τ) := by
  have h : evolutionPastInteriorRaw Ω γ τ =
      {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < τ} ∩
        (fun q : ℝ × (PDE.Vec d × PDE.Vec d) => q.2.1 - γ q.1) ⁻¹' Ω := by
    ext q
    simp only [evolutionPastInteriorRaw, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      mem_movingDomain_iff]
  rw [h]
  refine (isOpen_lt continuous_fst continuous_const).inter (hΩ.preimage ?_)
  exact (continuous_fst.comp continuous_snd).sub (hγ.comp continuous_fst)

variable {Φ}

variable (h : Φ.MapsDomain Ω γ Ω' γ')
include h

theorem MapsDomain.mem_openCylinder_iff (τ : ℝ) (p : KineticPoint d) :
    p ∈ evolutionPastOpenCylinder Ω' γ' τ ↔
      Φ.point p ∈ evolutionPastOpenCylinder Ω γ (Φ.time τ) := by
  simp only [evolutionPastOpenCylinder, mem_ofPred_eq, point_time, point_position,
    Φ.time_lt_iff, h.mem_iff]

theorem MapsDomain.mem_closedCylinder_iff (τ : ℝ) (p : KineticPoint d) :
    p ∈ evolutionPastClosedCylinder Ω' γ' τ ↔
      Φ.point p ∈ evolutionPastClosedCylinder Ω γ (Φ.time τ) := by
  simp only [evolutionPastClosedCylinder, mem_ofPred_eq, point_time, point_position,
    Φ.time_le_iff, h.closure_eq, mem_preimage]

theorem MapsDomain.mem_terminalClosure_iff (τ : ℝ) (p : KineticPoint d) :
    p ∈ evolutionTerminalClosure Ω' γ' τ ↔
      Φ.point p ∈ evolutionTerminalClosure Ω γ (Φ.time τ) := by
  simp only [evolutionTerminalClosure, mem_ofPred_eq, point_time, point_position,
    Φ.time_inj, h.closure_eq, mem_preimage]

theorem MapsDomain.mem_lateralFrontier_iff (τ : ℝ) (p : KineticPoint d) :
    p ∈ evolutionLateralFrontier Ω' γ' τ ↔
      Φ.point p ∈ evolutionLateralFrontier Ω γ (Φ.time τ) := by
  simp only [evolutionLateralFrontier, mem_ofPred_eq, point_time, point_position,
    Φ.time_le_iff, h.frontier_eq, mem_preimage]

theorem MapsDomain.mem_interiorRaw_iff (τ : ℝ) (q : ℝ × (PDE.Vec d × PDE.Vec d)) :
    q ∈ evolutionPastInteriorRaw Ω' γ' τ ↔
      Φ.raw q ∈ evolutionPastInteriorRaw Ω γ (Φ.time τ) := by
  simp only [evolutionPastInteriorRaw, mem_ofPred_eq, raw, Φ.time_lt_iff, h.mem_iff]

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
