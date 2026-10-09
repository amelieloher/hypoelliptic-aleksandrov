module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization

/-!
# Kinetic affine changes of variables

A `KineticAffineScaling` is the source's affine change of variables of the transported
kinetic space `(σ, y, z)` (companion paper, (2.10)):
`σ = σ₀ + a τ`, `y = y₀ + c Y`, `z = z₀ + (a τ) w + e Z`, with `a, c, e > 0`.

* The source kinetic scaling `r ↦ (a, c, e) = (r², r, r³)`, `w = b(v_*)` is
  `KineticAffineScaling.ofRadius` (in `Scaling.Instances`).
* The ellipticity normalization `σ̂ = λ^(1/3) σ`, `v̂ = λ^(-1/3) v`, `ẑ = z` is
  `KineticAffineScaling.ofLambda` (in `Scaling.Instances`).

This file records the coordinate maps (hat to original), their inverses, the rescaled
coefficient and drift, and the compatibility of the moving domains.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov

/-- The affine change of variables `σ = σ₀ + a τ`, `y = y₀ + c Y`,
`z = z₀ + (a τ) w + e Z` (hat variables `(τ, Y, Z)` to original variables `(σ, y, z)`). -/
structure KineticAffineScaling (d : ℕ) where
  /-- Time scale `a` (the source's `r²`). -/
  a : ℝ
  /-- Diffused-coordinate scale `c` (the source's `r`). -/
  c : ℝ
  /-- Transported-coordinate scale `e` (the source's `r³`). -/
  e : ℝ
  /-- Time origin `σ₀`. -/
  σ₀ : ℝ
  /-- Diffused-coordinate origin `y₀`. -/
  y₀ : PDE.Vec d
  /-- Transported-coordinate origin `z₀`. -/
  z₀ : PDE.Vec d
  /-- Constant transport velocity subtracted from the drift (the source's `b(v_*)`). -/
  w : PDE.Vec d
  a_pos : 0 < a
  c_pos : 0 < c
  e_pos : 0 < e

namespace KineticAffineScaling

variable {d : ℕ} (Φ : KineticAffineScaling d)

/-! ### Coordinate maps, hat to original -/

/-- Original time from hat time. -/
def time (τ : ℝ) : ℝ := Φ.σ₀ + Φ.a * τ

/-- Original diffused coordinate from the hat one. -/
def position (Y : PDE.Vec d) : PDE.Vec d := Φ.y₀ + Φ.c • Y

/-- Original transported coordinate from the hat one, at hat time `τ`. -/
def transport (τ : ℝ) (Z : PDE.Vec d) : PDE.Vec d :=
  Φ.z₀ + (Φ.a * τ) • Φ.w + Φ.e • Z

/-- Hat time from original time. -/
def timeInv (σ : ℝ) : ℝ := (σ - Φ.σ₀) / Φ.a

/-- Hat diffused coordinate from the original one. -/
def positionInv (y : PDE.Vec d) : PDE.Vec d := Φ.c⁻¹ • (y - Φ.y₀)

/-- Hat transported coordinate from the original one, at hat time `τ`. -/
def transportInv (τ : ℝ) (z : PDE.Vec d) : PDE.Vec d :=
  Φ.e⁻¹ • (z - Φ.z₀ - (Φ.a * τ) • Φ.w)

theorem time_timeInv (σ : ℝ) : Φ.time (Φ.timeInv σ) = σ := by
  unfold time timeInv
  rw [mul_div_cancel₀ _ Φ.a_pos.ne']
  ring

theorem timeInv_time (τ : ℝ) : Φ.timeInv (Φ.time τ) = τ := by
  unfold time timeInv
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ Φ.a_pos.ne']

theorem position_positionInv (y : PDE.Vec d) : Φ.position (Φ.positionInv y) = y := by
  unfold position positionInv
  rw [smul_smul, mul_inv_cancel₀ Φ.c_pos.ne', one_smul]
  abel

theorem positionInv_position (Y : PDE.Vec d) : Φ.positionInv (Φ.position Y) = Y := by
  unfold position positionInv
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ Φ.c_pos.ne', one_smul]

theorem transport_transportInv (τ : ℝ) (z : PDE.Vec d) :
    Φ.transport τ (Φ.transportInv τ z) = z := by
  unfold transport transportInv
  rw [smul_smul, mul_inv_cancel₀ Φ.e_pos.ne', one_smul]
  abel

theorem transportInv_transport (τ : ℝ) (Z : PDE.Vec d) :
    Φ.transportInv τ (Φ.transport τ Z) = Z := by
  unfold transport transportInv
  have : Φ.z₀ + (Φ.a * τ) • Φ.w + Φ.e • Z - Φ.z₀ - (Φ.a * τ) • Φ.w = Φ.e • Z := by abel
  rw [this, smul_smul, inv_mul_cancel₀ Φ.e_pos.ne', one_smul]

theorem continuous_position : Continuous Φ.position := by
  unfold position
  fun_prop

theorem continuous_positionInv : Continuous Φ.positionInv := by
  unfold positionInv
  fun_prop

theorem continuous_transport (τ : ℝ) : Continuous (Φ.transport τ) := by
  unfold transport
  fun_prop

theorem continuous_transportInv (τ : ℝ) : Continuous (Φ.transportInv τ) := by
  unfold transportInv
  fun_prop

/-- The change of the diffused coordinate as a homeomorphism. -/
def positionHomeo : PDE.Vec d ≃ₜ PDE.Vec d where
  toFun := Φ.position
  invFun := Φ.positionInv
  left_inv := Φ.positionInv_position
  right_inv := Φ.position_positionInv
  continuous_toFun := Φ.continuous_position
  continuous_invFun := Φ.continuous_positionInv

@[simp] theorem positionHomeo_apply (Y : PDE.Vec d) : Φ.positionHomeo Y = Φ.position Y := rfl

/-- The change of the ambient fixed-time state `(y, z)`, hat to original, at hat time `τ`. -/
def ambientHomeo (τ : ℝ) : EvolutionAmbientState d ≃ₜ EvolutionAmbientState d where
  toFun x := (Φ.position x.1, Φ.transport τ x.2)
  invFun x := (Φ.positionInv x.1, Φ.transportInv τ x.2)
  left_inv x := by
    simp only [Φ.positionInv_position, Φ.transportInv_transport]
  right_inv x := by
    simp only [Φ.position_positionInv, Φ.transport_transportInv]
  continuous_toFun := (Φ.continuous_position.comp continuous_fst).prodMk
    ((Φ.continuous_transport τ).comp continuous_snd)
  continuous_invFun := (Φ.continuous_positionInv.comp continuous_fst).prodMk
    ((Φ.continuous_transportInv τ).comp continuous_snd)

@[simp] theorem ambientHomeo_apply (τ : ℝ) (x : EvolutionAmbientState d) :
    Φ.ambientHomeo τ x = (Φ.position x.1, Φ.transport τ x.2) := rfl

@[simp] theorem ambientHomeo_symm_apply (τ : ℝ) (x : EvolutionAmbientState d) :
    (Φ.ambientHomeo τ).symm x = (Φ.positionInv x.1, Φ.transportInv τ x.2) := rfl

/-- The ambient change of variables as a measurable equivalence. -/
def ambientEquiv (τ : ℝ) : EvolutionAmbientState d ≃ᵐ EvolutionAmbientState d :=
  (Φ.ambientHomeo τ).toMeasurableEquiv

@[simp] theorem ambientEquiv_apply (τ : ℝ) (x : EvolutionAmbientState d) :
    Φ.ambientEquiv τ x = (Φ.position x.1, Φ.transport τ x.2) := rfl

@[simp] theorem ambientEquiv_symm_apply (τ : ℝ) (x : EvolutionAmbientState d) :
    (Φ.ambientEquiv τ).symm x = (Φ.positionInv x.1, Φ.transportInv τ x.2) := rfl

/-! ### The change of variables on kinetic points -/

/-- The change of variables on kinetic points `(τ, Y, Z) ↦ (σ, y, z)`. -/
def point (p : KineticPoint d) : KineticPoint d :=
  ⟨Φ.time p.time, Φ.position p.position, Φ.transport p.time p.velocity⟩

/-- The inverse change of variables on kinetic points. -/
def pointInv (p : KineticPoint d) : KineticPoint d :=
  ⟨Φ.timeInv p.time, Φ.positionInv p.position,
    Φ.transportInv (Φ.timeInv p.time) p.velocity⟩

@[simp] theorem point_time (p : KineticPoint d) : (Φ.point p).time = Φ.time p.time := rfl

@[simp] theorem point_position (p : KineticPoint d) :
    (Φ.point p).position = Φ.position p.position := rfl

@[simp] theorem point_velocity (p : KineticPoint d) :
    (Φ.point p).velocity = Φ.transport p.time p.velocity := rfl

theorem point_pointInv (p : KineticPoint d) : Φ.point (Φ.pointInv p) = p := by
  simp only [point, pointInv, Φ.time_timeInv, Φ.position_positionInv,
    Φ.transport_transportInv]

theorem pointInv_point (p : KineticPoint d) : Φ.pointInv (Φ.point p) = p := by
  simp only [point, pointInv, Φ.timeInv_time, Φ.positionInv_position,
    Φ.transportInv_transport]

/-- The change of variables on raw coordinates `(σ, (y, z))`. -/
def raw (q : ℝ × (PDE.Vec d × PDE.Vec d)) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (Φ.time q.1, (Φ.position q.2.1, Φ.transport q.1 q.2.2))

/-- The inverse change of variables on raw coordinates. -/
def rawInv (q : ℝ × (PDE.Vec d × PDE.Vec d)) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (Φ.timeInv q.1, (Φ.positionInv q.2.1, Φ.transportInv (Φ.timeInv q.1) q.2.2))

theorem raw_rawInv (q : ℝ × (PDE.Vec d × PDE.Vec d)) : Φ.raw (Φ.rawInv q) = q := by
  simp only [raw, rawInv, Φ.time_timeInv, Φ.position_positionInv, Φ.transport_transportInv]

theorem rawInv_raw (q : ℝ × (PDE.Vec d × PDE.Vec d)) : Φ.rawInv (Φ.raw q) = q := by
  simp only [raw, rawInv, Φ.timeInv_time, Φ.positionInv_position, Φ.transportInv_transport]

theorem contDiff_raw : ContDiff ℝ (⊤ : ℕ∞) Φ.raw := by
  unfold raw time position transport
  fun_prop

theorem contDiff_rawInv : ContDiff ℝ (⊤ : ℕ∞) Φ.rawInv := by
  unfold rawInv timeInv positionInv transportInv
  fun_prop

theorem continuous_point : Continuous Φ.point := by
  have h : Φ.point = fun p => (KineticPoint.homeomorphProd d).symm
      (Φ.raw ((KineticPoint.homeomorphProd d) p)) := rfl
  rw [h]
  exact (KineticPoint.homeomorphProd d).symm.continuous.comp
    (Φ.contDiff_raw.continuous.comp (KineticPoint.homeomorphProd d).continuous)

theorem continuous_pointInv : Continuous Φ.pointInv := by
  have h : Φ.pointInv = fun p => (KineticPoint.homeomorphProd d).symm
      (Φ.rawInv ((KineticPoint.homeomorphProd d) p)) := rfl
  rw [h]
  exact (KineticPoint.homeomorphProd d).symm.continuous.comp
    (Φ.contDiff_rawInv.continuous.comp (KineticPoint.homeomorphProd d).continuous)

/-- The change of variables on kinetic points as a homeomorphism. -/
def pointHomeo : KineticPoint d ≃ₜ KineticPoint d where
  toFun := Φ.point
  invFun := Φ.pointInv
  left_inv := Φ.pointInv_point
  right_inv := Φ.point_pointInv
  continuous_toFun := Φ.continuous_point
  continuous_invFun := Φ.continuous_pointInv

/-! ### Rescaled coefficient and drift -/

/-- The rescaled coefficient `B̂(τ, Y, Z) = (a / c²) B(σ, y, z)`. -/
def coefficient (B : FullKineticCoefficient d) : FullKineticCoefficient d :=
  fun τ Y Z => (Φ.a / Φ.c ^ 2) • B (Φ.time τ) (Φ.position Y) (Φ.transport τ Z)

/-- The rescaled drift `b̂(Y) = (a / e) (b(y₀ + c Y) - w)`. -/
def drift (b : PDE.Vec d → PDE.Vec d) : PDE.Vec d → PDE.Vec d :=
  fun Y => (Φ.a / Φ.e) • (b (Φ.position Y) - Φ.w)

@[simp] theorem coefficient_apply (B : FullKineticCoefficient d) (τ : ℝ) (Y Z : PDE.Vec d) :
    Φ.coefficient B τ Y Z =
      (Φ.a / Φ.c ^ 2) • B (Φ.time τ) (Φ.position Y) (Φ.transport τ Z) := rfl

@[simp] theorem drift_apply (b : PDE.Vec d → PDE.Vec d) (Y : PDE.Vec d) :
    Φ.drift b Y = (Φ.a / Φ.e) • (b (Φ.position Y) - Φ.w) := rfl

/-! ### Compatibility of the moving domains -/

/-- The hat moving domains are the preimages of the original ones:
`movingDomain Ω̂ γ̂ τ = {Y | y₀ + c Y ∈ movingDomain Ω γ (σ₀ + a τ)}`. -/
def MapsDomain (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (Ω' : Set (PDE.Vec d)) (γ' : ℝ → PDE.Vec d) : Prop :=
  ∀ τ, movingDomain Ω' γ' τ = Φ.position ⁻¹' movingDomain Ω γ (Φ.time τ)

variable {Ω Ω' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}

variable {Φ}

theorem MapsDomain.mem_iff (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ) (Y : PDE.Vec d) :
    Y ∈ movingDomain Ω' γ' τ ↔ Φ.position Y ∈ movingDomain Ω γ (Φ.time τ) := by
  rw [h τ]
  rfl

theorem MapsDomain.stateSet_mem_iff (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ)
    (x : EvolutionAmbientState d) :
    x ∈ evolutionStateSet Ω' γ' τ ↔
      Φ.ambientEquiv τ x ∈ evolutionStateSet Ω γ (Φ.time τ) := by
  simp only [evolutionStateSet, mem_prod, mem_univ, and_true, h.mem_iff, ambientEquiv_apply]

theorem MapsDomain.closure_eq (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ) :
    closure (movingDomain Ω' γ' τ) = Φ.position ⁻¹' closure (movingDomain Ω γ (Φ.time τ)) := by
  rw [h τ]
  exact (Φ.positionHomeo.preimage_closure _).symm

theorem MapsDomain.frontier_eq (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ) :
    frontier (movingDomain Ω' γ' τ) =
      Φ.position ⁻¹' frontier (movingDomain Ω γ (Φ.time τ)) := by
  rw [h τ]
  exact (Φ.positionHomeo.preimage_frontier _).symm

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
