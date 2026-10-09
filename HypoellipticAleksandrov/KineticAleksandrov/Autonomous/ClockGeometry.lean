module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import Mathlib.Basic.Real.Sign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # The literal position clock and its inverse

The clock uses the existing kinetic carrier in the order `(sigma,z,y)`.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The position clock of `e:clock`. -/
def Clock.map (c : Clock) (e p : Point) : Point :=
  ⟨(p.position 0 - e.position 0) / (c.vbar * c.r ^ 2),
    fun _ => (p.position 0 - e.position 0 - c.vbar * (p.time - e.time)) / c.r ^ 3,
    fun _ => (p.velocity 0 - c.vbar) / c.r⟩

/-- The literal inverse position clock of `e:clock-inverse`. -/
def Clock.inverse (c : Clock) (e p : Point) : Point :=
  ⟨e.time + c.r ^ 2 * p.time - c.r ^ 3 / c.vbar * p.position 0,
    fun _ => e.position 0 + c.vbar * c.r ^ 2 * p.time,
    fun _ => c.vbar + c.r * p.velocity 0⟩

/-- Applying the inverse after the clock recovers the physical point. -/
theorem Clock.inverse_map (c : Clock) (e p : Point) : c.inverse e (c.map e p) = p := by
  have hr : c.r ≠ 0 := ne_of_gt c.positive
  have hv : c.vbar ≠ 0 := c.nonzero
  ext i
  · simp only [Clock.inverse, Clock.map]
    field_simp [hr, hv]
    ring
  · have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Clock.inverse, Clock.map]
    field_simp [hr, hv]
    ring
  · have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Clock.inverse, Clock.map]
    field_simp [hr, hv]
    ring

/-- Applying the clock after its inverse recovers the normalized point. -/
theorem Clock.map_inverse (c : Clock) (e p : Point) : c.map e (c.inverse e p) = p := by
  have hr : c.r ≠ 0 := ne_of_gt c.positive
  have hv : c.vbar ≠ 0 := c.nonzero
  ext i
  · simp only [Clock.inverse, Clock.map]
    field_simp [hr, hv]
    ring
  · have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Clock.inverse, Clock.map]
    field_simp [hr, hv]
    ring
  · have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Clock.inverse, Clock.map]
    field_simp [hr, hv]
    ring

/-- The clock is a global equivalence; its strip restriction is supplied below. -/
def Clock.equiv (c : Clock) (e : Point) : Point ≃ Point where
  toFun := c.map e
  invFun := c.inverse e
  left_inv := c.inverse_map e
  right_inv := c.map_inverse e

/-- Active velocity membership is exactly normalized active velocity membership. -/
theorem Clock.mem_active_iff (c : Clock) (v : ℝ) :
    v ∈ c.active ↔ (v - c.vbar) / c.r ∈ normalizedActive := by
  simp only [Clock.active, normalizedActive, Set.mem_Ioo]
  rw [lt_div_iff₀ c.positive, div_lt_iff₀ c.positive]
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- The clock and its inverse exchange the two open velocity strips. -/
theorem Clock.strip_image (c : Clock) (e : Point) :
    c.map e '' {p : Point | p.velocity 0 ∈ c.active} =
      {p : Point | p.velocity 0 ∈ normalizedActive} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (c.mem_active_iff (q.velocity 0)).mp hq
  · intro hp
    refine ⟨c.inverse e p, ?_, c.map_inverse e p⟩
    apply (c.mem_active_iff _).mpr
    change p.velocity 0 ∈ normalizedActive at hp
    simpa only [Clock.inverse, add_sub_cancel_left, mul_div_cancel_left₀ _
      (ne_of_gt c.positive)] using hp

/-- Velocity in the active interval differs from the centre by less than half its size. -/
theorem Clock.active_distance (c : Clock) {v : ℝ} (hv : v ∈ c.active) :
    |v - c.vbar| < |c.vbar| / 2 := by
  have hp : 0 < |c.vbar| := abs_pos.mpr c.nonzero
  have hh : |v - c.vbar| < 3 * c.r / 4 := by
    rw [abs_lt]
    exact ⟨by linarith only [hv.1], by linarith only [hv.2]⟩
  linarith only [hh, c.radius]

/-- The two source absolute-velocity bounds on the active interval. -/
theorem Clock.active_abs_bounds (c : Clock) {v : ℝ} (hv : v ∈ c.active) :
    |c.vbar| / 2 ≤ |v| ∧ |v| ≤ 3 * |c.vbar| / 2 := by
  have hd := c.active_distance hv
  have h1 := abs_sub_abs_le_abs_sub c.vbar v
  have ht := abs_add_le (v - c.vbar) c.vbar
  rw [sub_add_cancel] at ht
  rw [abs_sub_comm] at h1
  constructor <;> linarith only [hd, h1, ht]

/-- Active velocities have the sign of the nonzero centre. -/
theorem Clock.active_sign (c : Clock) {v : ℝ} (hv : v ∈ c.active) :
    Real.sign v = Real.sign c.vbar := by
  have hd := c.active_distance hv
  rcases lt_or_gt_of_ne c.nonzero with hn | hp
  · have hvn : v < 0 := by
      rw [abs_of_neg hn] at hd
      have hh := (abs_lt.mp hd).2
      linarith only [hh, hn]
    rw [Real.sign_of_neg hvn, Real.sign_of_neg hn]
  · have hvp : 0 < v := by
      rw [abs_of_pos hp] at hd
      have hh := (abs_lt.mp hd).1
      linarith only [hh, hp]
    rw [Real.sign_of_pos hvp, Real.sign_of_pos hp]

/-- The affine clock is continuous for the existing physical topology. -/
theorem Clock.continuous_map (c : Clock) (e : Point) : Continuous (c.map e) := by
  have hx : Continuous (fun p : Point => p.position 0) :=
    (continuous_apply 0).comp continuous_position
  have hv : Continuous (fun p : Point => p.velocity 0) :=
    (continuous_apply 0).comp continuous_velocity
  exact KineticPoint.continuous_mk
    ((hx.sub continuous_const).div_const _)
    (continuous_pi fun _ =>
      ((hx.sub continuous_const).sub (continuous_const.mul
        (continuous_time.sub continuous_const))).div_const _)
    (continuous_pi fun _ => (hv.sub continuous_const).div_const _)

/-- The inverse affine clock is continuous too. -/
theorem Clock.continuous_inverse (c : Clock) (e : Point) : Continuous (c.inverse e) := by
  have hx : Continuous (fun p : Point => p.position 0) :=
    (continuous_apply 0).comp continuous_position
  have hv : Continuous (fun p : Point => p.velocity 0) :=
    (continuous_apply 0).comp continuous_velocity
  exact KineticPoint.continuous_mk
    ((continuous_const.add (continuous_const.mul continuous_time)).sub
      (continuous_const.mul hx))
    (continuous_pi fun _ => continuous_const.add (continuous_const.mul continuous_time))
    (continuous_pi fun _ => continuous_const.add (continuous_const.mul hv))

/-- The clock homeomorphism uses the same maps as the algebraic inverse theorem. -/
def Clock.homeomorph (c : Clock) (e : Point) : Point ≃ₜ Point where
  toEquiv := c.equiv e
  continuous_toFun := c.continuous_map e
  continuous_invFun := c.continuous_inverse e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
