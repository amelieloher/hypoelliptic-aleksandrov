module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import Mathlib.Tactic

/-! # Exact product-box volumes and quantitative shell estimates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Round product boxes are open. -/
theorem isOpen_roundBox (d : ℕ) (a b R : ℝ) : IsOpen (roundBox d a b R) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (((PDE.isOpen_euclideanBall 0 R).preimage continuous_position).inter
        ((PDE.isOpen_euclideanBall 0 1).preimage continuous_velocity)))

/-- The unit cylinder is the round unit product box. -/
theorem unitCylinder_eq_roundBox (d : ℕ) : unitCylinder d = roundBox d (-1) 0 1 := by
  ext X
  rw [mem_unitCylinder_iff]
  simp only [roundBox, mem_ofPred_eq,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_comm))

/-- Exact volume of a product box in the coordinate measure. -/
theorem volume_roundBox (d : ℕ) (a b : ℝ) {R : ℝ} (hR : 0 < R) :
    volume (roundBox d a b R) = ENNReal.ofReal (b-a)*ENNReal.ofReal (R^d)*
      volume (unitCylinder d) := by
  let s := Ioo a b ×ˢ (PDE.euclideanBall (0 : PDE.Vec d) R ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) 1)
  have hs : MeasurableSet s := measurableSet_Ioo.prod
    ((PDE.measurableSet_euclideanBall _ _).prod (PDE.measurableSet_euclideanBall _ _))
  have heq : roundBox d a b R = (KineticPoint.equivProd d) ⁻¹' s := by
    ext X
    simp only [roundBox, s, mem_preimage, mem_prod, mem_Ioo, mem_ofPred_eq,
      KineticPoint.equivProd, Equiv.coe_fn_mk, and_assoc]
  have hunit : volume (unitCylinder d) =
      volume (PDE.euclideanBall (0 : PDE.Vec d) 1)*
        volume (PDE.euclideanBall (0 : PDE.Vec d) 1) := by
    rw [unitCylinder, volume_cylinder_product _ zero_lt_one]
    simp only [one_pow, ENNReal.ofReal_one, one_mul]
  rw [heq, (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet]
  rw [show s = Ioo a b ×ˢ (PDE.euclideanBall (0 : PDE.Vec d) R ×ˢ
    PDE.euclideanBall (0 : PDE.Vec d) 1) from rfl]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioo, PDE.volume_euclideanBall_eq_unit_mul_of_pos _ hR, hunit]
  ring

/-- Finite volume of every positive-radius product box. -/
theorem volume_roundBox_ne_top (d : ℕ) (a b : ℝ) {R : ℝ} (hR : 0 < R) :
    volume (roundBox d a b R) ≠ ⊤ := by
  rw [volume_roundBox d a b hR]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (volume_cylinder_pos_ne_top _ zero_lt_one).2

/-- Real volume formula for a nonempty round product box. -/
theorem volume_roundBox_toReal (d : ℕ) {a b R : ℝ} (hab : a ≤ b) (hR : 0 < R) :
    (volume (roundBox d a b R)).toReal = (b-a)*R^d*(volume (unitCylinder d)).toReal := by
  rw [volume_roundBox d a b hR, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), ENNReal.toReal_ofReal (by positivity)]

/-- Convex chord bound for the particular polynomial controlling spatial leakage. -/
theorem one_add_four_mul_pow_le (d : ℕ) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    (1+4*h)^d ≤ 1+((5 : ℝ)^d-1)*h := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ]
    have hpow : 1 ≤ (5 : ℝ)^d := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right ih (by positivity : 0 ≤ 1+4*h)
    have hs : h^2 ≤ h := by nlinarith
    nlinarith

/-- Linear excess volume of the stack envelope for h between zero and one. -/
theorem leakage_envelope_volume {d : ℕ} {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    (volume (roundBox d (-1) h (1+4*h))).toReal ≤
      (volume (unitCylinder d)).toReal+
        (2*(5 : ℝ)^d)*(volume (unitCylinder d)).toReal*h := by
  rw [volume_roundBox_toReal d (by linarith) (by positivity)]
  have hp := one_add_four_mul_pow_le d h0.le h1
  have hv := ENNReal.toReal_nonneg (a := volume (unitCylinder d))
  have hpow : 1 ≤ (5 : ℝ)^d := one_le_pow₀ (by norm_num)
  have hs : h^2 ≤ h := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ h-(-1))
  have hpoly : (h-(-1))*(1+4*h)^d ≤ 1+2*(5 : ℝ)^d*h := by nlinarith
  nlinarith only [mul_le_mul_of_nonneg_right hpoly hv]

/-- Bernoulli's lower bound for the inner spatial radius. -/
theorem one_sub_pow_lower (d : ℕ) {z : ℝ} (_hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1-(d : ℝ)*z ≤ (1-z)^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    push_cast
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hz1)
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith [mul_nonneg hd (sq_nonneg z)]

/-- Finite-volume subtraction for a null-measurable subset. -/
theorem volume_sdiff_toReal_of_subset {d : ℕ} {A B : Set (KineticPoint d)}
    (hB : NullMeasurableSet B volume) (hBA : B ⊆ A) (hA : volume A ≠ ⊤) :
    (volume (A \ B)).toReal = (volume A).toReal-(volume B).toReal := by
  have hBn : volume B ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono hBA)
  have hDn : volume (A \ B) ≠ ⊤ := ne_top_of_le_ne_top hA (measure_mono sdiff_subset)
  have hs := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) A hB)
  rw [inter_eq_right.mpr hBA, ENNReal.toReal_add hBn hDn] at hs
  linarith

/-- The spatial core whose complement is charged in the critical-cylinder proof. -/
def spatialCore (d : ℕ) (R : ℝ) : Set (KineticPoint d) := roundBox d (-1) 0 (1-2*R^2)

/-- The spatial core is contained in the unit cylinder for small positive cutoff. -/
theorem spatialCore_subset_unit (d : ℕ) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1/4) :
    spatialCore d R ⊆ unitCylinder d := by
  have hrad : 0 < 1-2*R^2 := by nlinarith
  intro X hX
  apply (mem_unitCylinder_iff X).mpr
  refine ⟨hX.1, hX.2.1, ?_, ?_⟩
  · simpa only [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
      using hX.2.2.2
  · have hp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrad).mp hX.2.2.1
    rw [sub_zero] at hp
    nlinarith [sq_nonneg R]

/-- The excluded spatial layer costs at most twice dimension times unit volume times R². -/
theorem spatial_shell_volume (d : ℕ) {R : ℝ} (hR : 0 < R) (hRsmall : R ≤ 1/4) :
    (volume (unitCylinder d \ spatialCore d R)).toReal ≤
      2*(d : ℝ)*(volume (unitCylinder d)).toReal*R^2 := by
  have hrad : 0 < 1-2*R^2 := by nlinarith
  have hcore : NullMeasurableSet (spatialCore d R) volume :=
    (isOpen_roundBox d (-1) 0 (1-2*R^2)).measurableSet.nullMeasurableSet
  rw [volume_sdiff_toReal_of_subset hcore
    (spatialCore_subset_unit d hR hRsmall)
    (volume_cylinder_pos_ne_top _ zero_lt_one).2]
  rw [spatialCore, volume_roundBox_toReal d (by norm_num) hrad]
  have hp := one_sub_pow_lower d (by positivity : 0 ≤ 2*R^2)
    (by nlinarith : 2*R^2 ≤ 1)
  have hv := ENNReal.toReal_nonneg (a := volume (unitCylinder d))
  nlinarith only [mul_le_mul_of_nonneg_right hp hv]

/-- Q is contained in the positive-height leakage envelope. -/
theorem unit_subset_leakage_envelope (d : ℕ) {h : ℝ} (h0 : 0 < h) :
    unitCylinder d ⊆ roundBox d (-1) h (1+4*h) := by
  intro X hX
  obtain ⟨htlo, hthi, hv, hx⟩ := (mem_unitCylinder_iff X).mp hX
  refine ⟨htlo, hthi.trans h0, ?_, ?_⟩
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]
    linarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
    exact hv

/-- Linear volume bound for the portion of the leakage envelope outside Q. -/
theorem leakage_shell_volume (d : ℕ) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    (volume (roundBox d (-1) h (1+4*h) \ unitCylinder d)).toReal ≤
      2*(5 : ℝ)^d*(volume (unitCylinder d)).toReal*h := by
  have hQ : NullMeasurableSet (unitCylinder d) volume :=
    (isOpen_cylinder _ _).measurableSet.nullMeasurableSet
  rw [volume_sdiff_toReal_of_subset hQ
    (unit_subset_leakage_envelope d h0)
    (volume_roundBox_ne_top d (-1) h (by positivity))]
  have hb := leakage_envelope_volume (d := d) h0 h1
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
