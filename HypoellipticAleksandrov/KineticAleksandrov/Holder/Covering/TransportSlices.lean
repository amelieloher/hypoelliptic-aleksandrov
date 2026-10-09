module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic

/-! # Volume-preserving transport coordinates and cylinder slices -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Transport coordinates ordered as velocity, transported position, time. -/
def transportChart {d : ℕ} (z : PDE.Vec d × (PDE.Vec d × ℝ)) : KineticPoint d :=
  ⟨z.2.2, z.2.1+z.2.2 • z.1, z.1⟩

/-- The transport chart is continuous. -/
theorem continuous_transportChart (d : ℕ) : Continuous (@transportChart d) := by
  apply KineticPoint.continuous_mk <;> fun_prop

/-- At fixed velocity, time-dependent position translation preserves product volume. -/
theorem measurePreserving_transport_fiber {d : ℕ} (v : PDE.Vec d) :
    MeasurePreserving (fun z : PDE.Vec d × ℝ => (z.2, z.1+z.2 • v)) volume volume := by
  have h : MeasurePreserving (fun z : ℝ × PDE.Vec d => (z.1, z.2+z.1 • v))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun t x => x+t • v) ?_ ?_
    · exact (continuous_snd.add (continuous_fst.smul continuous_const)).measurable
    · exact Filter.Eventually.of_forall fun t =>
        (measurePreserving_add_right (volume : Measure (PDE.Vec d)) (t • v)).map_eq
  simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.swap,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using
    h.comp (Measure.measurePreserving_swap (μ := (volume : Measure (PDE.Vec d)))
      (ν := (volume : Measure ℝ)))

/-- The full transport chart preserves kinetic volume, with Jacobian one. -/
theorem measurePreserving_transportChart (d : ℕ) :
    MeasurePreserving (@transportChart d) volume volume := by
  have hshear : MeasurePreserving
      (fun z : PDE.Vec d × (PDE.Vec d × ℝ) => (z.1, z.2.2, z.2.1+z.2.2 • z.1))
      ((volume : Measure (PDE.Vec d)).prod volume)
      ((volume : Measure (PDE.Vec d)).prod volume) := by
    refine (MeasurePreserving.id (volume : Measure (PDE.Vec d))).skew_product
      (g := fun (v : PDE.Vec d) (z : PDE.Vec d × ℝ) => (z.2, z.1+z.2 • v)) ?_ ?_
    · exact (continuous_snd.snd.prodMk
        (continuous_snd.fst.add (continuous_snd.snd.smul continuous_fst))).measurable
    · exact Filter.Eventually.of_forall fun v => (measurePreserving_transport_fiber v).map_eq
  have hperm : MeasurePreserving
      (fun z : PDE.Vec d × (ℝ × PDE.Vec d) => (z.2.1, z.2.2, z.1)) volume volume := by
    simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.swap,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using
      (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure (PDE.Vec d))
        (volume : Measure (PDE.Vec d))).comp
        (Measure.measurePreserving_swap (μ := (volume : Measure (PDE.Vec d)))
          (ν := (volume : Measure (ℝ × PDE.Vec d))))
  have hinv : MeasurePreserving (KineticPoint.equivProd d).symm volume volume :=
    ⟨KineticPoint.measurable_equivProd_symm d, rfl⟩
  change MeasurePreserving
    (fun z : PDE.Vec d × (PDE.Vec d × ℝ) =>
      KineticPoint.mk z.2.2 (z.2.1+z.2.2 • z.1) z.1) _ _
  simpa only [Measure.volume_eq_prod, Function.comp_def, transportChart,
    KineticPoint.equivProd, Equiv.coe_fn_symm_mk] using hinv.comp (hperm.comp hshear)

/-- Backward transport slices fit in a fixed transported position ball of radius 2r³. -/
theorem cylinder_transport_slice {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (v y : PDE.Vec d) (t : ℝ)
    (h : transportChart (v, y, t) ∈ backwardCylinder P r) :
    t ∈ Ioo (P.time-r^2) P.time ∧ v ∈ PDE.euclideanBall P.velocity r ∧
      y ∈ PDE.euclideanBall (P.position-P.time • v) (2*r^3) := by
  refine ⟨⟨h.1, h.2.1⟩, h.2.2.1, ?_⟩
  have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp h.2.2.1
  have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp h.2.2.2
  rw [sub_zero] at hx
  change PDE.vecEuclideanNorm (v-P.velocity) < r at hv
  have htime₁ : P.time-r^2 < t := h.1
  have htime₂ : t < P.time := h.2.1
  have ht : |t-P.time| < r^2 := by
    rw [abs_lt]
    constructor <;> linarith only [htime₁, htime₂]
  have heq : y-(P.position-P.time • v) = relativePosition P (transportChart (v,y,t))-
      (t-P.time) • (v-P.velocity) := by
    ext i
    simp only [relativePosition, transportChart, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < 2*r^3), heq]
  have hn := PDE.vecEuclideanNorm_add_le (relativePosition P (transportChart (v,y,t)))
    (-((t-P.time) • (v-P.velocity)))
  rw [PDE.vecEuclideanNorm_neg, PDE.vecEuclideanNorm_smul] at hn
  rw [sub_eq_add_neg]
  have hm := mul_le_mul ht.le hv.le (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
  nlinarith

/-- The delayed transport product is contained in the forward stack. -/
theorem delayed_transport_slice {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (v y : PDE.Vec d) (t : ℝ)
    (ht : t ∈ Ioo P.time (P.time+(m : ℝ)*r^2))
    (hv : v ∈ PDE.euclideanBall P.velocity r)
    (hy : y ∈ PDE.euclideanBall (P.position-P.time • v) (2*r^3)) :
    transportChart (v,y,t) ∈ forwardStack P r m := by
  refine ⟨by change 0 < t-P.time; linarith only [ht.1],
    by change t-P.time ≤ (m : ℝ)*r^2; linarith only [ht.2], hv, ?_⟩
  have hvn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hv
  have hyn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : 0 < 2*r^3)).mp hy
  have heq : relativePosition P (transportChart (v,y,t)) =
      (y-(P.position-P.time • v))+(t-P.time) • (v-P.velocity) := by
    ext i
    simp only [relativePosition, transportChart, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hrad : 0 < ((m+2 : ℕ) : ℝ)*r^3 := by positivity
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrad, sub_zero, heq]
  have hn := PDE.vecEuclideanNorm_add_le (y-(P.position-P.time • v))
    ((t-P.time) • (v-P.velocity))
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (sub_pos.mpr ht.1)] at hn
  have hm := mul_le_mul (by linarith only [ht.2] : t-P.time ≤ (m : ℝ)*r^2)
    hvn.le (PDE.vecEuclideanNorm_nonneg _) (by positivity : 0 ≤ (m : ℝ)*r^2)
  push_cast
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
