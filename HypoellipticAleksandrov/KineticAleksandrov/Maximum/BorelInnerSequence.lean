module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # A concrete reflected inner-cylinder exhaustion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/-- A valid inner error scale for every natural index, starting at zero. -/
def borelInnerDelta (R : ℝ) (n : ℕ) : ℝ := R ^ 2 / (4 * ((n : ℝ) + 1))

/-- Every scale is positive and below half the original time depth. -/
theorem borelInnerDelta_valid (R : ℝ) (hR : 0 < R) (n : ℕ) :
    0 < borelInnerDelta R n ∧ borelInnerDelta R n < R ^ 2 / 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < 4 * ((n : ℝ) + 1) := by positivity
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  refine ⟨div_pos hR2 hd,?_⟩
  rw [borelInnerDelta,div_lt_iff₀ hd]
  nlinarith only [hn,hR2]

/-- The scale tends to zero with the centre and original radius fixed. -/
theorem borelInnerDelta_tendsto (R : ℝ) :
    Tendsto (borelInnerDelta R) atTop (𝓝 0) := by
  have heq : borelInnerDelta R = fun (n : ℕ) => R ^ 2 / 4 * (1 / ((n : ℝ) + 1)) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [borelInnerDelta]
    field_simp
  rw [heq]
  convert! tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R ^ 2 / 4) using 1
  simp only [mul_zero]

/-- Radius of the concrete reflected inner cylinder. -/
def borelInnerRadius (R : ℝ) (hR : 0 < R) (n : ℕ) : ℝ :=
  innerRatio R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2 * R

/-- Positivity holds at every index, without discarding the first cylinder. -/
theorem borelInnerRadius_pos (R : ℝ) (hR : 0 < R) (n : ℕ) :
    0 < borelInnerRadius R hR n :=
  mul_pos (innerRatio_spec R hR _ (borelInnerDelta_valid R hR n).1
    (borelInnerDelta_valid R hR n).2).1 hR

/-- The inner radii tend to the original radius, including arbitrary real powers later. -/
theorem borelInnerRadius_tendsto (R : ℝ) (hR : 0 < R) :
    Tendsto (borelInnerRadius R hR) atTop (𝓝 R) := by
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (((borelInnerDelta_tendsto R).const_mul 2).div_const (R ^ 2)))
  have ht' : Tendsto (fun n => (1 : ℝ) - 2 * borelInnerDelta R n / R ^ 2)
      atTop (𝓝 1) := by simpa only [mul_zero,zero_div,sub_zero] using ht
  have hs := (Real.continuous_sqrt.tendsto 1).comp ht'
  change Tendsto (fun n => Real.sqrt (1 - 2 * borelInnerDelta R n / R ^ 2) * R)
    atTop (𝓝 R)
  simpa only [Function.comp_def,Real.sqrt_one,one_mul] using hs.mul_const R

/-- The source shifted backward centre for the concrete sequence. -/
def borelInnerCentre {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (n : ℕ) : KineticPoint d :=
  ⟨P₀.time - borelInnerDelta R n,
    P₀.position - borelInnerDelta R n • P₀.velocity,P₀.velocity⟩

/-- Every backward interior point eventually lies in the shifted inner cylinders. -/
theorem borel_inner_exhaustion {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (P : KineticPoint d) (hP : P ∈ backwardCylinder P₀ R) :
    ∀ᶠ n in atTop, P ∈ backwardCylinder (borelInnerCentre P₀ R n) (borelInnerRadius R hR n) := by
  have hP' : kineticReflection P ∈ forwardCylinder (kineticReflection P₀) R hR := by
    rw [← kineticReflection_image_backwardCylinder P₀ R hR]
    exact mem_image_of_mem _ hP
  obtain ⟨η,hη,hmem⟩ := innerCylinder_exhaustion (kineticReflection P₀) R hR
    (kineticReflection P) hP'
  have hsmall := (tendsto_order.mp (borelInnerDelta_tendsto R)).2 η hη
  filter_upwards [hsmall] with n hn
  have hm := hmem (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2 hn
  change P ∈ backwardCylinder
    ⟨P₀.time - borelInnerDelta R n,P₀.position - borelInnerDelta R n • P₀.velocity,
      P₀.velocity⟩ (borelInnerRadius R hR n)
  unfold borelInnerRadius
  rw [← kineticReflection_image_innerCylinder P₀ R hR (borelInnerDelta R n)
    (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2]
  exact ⟨kineticReflection P,hm,kineticReflection_involutive P⟩

end HypoellipticAleksandrov.KineticAleksandrov
