module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

/-!
# Weak product calculus for cutoff jets

The preliminary pairing lemma passes smooth-approximation identities to Sobolev limits.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter
open scoped ENNReal Topology

/-- Strong `L²` convergence passes scalar pairings with a fixed `L²` function to the limit. -/
theorem integral_pairing_tendsto_of_eLpNorm_two {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (F : ℕ → X → ℝ) (f g : X → ℝ)
    (hF : ∀ n, MemLp (F n) 2 mu) (hf : MemLp f 2 mu) (hg : MemLp g 2 mu)
    (hlim : Tendsto (fun n => eLpNorm (F n - f) 2 mu) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * g x ∂mu) atTop (𝓝 (∫ x, f x * g x ∂mu)) := by
  have hLp : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).2 hlim
  have he (a b : X → ℝ) (ha : MemLp a 2 mu) (hb : MemLp b 2 mu) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp only [Real.inner_apply]
  have hi := hLp.inner (𝕜 := ℝ) (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)))
  simpa only [he] using hi

/-- A Sobolev multiplier obeys the weak product rule with a function having only the
specified weak partial derivative. All three products are locally integrable by `L²`.
No smoothness of the multiplier or of the weak derivative representative is assumed. -/
theorem weakPartial_product_sobolev {d : ℕ} {D : Set (PDE.Vec d)}
    (hD : PDE.IsOpenBoundedConvexDomain D) (a : PDE.W1pFunction D 2)
    (i : Fin d) (b Db : PDE.Vec d → ℝ)
    (hb : PDE.MemLpOn D 2 b) (hDb : PDE.MemLpOn D 2 Db)
    (hweak : PDE.HasWeakPartialDerivOn D i b Db) :
    PDE.HasWeakPartialDerivOn D i (fun x => a.toFun x * b x)
      (fun x => a.toFun x * Db x + b x * a.grad x i) := by
  rcases D.eq_empty_or_nonempty with hEmpty | hNonempty
  · subst D
    intro test _ _ _
    simp only [Measure.restrict_empty, integral_zero_measure, neg_zero]
  obtain ⟨x0, r, hr, hball⟩ :=
    PDE.exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain hD hNonempty
  let mu := PDE.volumeOn D
  have : IsFiniteMeasure mu := hD.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  let A (n : ℕ) := a.convexApproxSmoothW1p hD (by norm_num) x0 hr n
  have hsmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (A n).toFun :=
    a.contDiff_convexApproxSmoothW1p_toFun hD (by norm_num) x0 hr n
  have hv := a.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    hD (by norm_num) (by norm_num) hball hr
  have hg := a.tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
    hD (by norm_num) (by norm_num) hball hr i
  intro test ht hc hsub
  let dt := fun x : PDE.Vec d => fderiv ℝ test x (PDE.basisVec i)
  have hdt : Continuous dt :=
    (ht.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcompact : HasCompactSupport dt := hc.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i)
  have top_mem (f : PDE.Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
      MemLp f ∞ mu := by
    obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf
    exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have htTop := top_mem test ht.continuous hc
  have hdtTop := top_mem dt hdt hdcompact
  have hbt : MemLp (fun x => b x * test x) 2 mu := hb.fun_mul htTop
  have hDbt : MemLp (fun x => Db x * test x) 2 mu := hDb.fun_mul htTop
  have hbdt : MemLp (fun x => b x * dt x) 2 mu := hb.fun_mul hdtTop
  have hL := integral_pairing_tendsto_of_eLpNorm_two mu
    (fun n => (A n).toFun) a.toFun (fun x => b x * dt x)
    (fun n => (A n).memLp) a.memLp hbdt hv
  have hR1 := integral_pairing_tendsto_of_eLpNorm_two mu
    (fun n => (A n).toFun) a.toFun (fun x => Db x * test x)
    (fun n => (A n).memLp) a.memLp hDbt hv
  have hR2 := integral_pairing_tendsto_of_eLpNorm_two mu
    (fun n x => (A n).grad x i) (fun x => a.grad x i) (fun x => b x * test x)
    (fun n => (A n).gradMemLp i) (a.gradMemLp i) hbt hg
  have he (n : ℕ) : (∫ x, (A n).toFun x * (b x * dt x) ∂mu) =
      -((∫ x, (A n).toFun x * (Db x * test x) ∂mu) +
        ∫ x, (A n).grad x i * (b x * test x) ∂mu) := by
    have hn := hweak.mul_contDiff (hsmooth n)
      (hb.integrable (by norm_num)).locallyIntegrable
      (hDb.integrable (by norm_num)).locallyIntegrable
    have ha := hn test ht hc hsub
    have h1 : Integrable (fun x => (A n).toFun x * (Db x * test x)) mu :=
      (memLp_one_iff_integrable.mp ((A n).memLp.mul hDbt))
    have h2 : Integrable (fun x => (A n).grad x i * (b x * test x)) mu :=
      (memLp_one_iff_integrable.mp ((A n).gradMemLp i |>.mul hbt))
    change (∫ x, ((A n).toFun x * b x) * dt x ∂mu) =
      -(∫ x, ((A n).toFun x * Db x +
        b x * fderiv ℝ (A n).toFun x (PDE.basisVec i)) * test x ∂mu) at ha
    have hj : ∀ x, fderiv ℝ (A n).toFun x (PDE.basisVec i) = (A n).grad x i := by
      intro x
      exact (a.convexApproxSmoothW1p_grad_apply hD (by norm_num) x0 hr n x i).symm
    simp_rw [hj] at ha
    rw [← integral_add h1 h2]
    simpa only [mul_add, mul_assoc, mul_comm, mul_left_comm] using! ha
  have heq := tendsto_nhds_unique hL ((hR1.add hR2).neg.congr (fun n => (he n).symm))
  have h1 : Integrable (fun x => a.toFun x * (Db x * test x)) mu :=
    memLp_one_iff_integrable.mp (a.memLp.mul hDbt)
  have h2 : Integrable (fun x => a.grad x i * (b x * test x)) mu :=
    memLp_one_iff_integrable.mp ((a.gradMemLp i).mul hbt)
  change (∫ x, (a.toFun x * b x) * dt x ∂mu) =
    -(∫ x, (a.toFun x * Db x + b x * a.grad x i) * test x ∂mu)
  rw [← integral_add h1 h2] at heq
  simpa only [mul_add, mul_assoc, mul_comm, mul_left_comm] using! heq

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
