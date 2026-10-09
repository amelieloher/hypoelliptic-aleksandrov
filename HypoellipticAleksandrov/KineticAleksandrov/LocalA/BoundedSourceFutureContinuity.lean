module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceHomogeneousLimit
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceL2Convergence
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! # Pointwise continuity of bounded future potentials on compact collars

The starting measure is volume on the collar plus a Dirac mass at the chosen point. The
actual source approximation therefore gives both L2 convergence and that point's value.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- A positive bounded source supported strictly in the future gives a continuous literal
potential on every compact regular collar lying strictly before the source starts. -/
theorem continuousOn_duhamelFuture_compact_collar
    (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (a s T : ℝ) (has : a ≤ s) (hsT : s ≤ T)
    (U C : Set (EvolutionVec d)) (hU : IsOpen U) (hC : IsCompact C)
    (hCi : C ⊆ closure (interior C)) (hCU : C ⊆ U)
    [IsFiniteMeasure (volume.restrict U)]
    (hUpast : U ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
    (hUfloor : ∀ z ∈ U, a ≤ (evolutionHomeomorph d z).time)
    (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
    ContinuousOn (duhamelPotential K T F ∘ evolutionHomeomorph d) C := by
  classical
  let P := evolutionHomeomorph d
  let u := duhamelPotential K T F ∘ P
  let μ := volume.restrict U
  have hzero : ∀ p : KineticPoint d, p.time < s → F p = 0 := by
    intro p hp
    apply hFz p
    intro h
    exact (not_lt_of_gt hp) h.1
  have hweak := duhamelPotential_weak_before_source hΩa hΩ hγ B b S K hreal hB hBs hb
    F hF M hM (fun p => by rw [abs_of_nonneg (hFb p).1]; exact (hFb p).2)
    s T hsT hzero
  have hw := boundedSource_ambientWeak_restrict hUpast B b u hweak
  have hbound (g : KineticPoint d → ℝ) (Cg : ℝ) (hCg : 0 ≤ Cg)
      (hgb : ∀ p, |g p| ≤ Cg) : ∀ z ∈ U,
      |duhamelPotential K T g (P z)| ≤ (T - a) * Cg := by
    intro z hz
    have hzT : (P z).time ≤ T := (hUpast hz).1.le.trans hsT
    exact (abs_duhamelPotential_le K g Cg hCg hgb (P z) T hzT).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_left (hUfloor z hz) T) hCg)
  have hum : Measurable u := (measurable_duhamelPotential K hΩ hγ T F hF).comp P.measurable
  have hub : ∀ᵐ z ∂μ, |u z| ≤ (T - a) * (M + 2) := by
    apply ae_restrict_of_forall_mem hU.measurableSet
    intro z hz
    exact hbound F (M + 2) (by linarith) (fun p => by
      rw [abs_of_nonneg (hFb p).1]; linarith [(hFb p).2]) z hz
  have hu : MemLp u 2 μ := MemLp.of_bound hum.aestronglyMeasurable.restrict
    ((T - a) * (M + 2)) (by simpa only [Real.norm_eq_abs] using hub)
  obtain ⟨v, hvc, hve, hidentify⟩ :=
    exists_continuousRepresentative_identified_by_homogeneous_limits hH B b hB hb
      lam Lam m hlam hm hell hcoerc U C hU hC hCi hCU u hu hw
  have heq : EqOn u v C := by
    intro z hz
    let ν : Measure (KineticPoint d) := μ.map P + Measure.dirac (P z)
    have hfloor : ∀ᵐ p ∂ν, a ≤ p.time := by
      apply ae_add_measure_iff.mpr
      refine ⟨?_, ?_⟩
      · apply (ae_map_iff P.measurable.aemeasurable
          (measurableSet_le measurable_const continuous_time.measurable)).2
        exact ae_restrict_of_forall_mem hU.measurableSet hUfloor
      · simpa only [ae_dirac_eq, eventually_pure] using hUfloor z (hCU hz)
    obtain ⟨f, hfm, hfb, hfc, hfw, hlim⟩ := exists_duhamelFuture_approximating_sequence
      hΩa hΩ hγ B b S K hreal hB hBs hb a s T hsT ν hfloor F hF M hM hFb hFz
    let fn (n : ℕ) := duhamelPotential K T (f n) ∘ P
    have hfnm (n : ℕ) : Measurable (fn n) :=
      (measurable_duhamelPotential K hΩ hγ T (f n) (hfm n)).comp P.measurable
    have hfnb (n : ℕ) : ∀ᵐ w ∂μ, |fn n w| ≤ (T - a) * (M + 2) := by
      apply ae_restrict_of_forall_mem hU.measurableSet
      exact hbound (f n) (M + 2) (by linarith) (fun p => by
        rw [abs_of_nonneg (hfb n p).1]; exact (hfb n p).2)
    have hfn (n : ℕ) : MemLp (fn n) 2 μ :=
      MemLp.of_bound (hfnm n).aestronglyMeasurable.restrict ((T - a) * (M + 2))
        (by simpa only [Real.norm_eq_abs] using hfnb n)
    have hconv := ae_add_measure_iff.mp hlim
    have hae : ∀ᵐ w ∂μ, Tendsto (fun n => fn n w) atTop (𝓝 (u w)) :=
      ae_of_ae_map P.measurable.aemeasurable hconv.1
    have hp : Tendsto (fun n => fn n z) atTop (𝓝 (u z)) := by
      simpa only [ae_dirac_eq, eventually_pure, fn, u, Function.comp_def] using hconv.2
    have hstrong := tendsto_toLp_two_of_bounded_ae μ fn u hfn hu
      ((T - a) * (M + 2)) (mul_nonneg (sub_nonneg.mpr (has.trans hsT)) (by linarith))
      hfnb hub hae
    have hfnc (n : ℕ) : ContinuousOn (fn n) U :=
      (hfc n).comp P.continuous.continuousOn (fun w hw =>
        ⟨(hUpast hw).1.le.trans hsT, subset_closure (hUpast hw).2⟩)
    have hfnw (n : ℕ) := boundedSource_ambientWeak_restrict hUpast B b (fn n) (hfw n)
    exact hidentify fn hfn hfnc hfnw hstrong z hz hp
  exact (hvc.mono hCU).congr (fun z hz => heq hz)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
