module

public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff

/-!
# Global extension of cutoff-selected parabolic weak jets

This module transports all selected representatives of a compactly cutoff
local weak jet to the full time--velocity space.  The transport uses the
actual support of every product representative; it is not a generic extension
operator.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal Topology

private theorem timeDerivative_tsupport {d : ℕ} (f : TimeVelocity d → ℝ) :
    tsupport (timeDerivative f) ⊆ tsupport f := by
  unfold timeDerivative
  change closure (Function.support (fun z => fderiv ℝ f z (1, 0))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityGradient_tsupport {d : ℕ} {i : Fin d}
    (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support (fun z => fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem velocityHessian_tsupport {d : ℕ} {i j : Fin d}
    (f : TimeVelocity d → ℝ) :
    tsupport (fun z => velocityHessian f z i j) ⊆ tsupport f := by
  refine closure_minimal ?_ (isClosed_tsupport (f := f))
  intro z hz
  rw [Function.mem_support] at hz
  by_contra hzero
  have hzero' : f =ᶠ[𝓝 z] fun _ : TimeVelocity d => (0 : ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hzero
  apply hz
  unfold velocityHessian
  rw [hzero'.fderiv.fderiv_eq, fderiv_fun_const]
  simp

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_timeDeriv_subset {d : ℕ}
    (b u du : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * du z + u z * timeDerivative b z) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_right (f := u) (g := timeDerivative b)).trans
      (timeDerivative_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_velocityGrad_subset {d : ℕ} {i : Fin d}
    (b u dui : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * dui z + u z * velocityGradient b z i) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_right (f := u) (g := fun z => velocityGradient b z i)).trans
      (velocityGradient_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem tsupport_mul_velocityHessian_subset {d : ℕ} {i j : Fin d}
    (b u dui duj duij : TimeVelocity d → ℝ) :
    tsupport (fun z => b z * duij z + velocityGradient b z j * dui z +
      duj z * velocityGradient b z i + u z * velocityHessian b z i j) ⊆ tsupport b := by
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  refine (tsupport_add _ _).trans (union_subset ?_ ?_)
  · exact tsupport_mul_subset_left
  · exact (tsupport_mul_subset_left (f := fun z => velocityGradient b z j) (g := dui)).trans
      (velocityGradient_tsupport b)
  · exact (tsupport_mul_subset_right (f := duj) (g := fun z => velocityGradient b z i)).trans
      (velocityGradient_tsupport b)
  · exact (tsupport_mul_subset_right (f := u) (g := fun z => velocityHessian b z i j)).trans
      (velocityHessian_tsupport b)

/-- Support localization for extension to the full spacetime carrier. -/
theorem parabolicMemLpOn_univ_of_support_subset
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    {f : TimeVelocity d → ℝ}
    (hU : MeasurableSet U) (hf : ParabolicMemLpOn U p f)
    (hsupp : Function.support f ⊆ U) :
    ParabolicMemLpOn Set.univ p f := by
  have hindicator : U.indicator f = f := Set.indicator_eq_self.mpr hsupp
  change MemLp f p ((volume : Measure (TimeVelocity d)).restrict Set.univ)
  rw [← hindicator, memLp_indicator_iff_restrict hU]
  simpa only [Measure.restrict_univ] using hf

/-- Support localization for extension to the full spacetime carrier. -/
theorem HasWeakTimeDerivOn.univ_of_compact_tsupport_subset
    {d : ℕ} {U K : Set (TimeVelocity d)} {u du : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakTimeDerivOn U u du)
    (huK : tsupport u ⊆ K) (hduK : tsupport du ⊆ K) :
    HasWeakTimeDerivOn Set.univ u du := by
  intro φ hφ hφCompact _
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  obtain ⟨O, hOOpen, hKO, haO⟩ := eventually_nhdsSet_iff_exists.mp haOne
  have haφ : ContDiff ℝ (⊤ : ℕ∞) (a * φ) := ha.mul hφ
  have haφCompact : HasCompactSupport (a * φ) := by
    simpa only [Pi.mul_def] using hφCompact.mul_left (f := a)
  have haφU : tsupport (a * φ) ⊆ U :=
    (tsupport_mul_subset_left (f := a) (g := φ)).trans haU
  have hlocal := hu (a * φ) haφ haφCompact haφU
  have hleft : EqOn (fun z => u z * timeDerivative φ z)
      (fun z => u z * timeDerivative (a * φ) z) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp only [Pi.mul_apply, haO y hy, one_mul]
      have hderiv : timeDerivative (a * φ) z = timeDerivative φ z := by
        unfold timeDerivative
        rw [hza.fderiv_eq]
      exact congrArg (fun r => u z * r) hderiv.symm
    · have huzero : u z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun htz => hzK (huK htz))
      simp [huzero]
  have hright : EqOn (fun z => du z * φ z) (fun z => du z * (a * φ) z) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp only [Pi.mul_apply, haO y hy, one_mul]
      exact congrArg (fun r => du z * r) hza.eq_of_nhds.symm
    · have hduzero : du z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun htz => hzK (hduK htz))
      simp [hduzero]
  have hvalueZero : ∀ z, z ∉ U → u z * timeDerivative φ z = 0 := by
    intro z hzU
    have huzero : u z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (huK htz)))
    simp [huzero]
  have hderivZero : ∀ z, z ∉ U → du z * φ z = 0 := by
    intro z hzU
    have hduzero : du z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (hduK htz)))
    simp [hduzero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvalueZero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hderivZero,
    setIntegral_congr_fun hU.measurableSet hleft,
    setIntegral_congr_fun hU.measurableSet hright]
  simpa only [Measure.restrict_univ] using hlocal

/-- Support localization for extension to the full spacetime carrier. -/
theorem HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset
    {d : ℕ} {U K : Set (TimeVelocity d)} {i : Fin d}
    {u dui : TimeVelocity d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : HasWeakVelocityPartialDerivOn U i u dui)
    (huK : tsupport u ⊆ K) (hduiK : tsupport dui ⊆ K) :
    HasWeakVelocityPartialDerivOn Set.univ i u dui := by
  intro φ hφ hφCompact _
  obtain ⟨a, ha, haOne, haU⟩ := exists_smooth_cutoff_tsupport_subset hK hU hKU
  obtain ⟨O, hOOpen, hKO, haO⟩ := eventually_nhdsSet_iff_exists.mp haOne
  have haφ : ContDiff ℝ (⊤ : ℕ∞) (a * φ) := ha.mul hφ
  have haφCompact : HasCompactSupport (a * φ) := by
    simpa only [Pi.mul_def] using hφCompact.mul_left (f := a)
  have haφU : tsupport (a * φ) ⊆ U :=
    (tsupport_mul_subset_left (f := a) (g := φ)).trans haU
  have hlocal := hu (a * φ) haφ haφCompact haφU
  have hleft : EqOn (fun z => u z * velocityGradient φ z i)
      (fun z => u z * velocityGradient (a * φ) z i) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp only [Pi.mul_apply, haO y hy, one_mul]
      have hderiv : velocityGradient (a * φ) z i = velocityGradient φ z i := by
        unfold velocityGradient
        rw [hza.fderiv_eq]
      exact congrArg (fun r => u z * r) hderiv.symm
    · have huzero : u z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun htz => hzK (huK htz))
      simp [huzero]
  have hright : EqOn (fun z => dui z * φ z) (fun z => dui z * (a * φ) z) U := by
    intro z hzU
    by_cases hzK : z ∈ K
    · have hza : a * φ =ᶠ[𝓝 z] φ := by
        filter_upwards [hOOpen.mem_nhds (hKO hzK)] with y hy
        simp only [Pi.mul_apply, haO y hy, one_mul]
      exact congrArg (fun r => dui z * r) hza.eq_of_nhds.symm
    · have hduizero : dui z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun htz => hzK (hduiK htz))
      simp [hduizero]
  have hvalueZero : ∀ z, z ∉ U → u z * velocityGradient φ z i = 0 := by
    intro z hzU
    have huzero : u z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (huK htz)))
    simp [huzero]
  have hderivZero : ∀ z, z ∉ U → dui z * φ z = 0 := by
    intro z hzU
    have hduizero : dui z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun htz => hzU (hKU (hduiK htz)))
    simp [hduizero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvalueZero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hderivZero,
    setIntegral_congr_fun hU.measurableSet hleft,
    setIntegral_congr_fun hU.measurableSet hright]
  simpa only [Measure.restrict_univ] using hlocal

namespace ParabolicW12Function

/-- A selected weak jet multiplied by an actual smooth compact cutoff supported
in its open domain is a global selected weak jet. -/
noncomputable def mulContDiffHasCompactSupport_univ
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    ParabolicW12Function d Set.univ p := by
  let jet := w.mulContDiffHasCompactSupport hp hb hbCompact
  have hKCompact : IsCompact (tsupport b) := hbCompact
  have hvalueK : tsupport jet.toFun ⊆ tsupport b := by
    simpa only [jet, mulContDiffHasCompactSupport_toFun] using
      (tsupport_mul_subset_left (f := b) (g := w.toFun))
  have htimeK : tsupport jet.timeDeriv ⊆ tsupport b := by
    simpa only [jet, mulContDiffHasCompactSupport_timeDeriv] using
      (tsupport_mul_timeDeriv_subset b w.toFun w.timeDeriv)
  have hgradK : ∀ i : Fin d, tsupport (fun z => jet.velocityGrad z i) ⊆ tsupport b := by
    intro i
    simpa only [jet, mulContDiffHasCompactSupport_velocityGrad] using
      (tsupport_mul_velocityGrad_subset (i := i) b w.toFun (fun z => w.velocityGrad z i))
  have hhessianK : ∀ i j : Fin d,
      tsupport (fun z => jet.velocityHessian z i j) ⊆ tsupport b := by
    intro i j
    simpa only [jet, mulContDiffHasCompactSupport_velocityHessian] using
      (tsupport_mul_velocityHessian_subset (i := i) (j := j) b w.toFun
        (fun z => w.velocityGrad z i) (fun z => w.velocityGrad z j)
        (fun z => w.velocityHessian z i j))
  refine
    { toFun := jet.toFun
      timeDeriv := jet.timeDeriv
      velocityGrad := jet.velocityGrad
      velocityHessian := jet.velocityHessian
      memLp := parabolicMemLpOn_univ_of_support_subset hU.measurableSet jet.memLp
        (subset_closure.trans (hvalueK.trans hbU))
      timeDeriv_memLp := parabolicMemLpOn_univ_of_support_subset hU.measurableSet
        jet.timeDeriv_memLp (subset_closure.trans (htimeK.trans hbU))
      velocityGrad_memLp := fun i => parabolicMemLpOn_univ_of_support_subset hU.measurableSet
        (jet.velocityGrad_memLp i)
          (subset_closure.trans ((hgradK i).trans hbU))
      velocityHessian_memLp := fun i j =>
        parabolicMemLpOn_univ_of_support_subset hU.measurableSet
          (jet.velocityHessian_memLp i j)
          (subset_closure.trans ((hhessianK i j).trans hbU))
      hasWeakTimeDeriv := HasWeakTimeDerivOn.univ_of_compact_tsupport_subset hU hKCompact hbU
        jet.hasWeakTimeDeriv hvalueK htimeK
      hasWeakVelocityPartialDeriv := fun i =>
        HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset hU hKCompact hbU
          (jet.hasWeakVelocityPartialDeriv i) hvalueK (hgradK i)
      hasWeakVelocitySecondPartialDeriv := fun i j =>
        HasWeakVelocityPartialDerivOn.univ_of_compact_tsupport_subset hU hKCompact hbU
          (jet.hasWeakVelocitySecondPartialDeriv i j) (hgradK i) (hhessianK i j) }

/-- Value representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_toFun
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).toFun =
      fun z => b z * w.toFun z := rfl

/-- Time-derivative representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_timeDeriv
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).timeDeriv =
      fun z => b z * w.timeDeriv z + w.toFun z * timeDerivative b z := rfl

/-- Velocity-gradient representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_velocityGrad
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).velocityGrad =
      fun z i => b z * w.velocityGrad z i + w.toFun z * velocityGradient b z i := rfl

/-- Ordered velocity-Hessian representative of the global cutoff-product jet. -/
@[simp] theorem mulContDiffHasCompactSupport_univ_velocityHessian
    {d : ℕ} {U : Set (TimeVelocity d)} {p : ℝ≥0∞}
    (w : ParabolicW12Function d U p) (hp : 1 ≤ p)
    {b : TimeVelocity d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbCompact : HasCompactSupport b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) :
    (w.mulContDiffHasCompactSupport_univ hp hb hbCompact hU hbU).velocityHessian =
      fun z i j => b z * w.velocityHessian z i j + velocityGradient b z j * w.velocityGrad z i +
        w.velocityGrad z j * velocityGradient b z i + w.toFun z *
          HypoellipticAleksandrov.Parabolic.velocityHessian b z i j := rfl

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
