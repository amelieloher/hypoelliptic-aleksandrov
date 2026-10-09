module

public import Mathlib.Analysis.Calculus.MeanValue
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.W1p.Closure
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density

/-!
# Bounded-derivative composition in `W^{1,p}`

This file proves the `C¹` chain rule on bounded open convex domains for every
finite exponent `p ≥ 1`.  If `|G'| ≤ M`, then

`D(G ∘ u) = G'(u) Du`

with the exact multiplier `M` in the value and gradient estimates.

The proof follows the non-circular route used later for truncations:

1. approximate `u` smoothly on the convex domain;
2. extract an almost-everywhere convergent subsequence;
3. use domination by `2 M |Du|` for the nonlinear gradient term;
4. pass to the limit through the closed `W^{1,p}` graph.

No general Lipschitz Sobolev chain rule is asserted here.  Such a theorem also
requires Stampacchia's null-preimage result at the nondifferentiability set.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- A differentiable real function with derivative bounded by `M` is
`M`-Lipschitz. -/
theorem lipschitzWith_of_abs_deriv_le
    {G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hG : Differentiable ℝ G)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    LipschitzWith M.toNNReal G := by
  apply lipschitzWith_of_nnnorm_deriv_le hG
  intro t
  rw [← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal M hM, Real.norm_eq_abs]
  exact hderiv t

/-- Coordinate form of the classical chain rule. -/
theorem fderiv_comp_basisVec
    {d : ℕ} {G : ℝ → ℝ} {w : Vec d → ℝ}
    {x : Vec d} {i : Fin d}
    (hG : DifferentiableAt ℝ G (w x))
    (hw : DifferentiableAt ℝ w x) :
    (fderiv ℝ (fun y => G (w y)) x) (basisVec i) =
      deriv G (w x) *
        (fderiv ℝ w x) (basisVec i) := by
  have hcomp :
      HasFDerivAt
        (fun y => G (w y))
        ((fderiv ℝ G (w x)).comp (fderiv ℝ w x)) x :=
    hG.hasFDerivAt.comp x hw.hasFDerivAt
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply,
    fderiv_eq_deriv_mul]

/-- Exact `L^p` stability of composition by an `M`-Lipschitz real map. -/
theorem eLpNorm_comp_sub_le_of_lipschitz
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {G : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hLip : LipschitzWith M.toNNReal G)
    (f g : α → ℝ)
    (hmeas : AEStronglyMeasurable (fun x => G (f x) - G (g x)) μ) :
    eLpNorm (fun x => G (f x) - G (g x)) p μ ≤
      ENNReal.ofReal M *
        eLpNorm (fun x => f x - g x) p μ := by
  have hpoint :
      ∀ x,
        ‖G (f x) - G (g x)‖ ≤
          ‖M • (f x - g x)‖ := by
    intro x
    have hdist := hLip.dist_le_mul (f x) (g x)
    rw [norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg hM]
    simpa only [Real.dist_eq,
      Real.coe_toNNReal M hM] using hdist
  calc
    eLpNorm (fun x => G (f x) - G (g x)) p μ ≤
        eLpNorm (fun x => M • (f x - g x)) p μ :=
      eLpNorm_mono hmeas hpoint
    _ = ENNReal.ofReal M *
          eLpNorm (fun x => f x - g x) p μ := by
      rw [show
        (fun x => M • (f x - g x)) =
          M • (fun x => f x - g x) by rfl,
        eLpNorm_const_smul]
      rw [Real.enorm_eq_ofReal hM]

/-- A pointwise scalar multiplier bounded by `M` costs exactly `M` in the
Euclidean vector-field `L^p` norm. -/
theorem eLpNorm_vecEuclideanNorm_smul_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {p : ℝ≥0∞} {a : α → ℝ}
    {F : α → Vec d} {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hmeas : AEStronglyMeasurable
      (fun x => vecEuclideanNorm (a x • F x)) μ) :
    eLpNorm
        (fun x => vecEuclideanNorm (a x • F x)) p μ ≤
      ENNReal.ofReal M *
        eLpNorm (fun x => vecEuclideanNorm (F x)) p μ := by
  have hpoint :
      ∀ x,
        ‖vecEuclideanNorm (a x • F x)‖ ≤
          ‖M • vecEuclideanNorm (F x)‖ := by
    intro x
    simp only [Real.norm_eq_abs, vecEuclideanNorm_smul,
      smul_eq_mul, abs_mul, abs_abs, abs_of_nonneg hM,
      abs_of_nonneg (vecEuclideanNorm_nonneg (F x))]
    exact
      mul_le_mul_of_nonneg_right
        (ha x) (vecEuclideanNorm_nonneg (F x))
  calc
    eLpNorm
        (fun x => vecEuclideanNorm (a x • F x)) p μ ≤
        eLpNorm
          (fun x => M • vecEuclideanNorm (F x)) p μ :=
      eLpNorm_mono hmeas hpoint
    _ = ENNReal.ofReal M *
          eLpNorm
            (fun x => vecEuclideanNorm (F x)) p μ := by
      rw [show
        (fun x => M • vecEuclideanNorm (F x)) =
          M • (fun x => vecEuclideanNorm (F x)) by rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal hM]

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- A bounded-derivative `C¹` composition has the expected weak gradient on a
bounded open convex domain, for every finite `p ≥ 1`. -/
theorem hasWeakGradient_comp_contDiff_of_deriv_bounded
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    HasWeakGradientOn U
      (fun x => G (u.toFun x))
      (fun x i =>
        deriv G (u.toFun x) * u.grad x i) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  rcases U.eq_empty_or_nonempty with hUEmpty | hUNonempty
  · subst U
    intro i φ _hφSmooth _hφCompact _hφSupport
    simp only [Measure.restrict_empty,
      integral_zero_measure, neg_zero]
  obtain ⟨x0, r, hr, hball⟩ :=
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain
      hU hUNonempty
  have hGDiff : Differentiable ℝ G :=
    hG.differentiable (by norm_num)
  have hGLip : LipschitzWith M.toNNReal G :=
    lipschitzWith_of_abs_deriv_le hM hGDiff hderiv
  have hderivContinuous : Continuous (deriv G) :=
    hG.continuous_deriv (by norm_num)
  have hGZeroLip :
      LipschitzWith M.toNNReal
        (fun t => G t - G 0) := by
    intro a b
    simpa only [edist_sub_right] using hGLip a b
  have hcompMem :
      ∀ v : Vec d → ℝ,
        MemLp v p (volumeOn U) →
          MemLp (fun x => G (v x)) p (volumeOn U) := by
    intro v hv
    have hshift :
        MemLp (fun x => G (v x) - G 0)
          p (volumeOn U) := by
      simpa only [Function.comp_apply] using!
        hGZeroLip.comp_memLp (by simp) hv
    have hconstant :
        MemLp (fun _ : Vec d => G 0)
          p (volumeOn U) :=
      memLp_const (G 0)
    refine (hshift.add hconstant).ae_eq ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hcompGradMem :
      ∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
        MemLp v p (volumeOn U) →
        GradMemLpOn U p Dv →
          GradMemLpOn U p
            (fun x i => deriv G (v x) * Dv x i) := by
    intro v Dv hv hDv i
    refine MemLp.of_le_mul (c := M) (hDv i) ?_ ?_
    · exact
        (hderivContinuous.comp_aestronglyMeasurable
          hv.aestronglyMeasurable).mul
          (hDv i).aestronglyMeasurable
    · filter_upwards with x
      simp only [norm_mul, Real.norm_eq_abs]
      exact
        mul_le_mul_of_nonneg_right
          (hderiv (v x)) (abs_nonneg (Dv x i))
  let ψ : ℕ → W1pFunction U p :=
    convexApproxSmoothW1p hU hp u x0 hr
  have hψSmooth :
      ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n).toFun := by
    intro n
    exact
      contDiff_convexApproxSmoothW1p_toFun
        hU hp u x0 hr n
  let valueSeq : ℕ → Vec d → ℝ :=
    fun n x => G ((ψ n).toFun x)
  let gradSeq : ℕ → Vec d → Vec d :=
    fun n x i =>
      deriv G ((ψ n).toFun x) * (ψ n).grad x i
  have hvalueSeqMem :
      ∀ n, MemLpOn U p (valueSeq n) := by
    intro n
    exact hcompMem (ψ n).toFun (ψ n).memLp
  have hgradSeqMem :
      ∀ n, GradMemLpOn U p (gradSeq n) := by
    intro n
    exact
      hcompGradMem (ψ n).toFun (ψ n).grad
        (ψ n).memLp (ψ n).gradMemLp
  have hweakSeq :
      ∀ n,
        HasWeakGradientOn U (valueSeq n) (gradSeq n) := by
    intro n
    have hcompSmooth :
        ContDiff ℝ 1
          (fun x => G ((ψ n).toFun x)) :=
      hG.comp ((hψSmooth n).of_le (by norm_num))
    have hgradient :
        classicalGradient
            (fun x => G ((ψ n).toFun x)) =
          gradSeq n := by
      funext x i
      rw [classicalGradient_apply]
      exact
        fderiv_comp_basisVec
          hGDiff.differentiableAt
          ((hψSmooth n).differentiable
            (by norm_num)).differentiableAt
    change
      HasWeakGradientOn U
        (fun x => G ((ψ n).toFun x)) (gradSeq n)
    rw [← hgradient]
    simpa only [classicalGradient_apply] using!
      HasWeakGradientOn.of_contDiff hcompSmooth
  have htargetValueMem :
      MemLpOn U p (fun x => G (u.toFun x)) :=
    hcompMem u.toFun u.memLp
  have htargetGradMem :
      GradMemLpOn U p
        (fun x i =>
          deriv G (u.toFun x) * u.grad x i) :=
    hcompGradMem u.toFun u.grad u.memLp u.gradMemLp
  have hψValue :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x => (ψ n).toFun x - u.toFun x)
            p (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [ψ] using
      tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
        hU hp hpTop u hball hr
  have hvalueSeq :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              valueSeq n x - G (u.toFun x))
            p (volumeOn U))
        atTop (𝓝 0) := by
    have hupper :
        Tendsto
          (fun n =>
            ENNReal.ofReal M *
              eLpNorm
                (fun x => (ψ n).toFun x - u.toFun x)
                p (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hψValue
          (Or.inr ENNReal.ofReal_ne_top)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper
        (fun _ => zero_le)
        (fun n =>
          eLpNorm_comp_sub_le_of_lipschitz
            hM hGLip (ψ n).toFun u.toFun
            ((hGLip.continuous.comp_aestronglyMeasurable
                (ψ n).memLp.aestronglyMeasurable).sub
              (hGLip.continuous.comp_aestronglyMeasurable
                u.memLp.aestronglyMeasurable)))
  have hpZero : p ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le hp)
  obtain ⟨σ, hσStrictMono, hσAe⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm
      hpZero hψValue).exists_seq_tendsto_ae
  have hψGradCoordinate :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x =>
                (ψ n).grad x i - u.grad x i)
              p (volumeOn U))
          atTop (𝓝 0) := by
    intro i
    simpa only [ψ] using
      tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
        hU hp hpTop u hball hr i
  have hgradSeq :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x =>
                gradSeq (σ n) x i -
                  deriv G (u.toFun x) * u.grad x i)
              p (volumeOn U))
          atTop (𝓝 0) := by
    intro i
    let first : ℕ → Vec d → ℝ :=
      fun n x =>
        deriv G ((ψ (σ n)).toFun x) *
          ((ψ (σ n)).grad x i - u.grad x i)
    let second : ℕ → Vec d → ℝ :=
      fun n x =>
        (deriv G ((ψ (σ n)).toFun x) -
            deriv G (u.toFun x)) *
          u.grad x i
    have hfirstMeas :
        ∀ n,
          AEStronglyMeasurable
            (first n) (volumeOn U) := by
      intro n
      exact
        (hderivContinuous.comp_aestronglyMeasurable
          (ψ (σ n)).memLp.aestronglyMeasurable).mul
          (((ψ (σ n)).grad_memLp i).aestronglyMeasurable.sub
            (u.grad_memLp i).aestronglyMeasurable)
    have hfirstBound :
        ∀ n,
          eLpNorm (first n) p (volumeOn U) ≤
            ENNReal.ofReal M *
              eLpNorm
                (fun x =>
                  (ψ (σ n)).grad x i - u.grad x i)
                p (volumeOn U) := by
      intro n
      have hpoint :
          ∀ x,
            ‖first n x‖ ≤
              ‖M •
                ((ψ (σ n)).grad x i -
                  u.grad x i)‖ := by
        intro x
        simp only [first, norm_mul, Real.norm_eq_abs,
          norm_smul, abs_of_nonneg hM]
        exact
          mul_le_mul_of_nonneg_right
            (hderiv ((ψ (σ n)).toFun x))
            (abs_nonneg
              ((ψ (σ n)).grad x i - u.grad x i))
      calc
        eLpNorm (first n) p (volumeOn U) ≤
            eLpNorm
              (fun x =>
                M •
                  ((ψ (σ n)).grad x i -
                    u.grad x i))
              p (volumeOn U) :=
          eLpNorm_mono (hfirstMeas n) hpoint
        _ = ENNReal.ofReal M *
              eLpNorm
                (fun x =>
                  (ψ (σ n)).grad x i - u.grad x i)
                p (volumeOn U) := by
          rw [show
            (fun x =>
              M •
                ((ψ (σ n)).grad x i -
                  u.grad x i)) =
              M •
                (fun x =>
                  (ψ (σ n)).grad x i -
                    u.grad x i) by rfl,
            eLpNorm_const_smul,
            Real.enorm_eq_ofReal hM]
    have hfirst :
        Tendsto
          (fun n =>
            eLpNorm (first n) p (volumeOn U))
          atTop (𝓝 0) := by
      have hcoordinate :=
        (hψGradCoordinate i).comp
          hσStrictMono.tendsto_atTop
      have hupper :
          Tendsto
            (fun n =>
              ENNReal.ofReal M *
                eLpNorm
                  (fun x =>
                    (ψ (σ n)).grad x i - u.grad x i)
                  p (volumeOn U))
            atTop (𝓝 0) := by
        simpa only [mul_zero, Function.comp_apply] using
          ENNReal.Tendsto.const_mul hcoordinate
            (Or.inr ENNReal.ofReal_ne_top)
      exact
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds hupper
          (fun _ => zero_le) hfirstBound
    have hsecondMeas :
        ∀ n,
          AEStronglyMeasurable
            (second n) (volumeOn U) := by
      intro n
      exact
        ((hderivContinuous.comp_aestronglyMeasurable
          (ψ (σ n)).memLp.aestronglyMeasurable).sub
          (hderivContinuous.comp_aestronglyMeasurable
            u.memLp.aestronglyMeasurable)).mul
          (u.grad_memLp i).aestronglyMeasurable
    let secondBound : Vec d → ℝ :=
      fun x => (2 * M) * u.grad x i
    have hsecondBoundMem :
        MemLp secondBound p (volumeOn U) := by
      exact (u.grad_memLp i).const_mul (2 * M)
    have hsecondBound :
        ∀ n, ∀ᵐ x ∂(volumeOn U),
          ‖second n x‖ ≤ ‖secondBound x‖ := by
      intro n
      filter_upwards with x
      have hdiff :
          |deriv G ((ψ (σ n)).toFun x) -
              deriv G (u.toFun x)| ≤
            2 * M := by
        calc
          |deriv G ((ψ (σ n)).toFun x) -
              deriv G (u.toFun x)| ≤
              |deriv G ((ψ (σ n)).toFun x)| +
                |deriv G (u.toFun x)| :=
            abs_sub _ _
          _ ≤ M + M :=
            add_le_add
              (hderiv ((ψ (σ n)).toFun x))
              (hderiv (u.toFun x))
          _ = 2 * M := by ring
      simp only [second, secondBound, norm_mul,
        Real.norm_eq_abs]
      simpa only [abs_of_nonneg hM,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        mul_le_mul_of_nonneg_right hdiff
          (abs_nonneg (u.grad x i))
    have hsecondAe :
        ∀ᵐ x ∂(volumeOn U),
          Tendsto
            (fun n => second n x)
            atTop (𝓝 0) := by
      filter_upwards [hσAe] with x hx
      have hderivTendsto :
          Tendsto
            (fun n =>
              deriv G ((ψ (σ n)).toFun x))
            atTop
            (𝓝 (deriv G (u.toFun x))) :=
        (hderivContinuous.tendsto (u.toFun x)).comp hx
      have hdifference :=
        hderivTendsto.sub
          (tendsto_const_nhds :
            Tendsto
              (fun _ : ℕ => deriv G (u.toFun x))
              atTop
              (𝓝 (deriv G (u.toFun x))))
      have hproduct :=
        hdifference.mul_const (u.grad x i)
      simpa only [second, sub_self, zero_mul] using hproduct
    have hsecond :
        Tendsto
          (fun n =>
            eLpNorm
              (second n - (0 : Vec d → ℝ))
              p (volumeOn U))
          atTop (𝓝 0) :=
      tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
        hp hpTop hsecondMeas
        (MeasureTheory.MemLp.zero :
          MemLp (0 : Vec d → ℝ) p (volumeOn U))
        hsecondBoundMem hsecondBound hsecondAe
    have hsecondZero :
        Tendsto
          (fun n =>
            eLpNorm (second n) p (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [Pi.sub_apply, sub_zero] using hsecond
    have hsum :
        Tendsto
          (fun n =>
            eLpNorm (first n) p (volumeOn U) +
              eLpNorm (second n) p (volumeOn U))
          atTop (𝓝 0) := by
      simpa only [zero_add] using hfirst.add hsecondZero
    have hdecomp :
        ∀ n,
          (fun x =>
            gradSeq (σ n) x i -
              deriv G (u.toFun x) * u.grad x i) =
            first n + second n := by
      intro n
      funext x
      simp only [gradSeq, first, second,
        Pi.add_apply]
      ring
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hsum
        (fun _ => zero_le)
        (fun n => by
          rw [hdecomp n]
          exact
            eLpNorm_add_le hp)
  exact
    HasWeakGradientOn.of_tendsto_eLpNorm
      htargetValueMem htargetGradMem
      (fun n => hvalueSeqMem (σ n))
      (fun n => hgradSeqMem (σ n))
      (fun n => hweakSeq (σ n))
      (hvalueSeq.comp hσStrictMono.tendsto_atTop)
      hgradSeq

/-- Compose a representative-level Sobolev function with a `C¹` real
function whose derivative is bounded by `M`. -/
noncomputable def compContDiffOfDerivBounded
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    W1pFunction U p where
  toFun := fun x => G (u.toFun x)
  grad := fun x i =>
    deriv G (u.toFun x) * u.grad x i
  memLp := by
    let : IsFiniteMeasure (volumeOn U) :=
      hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
    have hGDiff : Differentiable ℝ G :=
      hG.differentiable (by norm_num)
    have hGLip : LipschitzWith M.toNNReal G :=
      lipschitzWith_of_abs_deriv_le hM hGDiff hderiv
    have hGZeroLip :
        LipschitzWith M.toNNReal
          (fun t => G t - G 0) := by
      intro a b
      simpa only [edist_sub_right] using hGLip a b
    have hshift :
        MemLp
          (fun x => G (u.toFun x) - G 0)
          p (volumeOn U) := by
      exact hGZeroLip.comp_memLp (by simp) u.memLp
    refine
      (hshift.add
        (memLp_const (G 0) :
          MemLp (fun _ : Vec d => G 0)
            p (volumeOn U))).ae_eq ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  gradMemLp := by
    have hderivContinuous : Continuous (deriv G) :=
      hG.continuous_deriv (by norm_num)
    intro i
    refine MemLp.of_le_mul (c := M) (u.grad_memLp i) ?_ ?_
    · exact
        (hderivContinuous.comp_aestronglyMeasurable
          u.memLp.aestronglyMeasurable).mul
          (u.grad_memLp i).aestronglyMeasurable
    · filter_upwards with x
      simp only [norm_mul, Real.norm_eq_abs]
      exact
        mul_le_mul_of_nonneg_right
          (hderiv (u.toFun x))
          (abs_nonneg (u.grad x i))
  hasWeakGradient :=
    hasWeakGradient_comp_contDiff_of_deriv_bounded
      hU hp hpTop u hG hM hderiv

@[simp]
theorem compContDiffOfDerivBounded_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    (u.compContDiffOfDerivBounded
      hU hp hpTop hG hM hderiv).toFun =
        fun x => G (u.toFun x) :=
  rfl

@[simp]
theorem compContDiffOfDerivBounded_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    (u.compContDiffOfDerivBounded
      hU hp hpTop hG hM hderiv).grad =
        fun x i =>
          deriv G (u.toFun x) * u.grad x i :=
  rfl

/-- Sharp value estimate after subtracting the unavoidable constant
`G(0)`. -/
theorem eLpNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    eLpNormOn U p
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hp hpTop hG hM hderiv).toFun x -
            G 0) ≤
      ENNReal.ofReal M *
        eLpNormOn U p u.toFun := by
  have hGDiff : Differentiable ℝ G :=
    hG.differentiable (by norm_num)
  have hGLip : LipschitzWith M.toNNReal G :=
    lipschitzWith_of_abs_deriv_le hM hGDiff hderiv
  simpa only [eLpNormOn,
    compContDiffOfDerivBounded_toFun,
    sub_zero] using
    eLpNorm_comp_sub_le_of_lipschitz
      (μ := volumeOn U) (p := p)
      hM hGLip u.toFun (fun _ => 0)
      ((hGLip.continuous.comp_aestronglyMeasurable
          u.memLp.aestronglyMeasurable).sub aestronglyMeasurable_const)

/-- Normalized sharp value estimate after subtracting the unavoidable
constant `G(0)`. -/
theorem eLpMeanNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
    (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    eLpMeanNormOn U p
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hp hpTop hG hM hderiv).toFun x -
            G 0) ≤
      ENNReal.ofReal M *
        eLpMeanNormOn U p u.toFun := by
  have hvolumePos :
      0 < volume U ^ (1 / p).toReal :=
    ENNReal.rpow_pos hUPos hUTop.ne
  have hvolumeTop :
      volume U ^ (1 / p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hUPos.ne' hUTop.ne
  have hraw :=
    eLpNormOn_compContDiffOfDerivBounded_sub_apply_zero_le
      hU hp hpTop u hG hM hderiv
  rw [eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      hUPos hUTop,
    eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      hUPos hUTop] at hraw
  exact
    (ENNReal.mul_le_mul_iff_right
      hvolumePos.ne' hvolumeTop).mp <| by
        simpa only [mul_assoc, mul_left_comm] using hraw

/-- Every gradient coordinate has the exact multiplier cost `M`. -/
theorem eLpNormOn_compContDiffOfDerivBounded_grad_coord_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M)
    (i : Fin d) :
    eLpNormOn U p
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hp hpTop hG hM hderiv).grad x i) ≤
      ENNReal.ofReal M *
        eLpNormOn U p (fun x => u.grad x i) := by
  have hpoint :
      ∀ x,
        ‖deriv G (u.toFun x) * u.grad x i‖ ≤
          ‖M • u.grad x i‖ := by
    intro x
    simp only [norm_mul, Real.norm_eq_abs,
      norm_smul, abs_of_nonneg hM]
    exact
      mul_le_mul_of_nonneg_right
        (hderiv (u.toFun x))
        (abs_nonneg (u.grad x i))
  calc
    eLpNormOn U p
        (fun x =>
          (u.compContDiffOfDerivBounded
            hU hp hpTop hG hM hderiv).grad x i) ≤
        eLpNormOn U p
          (fun x => M • u.grad x i) := by
      apply eLpNorm_mono
        ((u.compContDiffOfDerivBounded
          hU hp hpTop hG hM hderiv).gradMemLp i).aestronglyMeasurable
      simpa only [compContDiffOfDerivBounded_grad] using!
        hpoint
    _ = ENNReal.ofReal M *
          eLpNormOn U p (fun x => u.grad x i) := by
      simp only [eLpNormOn]
      rw [show
        (fun x => M • u.grad x i) =
          M • (fun x => u.grad x i) by rfl,
        eLpNorm_const_smul,
        Real.enorm_eq_ofReal hM]

/-- The full Euclidean gradient has the exact, dimension-free multiplier
cost `M`. -/
theorem euclideanFieldELpNormOn_compContDiffOfDerivBounded_grad_le
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    euclideanFieldELpNormOn U p
        (u.compContDiffOfDerivBounded
          hU hp hpTop hG hM hderiv).grad ≤
      ENNReal.ofReal M *
        euclideanFieldELpNormOn U p u.grad := by
  have hfield :
      (u.compContDiffOfDerivBounded
          hU hp hpTop hG hM hderiv).grad =
        fun x =>
          deriv G (u.toFun x) • u.grad x := by
    funext x i
    rfl
  rw [hfield]
  exact
    eLpNorm_vecEuclideanNorm_smul_le
      (μ := volumeOn U) hM
      (fun x => hderiv (u.toFun x))
      (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i =>
        ((u.compContDiffOfDerivBounded
          hU hp hpTop hG hM hderiv).gradMemLp i).aestronglyMeasurable)

/-- The normalized full Euclidean gradient has the exact, dimension-free
multiplier cost `M`. -/
theorem euclideanFieldELpMeanNormOn_compContDiffOfDerivBounded_grad_le
    (hU : IsOpenBoundedConvexDomain U)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    {M : ℝ} (hM : 0 ≤ M)
    (hderiv : ∀ t, |deriv G t| ≤ M) :
    euclideanFieldELpMeanNormOn U p
        (u.compContDiffOfDerivBounded
          hU hp hpTop hG hM hderiv).grad ≤
      ENNReal.ofReal M *
        euclideanFieldELpMeanNormOn U p u.grad := by
  have hvolumePos :
      0 < volume U ^ (1 / p).toReal :=
    ENNReal.rpow_pos hUPos hUTop.ne
  have hvolumeTop :
      volume U ^ (1 / p).toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hUPos.ne' hUTop.ne
  have hraw :=
    euclideanFieldELpNormOn_compContDiffOfDerivBounded_grad_le
      hU hp hpTop u hG hM hderiv
  rw [euclideanFieldELpNormOn_eq_volume_rpow_mul
      hUPos hUTop,
    euclideanFieldELpNormOn_eq_volume_rpow_mul
      hUPos hUTop] at hraw
  exact
    (ENNReal.mul_le_mul_iff_right
      hvolumePos.ne' hvolumeTop).mp <| by
        simpa only [mul_assoc, mul_left_comm] using hraw

end W1pFunction

end PDE
