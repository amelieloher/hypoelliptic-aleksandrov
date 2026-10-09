module

public import PDEFoundation.Sobolev.W1p.Closure
public import PDEFoundation.Sobolev.W1p.Algebra

/-!
# Zero-boundary `W^{1,p}` as a closed graph

This file defines the canonical complete zero-boundary Sobolev carrier as the
closure, inside `W1pGraph`, of the range of actual bundled globally smooth
functions with compact support contained in the domain.  It also retains the
representative-level supported-approximation certificate used by local PDE
arguments.

## Main definitions

- `W1pFunction.SupportedSmoothApproximation`: concrete supported smooth
  approximation data for a representative.
- `smoothCompactlySupportedW1pGraphSubmodule`: the range submodule of the
  exact linear map from supported smooth test functions.
- `W10pGraph`: the closed zero-boundary graph carrier.

## Main results

- `W1pFunction.SupportedSmoothApproximation.tendsto_toW1pGraph` upgrades the
  explicit value and coordinate-gradient convergence to graph convergence.
- `W1pFunction.mem_w10pGraph_of_supportedSmoothApproximation` sends a
  representative certificate to the complete zero-boundary carrier.
- `W10pGraph.exists_tendsto_smooth` gives an actual sequence of bundled
  smooth test functions converging to every complete-carrier point.

The complete carrier is deliberately a closure in the existing `W1pGraph`;
there is no second weak-gradient relation and no extra boundary condition
hidden in a structure field.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace WeakTestFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- Smooth compactly supported weak test functions are closed under the
linear operations used by zero-boundary density. -/
instance : Zero (WeakTestFunction U) where
  zero :=
    { toFun := 0
      contDiff := contDiff_zero_fun
      hasCompactSupport := HasCompactSupport.zero
      tsupport_subset := by simp only [tsupport_zero, Set.empty_subset] }

instance : Add (WeakTestFunction U) where
  add φ ψ :=
    { toFun := φ.toFun + ψ.toFun
      contDiff := φ.contDiff.add ψ.contDiff
      hasCompactSupport := φ.hasCompactSupport.add ψ.hasCompactSupport
      tsupport_subset :=
        (tsupport_add φ.toFun ψ.toFun).trans
          (Set.union_subset φ.tsupport_subset ψ.tsupport_subset) }

instance : Neg (WeakTestFunction U) where
  neg φ :=
    { toFun := -φ.toFun
      contDiff := φ.contDiff.neg
      hasCompactSupport := φ.hasCompactSupport.neg
      tsupport_subset := by
        rw [tsupport_neg]
        exact φ.tsupport_subset }

instance : Sub (WeakTestFunction U) where
  sub φ ψ :=
    { toFun := φ.toFun - ψ.toFun
      contDiff := φ.contDiff.sub ψ.contDiff
      hasCompactSupport := φ.hasCompactSupport.sub ψ.hasCompactSupport
      tsupport_subset :=
        (tsupport_sub φ.toFun ψ.toFun).trans
          (Set.union_subset φ.tsupport_subset ψ.tsupport_subset) }

instance : SMul ℝ (WeakTestFunction U) where
  smul c φ :=
    { toFun := c • φ.toFun
      contDiff := φ.contDiff.const_smul c
      hasCompactSupport := φ.hasCompactSupport.smul_left
      tsupport_subset :=
        (tsupport_smul_subset_right (fun _ : Vec d => c) φ.toFun).trans
          φ.tsupport_subset }

@[simp]
theorem zero_toFun :
    (0 : WeakTestFunction U).toFun = 0 :=
  rfl

@[simp]
theorem add_toFun (φ ψ : WeakTestFunction U) :
    (φ + ψ).toFun = fun x => φ x + ψ x :=
  rfl

@[simp]
theorem neg_toFun (φ : WeakTestFunction U) :
    (-φ).toFun = fun x => -φ x :=
  rfl

@[simp]
theorem sub_toFun (φ ψ : WeakTestFunction U) :
    (φ - ψ).toFun = fun x => φ x - ψ x :=
  rfl

@[simp]
theorem smul_toFun (c : ℝ) (φ : WeakTestFunction U) :
    (c • φ).toFun = fun x => c * φ x :=
  rfl

@[ext]
theorem ext {φ ψ : WeakTestFunction U} (h : φ.toFun = ψ.toFun) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

theorem toFun_injective : Function.Injective (fun φ : WeakTestFunction U => φ.toFun) :=
  fun _ _ h => ext h

instance : SMul ℕ (WeakTestFunction U) where
  smul n φ := (n : ℝ) • φ

instance : SMul ℤ (WeakTestFunction U) where
  smul n φ := (n : ℝ) • φ

instance : AddCommGroup (WeakTestFunction U) :=
  Function.Injective.addCommGroup
    (fun φ : WeakTestFunction U => φ.toFun) toFun_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun φ n => by
      funext x
      change ((n : ℝ) • φ.toFun) x = (n • φ.toFun) x
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul])
    (fun φ n => by
      funext x
      change ((n : ℝ) • φ.toFun) x = (n • φ.toFun) x
      simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul])

/-- The underlying-function additive homomorphism transfers the standard
real module structure to bundled weak test functions. -/
def toFunAddMonoidHom : WeakTestFunction U →+ (Vec d → ℝ) where
  toFun := fun φ => φ.toFun
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (WeakTestFunction U) :=
  Function.Injective.module ℝ toFunAddMonoidHom toFun_injective
    (fun _ _ => rfl)

end WeakTestFunction

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
variable {u : W1pFunction U p}

/-- Explicit supported smooth approximation data for a representative-level
`W^{1,p}(U)` function.  The value and every native gradient coordinate
converge in the exact same exponent. -/
structure SupportedSmoothApproximation
    (u : W1pFunction U p) where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_tsupport_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_value :
    Tendsto
      (fun n => eLpNorm (approx n - u.toFun) p (volumeOn U))
      atTop (𝓝 0)
  tendsto_grad :
    ∀ i : Fin d,
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ (approx n) x) (basisVec i) - u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0)

/-- Proposition-valued supported smooth approximability.  The sequence may
remain hidden when a later argument only needs zero-boundary membership. -/
def HasSupportedSmoothApproximation (u : W1pFunction U p) : Prop :=
  Nonempty u.SupportedSmoothApproximation

/-- Regard one member of a supported approximation as a bundled weak test
function. -/
noncomputable def SupportedSmoothApproximation.toWeakTestFunction
    (happrox : u.SupportedSmoothApproximation) (n : ℕ) :
    WeakTestFunction U where
  toFun := happrox.approx n
  contDiff := happrox.approx_smooth n
  hasCompactSupport := happrox.approx_hasCompactSupport n
  tsupport_subset := happrox.approx_tsupport_subset n

/-- Convergence of representatives and all native gradient coordinates gives
convergence in the closed quotient-level `W^{1,p}` graph. -/
theorem tendsto_toW1pGraph_of_tendsto_eLpNorm
    [Fact (1 ≤ p)]
    (u : W1pFunction U p) (uSeq : ℕ → W1pFunction U p)
    (hValue :
      Tendsto
        (fun n => eLpNorm ((uSeq n).toFun - u.toFun) p (volumeOn U))
        atTop (𝓝 0))
    (hGradient :
      ∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (uSeq n).grad x i - u.grad x i)
              p (volumeOn U))
          atTop (𝓝 0)) :
    Tendsto (fun n => (uSeq n).toW1pGraph) atTop (𝓝 u.toW1pGraph) := by
  rw [tendsto_subtype_rng]
  have hValueLp :
      Tendsto
        (fun n => (uSeq n).memLp.toScalarLp)
        atTop (𝓝 u.memLp.toScalarLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => (uSeq n).toFun) (fun n => (uSeq n).memLp)
        u.toFun u.memLp).mpr hValue
  have hGradientEuclidean :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x => vecEuclideanNorm ((uSeq n).grad x - u.grad x))
            p (volumeOn U))
        atTop (𝓝 0) := by
    apply
      tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
        Fact.out
    · intro n i
      exact
        ((uSeq n).grad_memLp i).aestronglyMeasurable.sub
          (u.grad_memLp i).aestronglyMeasurable
    · exact hGradient
  have hGradientHilbert :
      Tendsto
        (fun n =>
          eLpNorm
            (toHilbertVecField (uSeq n).grad - toHilbertVecField u.grad)
            p (volumeOn U))
        atTop (𝓝 0) := by
    have hEq : ∀ n,
        eLpNorm (toHilbertVecField fun x => (uSeq n).grad x - u.grad x) p
            (volumeOn U) =
          eLpNorm (fun x => vecEuclideanNorm ((uSeq n).grad x - u.grad x)) p
            (volumeOn U) :=
      fun n => eLpNorm_toHilbertVecField_eq _ _ _
        (aemeasurable_pi_iff.2 fun i =>
          (((uSeq n).grad_memLp i).aestronglyMeasurable.sub
            (u.grad_memLp i).aestronglyMeasurable).aemeasurable).aestronglyMeasurable
    simpa only [toHilbertVecField_sub, hEq] using
      hGradientEuclidean
  have hGradientLp :
      Tendsto
        (fun n => (uSeq n).gradMemLp.toHilbertVectorLp)
        atTop (𝓝 u.gradMemLp.toHilbertVectorLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => toHilbertVecField (uSeq n).grad)
        (fun n =>
          gradMemLpOn_iff_memLp_toHilbertVecField.mp (uSeq n).gradMemLp)
        (toHilbertVecField u.grad)
        (gradMemLpOn_iff_memLp_toHilbertVecField.mp u.gradMemLp)).mpr
        hGradientHilbert
  have hPair :
      Tendsto
        (fun n =>
          weakGradientLpPairOfRepresentatives
            (uSeq n).memLp (uSeq n).gradMemLp)
        atTop
        (𝓝 (weakGradientLpPairOfRepresentatives u.memLp u.gradMemLp)) := by
    simpa only [weakGradientLpPairOfRepresentatives] using
      hValueLp.prodMk_nhds hGradientLp
  exact hPair

/-- The graph images of a supported smooth approximation converge to the graph
image of its target representative. -/
theorem SupportedSmoothApproximation.tendsto_toW1pGraph
    [Fact (1 ≤ p)] (hU : IsOpen U)
    (happrox : u.SupportedSmoothApproximation) :
    Tendsto
      (fun n =>
        (W1pFunction.ofContDiff hU
          ((happrox.approx_smooth n).of_le (by simp))
          (happrox.approx_hasCompactSupport n) p).toW1pGraph)
      atTop (𝓝 u.toW1pGraph) := by
  apply W1pFunction.tendsto_toW1pGraph_of_tendsto_eLpNorm u
  · simpa only [W1pFunction.ofContDiff] using happrox.tendsto_value
  · intro i
    simpa only [W1pFunction.ofContDiff] using happrox.tendsto_grad i

end W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The complete graph point associated to a globally smooth function with
compact support contained in `U`. -/
noncomputable def smoothCompactlySupportedW1pGraph
    [Fact (1 ≤ p)] (hU : IsOpen U) (φ : WeakTestFunction U) :
    W1pGraph U p :=
  (W1pFunction.ofContDiff hU
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph

/-- The graph image of supported smooth test functions respects addition. -/
theorem smoothCompactlySupportedW1pGraph_add
    [Fact (1 ≤ p)] (hU : IsOpen U) (φ ψ : WeakTestFunction U) :
    smoothCompactlySupportedW1pGraph (p := p) hU (φ + ψ) =
      smoothCompactlySupportedW1pGraph (p := p) hU φ +
        smoothCompactlySupportedW1pGraph (p := p) hU ψ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [
      (W1pFunction.coeFn_toW1pGraph_fst
        (W1pFunction.ofContDiff hU
          ((φ + ψ).contDiff.of_le (by simp))
          (φ + ψ).hasCompactSupport p)),
      Lp.coeFn_add
        (smoothCompactlySupportedW1pGraph (p := p) hU φ).1.1
        (smoothCompactlySupportedW1pGraph (p := p) hU ψ).1.1,
      (W1pFunction.coeFn_toW1pGraph_fst
        (W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p)),
      (W1pFunction.coeFn_toW1pGraph_fst
        (W1pFunction.ofContDiff hU
          (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p))]
      with x hsum hadd hφ hψ
    change
      ⇑((W1pFunction.ofContDiff hU
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.1 +
          (W1pFunction.ofContDiff hU
            (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p).toW1pGraph.1.1) x =
        (⇑(W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.1 +
          ⇑(W1pFunction.ofContDiff hU
            (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p).toW1pGraph.1.1) x at hadd
    change
      ⇑(W1pFunction.ofContDiff hU
        ((φ + ψ).contDiff.of_le (by simp))
        (φ + ψ).hasCompactSupport p).toW1pGraph.1.1 x =
        ⇑((W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.1 +
          (W1pFunction.ofContDiff hU
            (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p).toW1pGraph.1.1) x
    rw [hsum, hadd]
    simp only [Pi.add_apply]
    rw [hφ, hψ]
    rfl
  · apply Lp.ext
    filter_upwards [
      (W1pFunction.coeFn_toW1pGraph_snd
        (W1pFunction.ofContDiff hU
          ((φ + ψ).contDiff.of_le (by simp))
          (φ + ψ).hasCompactSupport p)),
      Lp.coeFn_add
        (smoothCompactlySupportedW1pGraph (p := p) hU φ).1.2
        (smoothCompactlySupportedW1pGraph (p := p) hU ψ).1.2,
      (W1pFunction.coeFn_toW1pGraph_snd
        (W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p)),
      (W1pFunction.coeFn_toW1pGraph_snd
        (W1pFunction.ofContDiff hU
          (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p))]
      with x hsum hadd hφ hψ
    change
      ⇑((W1pFunction.ofContDiff hU
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.2 +
          (W1pFunction.ofContDiff hU
            (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p).toW1pGraph.1.2) x =
        (⇑(W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.2 +
          ⇑(W1pFunction.ofContDiff hU
            (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p).toW1pGraph.1.2) x at hadd
    change
      ⇑(W1pFunction.ofContDiff hU
        ((φ + ψ).contDiff.of_le (by simp))
        (φ + ψ).hasCompactSupport p).toW1pGraph.1.2 x =
        ⇑((W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.2 +
          (W1pFunction.ofContDiff hU
            (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport p).toW1pGraph.1.2) x
    rw [hsum, hadd]
    simp only [Pi.add_apply]
    rw [hφ, hψ]
    ext i
    simp only [W1pFunction.ofContDiff, toHilbertVecField_apply,
      Vec.toHilbertVec_apply]
    change
      (fderiv ℝ (φ.toFun + ψ.toFun) x) (basisVec i) =
        (fderiv ℝ φ.toFun x) (basisVec i) +
          (fderiv ℝ ψ.toFun x) (basisVec i)
    rw [fderiv_add]
    · rfl
    · exact φ.contDiff.differentiable (by simp) x
    · exact ψ.contDiff.differentiable (by simp) x

/-- The graph image of supported smooth test functions respects real scalar
multiplication. -/
theorem smoothCompactlySupportedW1pGraph_smul
    [Fact (1 ≤ p)] (hU : IsOpen U) (c : ℝ) (φ : WeakTestFunction U) :
    smoothCompactlySupportedW1pGraph (p := p) hU (c • φ) =
      c • smoothCompactlySupportedW1pGraph (p := p) hU φ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [
      (W1pFunction.coeFn_toW1pGraph_fst
        (W1pFunction.ofContDiff hU
          ((c • φ).contDiff.of_le (by simp))
          (c • φ).hasCompactSupport p)),
      Lp.coeFn_smul c
        (smoothCompactlySupportedW1pGraph (p := p) hU φ).1.1,
      (W1pFunction.coeFn_toW1pGraph_fst
        (W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p))]
      with x hsmul htarget hφ
    change
      ⇑(c • (W1pFunction.ofContDiff hU
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.1) x =
        (c • ⇑(W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.1) x at htarget
    change
      ⇑(W1pFunction.ofContDiff hU
        ((c • φ).contDiff.of_le (by simp))
        (c • φ).hasCompactSupport p).toW1pGraph.1.1 x =
        ⇑(c • (W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.1) x
    rw [hsmul, htarget]
    simp only [Pi.smul_apply]
    rw [hφ]
    rfl
  · apply Lp.ext
    filter_upwards [
      (W1pFunction.coeFn_toW1pGraph_snd
        (W1pFunction.ofContDiff hU
          ((c • φ).contDiff.of_le (by simp))
          (c • φ).hasCompactSupport p)),
      Lp.coeFn_smul c
        (smoothCompactlySupportedW1pGraph (p := p) hU φ).1.2,
      (W1pFunction.coeFn_toW1pGraph_snd
        (W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p))]
      with x hsmul htarget hφ
    change
      ⇑(c • (W1pFunction.ofContDiff hU
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.2) x =
        (c • ⇑(W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.2) x at htarget
    change
      ⇑(W1pFunction.ofContDiff hU
        ((c • φ).contDiff.of_le (by simp))
        (c • φ).hasCompactSupport p).toW1pGraph.1.2 x =
        ⇑(c • (W1pFunction.ofContDiff hU
          (φ.contDiff.of_le (by simp)) φ.hasCompactSupport p).toW1pGraph.1.2) x
    rw [hsmul, htarget]
    simp only [Pi.smul_apply]
    rw [hφ]
    ext i
    simp only [W1pFunction.ofContDiff, toHilbertVecField_apply,
      Vec.toHilbertVec_apply]
    change
      (fderiv ℝ (c • φ.toFun) x) (basisVec i) =
        c * (fderiv ℝ φ.toFun x) (basisVec i)
    rw [fderiv_const_smul]
    rfl
    exact φ.contDiff.differentiable (by simp) x

/-- The exact linear map from bundled smooth compactly supported test
functions to the complete weak-gradient graph. -/
noncomputable def smoothCompactlySupportedW1pGraphLinearMap
    [Fact (1 ≤ p)] (hU : IsOpen U) :
    WeakTestFunction U →ₗ[ℝ] W1pGraph U p where
  toFun := smoothCompactlySupportedW1pGraph (p := p) hU
  map_add' := smoothCompactlySupportedW1pGraph_add hU
  map_smul' := smoothCompactlySupportedW1pGraph_smul hU

/-- The graph-level submodule of actual bundled smooth compactly supported
test functions.  Because this is the range of a linear map, it is not merely
a formal span with unbundled finite combinations. -/
noncomputable def smoothCompactlySupportedW1pGraphSubmodule
    [Fact (1 ≤ p)] (hU : IsOpen U) :
    Submodule ℝ (W1pGraph U p) :=
  LinearMap.range (smoothCompactlySupportedW1pGraphLinearMap (p := p) hU)

/-- The closed zero-boundary graph: the closure, in `W1pGraph U p`, of the
range of actual bundled smooth compactly supported test functions. -/
noncomputable def w10pGraphClosedSubmodule
    [Fact (1 ≤ p)] (hU : IsOpen U) :
    ClosedSubmodule ℝ (W1pGraph U p) :=
  (smoothCompactlySupportedW1pGraphSubmodule (p := p) hU).closure

/-- The canonical complete quotient-level `W^{1,p}_0(U)` carrier. -/
noncomputable abbrev W10pGraph
    [Fact (1 ≤ p)] (hU : IsOpen U) :=
  ↥((w10pGraphClosedSubmodule (p := p) hU).toSubmodule)

/-- The zero-boundary graph is complete because it is a closed submodule of
the complete `W1pGraph` carrier. -/
noncomputable instance w10pGraphCompleteSpace
    [Fact (1 ≤ p)] (hU : IsOpen U) :
    CompleteSpace (W10pGraph (p := p) hU) :=
  (w10pGraphClosedSubmodule (p := p) hU).isClosed.completeSpace_coe

/-- A supported smooth function belongs to the complete zero-boundary graph. -/
theorem smoothCompactlySupportedW1pGraph_mem_w10pGraph
    [Fact (1 ≤ p)] (hU : IsOpen U) (φ : WeakTestFunction U) :
    smoothCompactlySupportedW1pGraph (p := p) hU φ ∈
      (w10pGraphClosedSubmodule (p := p) hU).toSubmodule := by
  exact subset_closure
    (LinearMap.mem_range_self
      (smoothCompactlySupportedW1pGraphLinearMap (p := p) hU) φ)

/-- The canonical inclusion of a supported smooth graph point into
`W10pGraph`. -/
noncomputable def smoothCompactlySupportedW1pGraphToW10pGraph
    [Fact (1 ≤ p)] (hU : IsOpen U) (φ : WeakTestFunction U) :
    W10pGraph (p := p) hU :=
  ⟨smoothCompactlySupportedW1pGraph (p := p) hU φ,
    smoothCompactlySupportedW1pGraph_mem_w10pGraph (p := p) hU φ⟩

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- A representative-level supported smooth approximation places its graph
class in the canonical complete zero-boundary carrier. -/
theorem mem_w10pGraph_of_supportedSmoothApproximation
    [Fact (1 ≤ p)] (hU : IsOpen U) (u : W1pFunction U p)
    (happrox : u.SupportedSmoothApproximation) :
    u.toW1pGraph ∈ (w10pGraphClosedSubmodule (p := p) hU).toSubmodule := by
  apply (w10pGraphClosedSubmodule (p := p) hU).isClosed.mem_of_tendsto
    (happrox.tendsto_toW1pGraph hU)
  filter_upwards with n
  apply smoothCompactlySupportedW1pGraph_mem_w10pGraph (p := p) hU
    (happrox.toWeakTestFunction n)

/-- A hidden supported smooth approximation certificate still gives complete
zero-boundary membership. -/
theorem mem_w10pGraph_of_hasSupportedSmoothApproximation
    [Fact (1 ≤ p)] (hU : IsOpen U) (u : W1pFunction U p)
    (happrox : u.HasSupportedSmoothApproximation) :
    u.toW1pGraph ∈ (w10pGraphClosedSubmodule (p := p) hU).toSubmodule := by
  rcases happrox with ⟨happrox⟩
  exact u.mem_w10pGraph_of_supportedSmoothApproximation hU happrox

end W1pFunction

namespace W10pGraph

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Every complete zero-boundary graph point is a limit of actual bundled
smooth compactly supported test-function images. -/
theorem exists_tendsto_smooth_span
    [Fact (1 ≤ p)] (hU : IsOpen U) (u : W10pGraph (p := p) hU) :
    ∃ v : ℕ → W1pGraph U p,
      (∀ n, v n ∈ smoothCompactlySupportedW1pGraphSubmodule (p := p) hU) ∧
        Tendsto v atTop (𝓝 (u : W1pGraph U p)) := by
  have huClosure :
      (u : W1pGraph U p) ∈
        closure
          ((smoothCompactlySupportedW1pGraphSubmodule (p := p) hU :
            Submodule ℝ (W1pGraph U p)) : Set (W1pGraph U p)) := by
    simpa only [w10pGraphClosedSubmodule,
      Submodule.topologicalClosure_coe] using! u.property
  exact mem_closure_iff_seq_limit.mp huClosure

/-- Every complete zero-boundary graph point is a limit of actual bundled
smooth compactly supported test functions.  This is the density theorem used
by weak-formulation and duality arguments; no finite linear combination is
left unbundled. -/
theorem exists_tendsto_smooth
    [Fact (1 ≤ p)] (hU : IsOpen U) (u : W10pGraph (p := p) hU) :
    ∃ φ : ℕ → WeakTestFunction U,
      Tendsto
        (fun n => smoothCompactlySupportedW1pGraph (p := p) hU (φ n))
        atTop (𝓝 (u : W1pGraph U p)) := by
  rcases exists_tendsto_smooth_span hU u with ⟨v, hv, hvTendsto⟩
  have hactual : ∀ n, ∃ φ : WeakTestFunction U,
      smoothCompactlySupportedW1pGraph (p := p) hU φ = v n := by
    intro n
    rcases hv n with ⟨φ, hφ⟩
    exact ⟨φ, hφ⟩
  choose φ hφ using hactual
  refine ⟨φ, ?_⟩
  simpa only [hφ] using hvTendsto

end W10pGraph

end PDE
