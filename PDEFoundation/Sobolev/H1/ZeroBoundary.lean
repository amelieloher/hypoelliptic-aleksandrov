module

public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-!
# Zero-boundary `H¹` graph

This file is the `p = 2` facade for the canonical zero-boundary graph from
`PDEFoundation.Sobolev.W1p.ZeroBoundary`.  In particular, `H10Graph hU` is
definitionally the closure in `H1Graph U` of the range of actual bundled
smooth compactly supported test functions.  No second weak-gradient relation
or boundary-condition predicate is introduced here.

For compatibility with `LeanIntoHomogenization`, the file also exposes its
representative-level `H10Function` field surface.  That structure merely
bundles an `H1Function` with the same supported smooth approximation
certificate used to enter the closed graph.

## Main definitions

- `H10Function`: the LIH-compatible representative facade.
- `MemH10`: concrete-function membership through that facade.
- `h10GraphClosedSubmodule`: the closed `H¹₀` submodule of `H1Graph U`.
- `H10Graph`: its complete carrier.
- `H1Function.SupportedSmoothApproximation`: the exact representative-level
  `p = 2` specialization of the generic certificate.

## Main results

- `H1Function.mem_h10Graph_of_supportedSmoothApproximation` sends an explicit
  supported approximation to the complete carrier.
- `H10Graph.exists_tendsto_smooth` supplies actual bundled test functions
  converging to every point of the complete carrier.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter

variable {d : ℕ} {U : Set (Vec d)}

/-- A representative-level `H¹₀(U)` witness with the exact field surface used
by `LeanIntoHomogenization`.

The additional fields are precisely a supported smooth approximation
certificate for `toH1Function`; they do not define a second boundary
condition. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => approx n x - toH1Function.toFun x)
          (2 : ℝ≥0∞) (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (approx n) x) (basisVec i) -
                toH1Function.grad x i)
            (2 : ℝ≥0∞) (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance : CoeFun (H10Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function.toFun

/-- Representative-level membership of a concrete function in `H¹₀(U)`.
This is the LIH-compatible existential wrapper around `H10Function`. -/
def MemH10 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H10Function U, v.toH1Function.toFun = u

/-- The canonical closed `H¹₀(U)` submodule, definitionally inherited from
the generic `W¹,p` zero-boundary construction at `p = 2`. -/
noncomputable abbrev h10GraphClosedSubmodule (hU : IsOpen U) :
    ClosedSubmodule ℝ (H1Graph U) :=
  w10pGraphClosedSubmodule (p := (2 : ℝ≥0∞)) hU

/-- The canonical complete quotient-level `H¹₀(U)` carrier. -/
noncomputable abbrev H10Graph (hU : IsOpen U) :=
  W10pGraph (p := (2 : ℝ≥0∞)) hU

/-- The `H¹` graph point associated to an actual bundled smooth compactly
supported test function. -/
noncomputable abbrev smoothCompactlySupportedH1Graph (hU : IsOpen U)
    (φ : WeakTestFunction U) : H1Graph U :=
  smoothCompactlySupportedW1pGraph (p := (2 : ℝ≥0∞)) hU φ

/-- The `H¹` graph-level submodule of actual bundled smooth compactly
supported test functions. -/
noncomputable abbrev smoothCompactlySupportedH1GraphSubmodule (hU : IsOpen U) :
    Submodule ℝ (H1Graph U) :=
  smoothCompactlySupportedW1pGraphSubmodule (p := (2 : ℝ≥0∞)) hU

/-- The actual smooth test-function image belongs to the canonical
zero-boundary `H¹` graph. -/
theorem smoothCompactlySupportedH1Graph_mem_h10Graph
    (hU : IsOpen U) (φ : WeakTestFunction U) :
    smoothCompactlySupportedH1Graph hU φ ∈
      (h10GraphClosedSubmodule hU).toSubmodule :=
  smoothCompactlySupportedW1pGraph_mem_w10pGraph (p := (2 : ℝ≥0∞)) hU φ

/-- The canonical inclusion of an actual smooth test function into
`H10Graph`. -/
noncomputable abbrev smoothCompactlySupportedH1GraphToH10Graph
    (hU : IsOpen U) (φ : WeakTestFunction U) : H10Graph hU :=
  smoothCompactlySupportedW1pGraphToW10pGraph (p := (2 : ℝ≥0∞)) hU φ

namespace H1Function

variable {u : H1Function U}

/-- Explicit supported smooth approximation data for an `H1Function`,
definitionally the generic `W¹,2` certificate. -/
abbrev SupportedSmoothApproximation (u : H1Function U) : Type :=
  W1pFunction.SupportedSmoothApproximation u.toW1pFunction

/-- Proposition-valued supported smooth approximability for an
`H1Function`. -/
abbrev HasSupportedSmoothApproximation (u : H1Function U) : Prop :=
  W1pFunction.HasSupportedSmoothApproximation u.toW1pFunction

/-- Bundle an `H1Function` with an explicit supported smooth approximation.
This is the representative facade constructor; it adds no data beyond the
certificate. -/
def toH10Function (u : H1Function U)
    (happrox : u.SupportedSmoothApproximation) : H10Function U where
  toH1Function := u
  approx := happrox.approx
  approx_smooth := happrox.approx_smooth
  approx_hasCompactSupport := happrox.approx_hasCompactSupport
  approx_support_subset := happrox.approx_tsupport_subset
  tendsto_approx := happrox.tendsto_value
  tendsto_approx_grad := happrox.tendsto_grad

@[simp]
theorem toH10Function_toH1Function (u : H1Function U)
    (happrox : u.SupportedSmoothApproximation) :
    (u.toH10Function happrox).toH1Function = u :=
  rfl

/-- An explicit supported smooth approximation gives LIH-style
representative-level `H¹₀` membership. -/
theorem memH10_of_supportedSmoothApproximation (u : H1Function U)
    (happrox : u.SupportedSmoothApproximation) :
    MemH10 U u.toFun :=
  ⟨u.toH10Function happrox, rfl⟩

/-- A hidden supported smooth approximation still gives LIH-style
representative-level `H¹₀` membership. -/
theorem memH10_of_hasSupportedSmoothApproximation (u : H1Function U)
    (happrox : u.HasSupportedSmoothApproximation) :
    MemH10 U u.toFun := by
  rcases happrox with ⟨happrox⟩
  exact u.memH10_of_supportedSmoothApproximation happrox

/-- Regard a member of an `H¹` supported approximation as an actual bundled
smooth compactly supported test function. -/
noncomputable abbrev SupportedSmoothApproximation.toWeakTestFunction
    (happrox : u.SupportedSmoothApproximation) (n : ℕ) : WeakTestFunction U :=
  W1pFunction.SupportedSmoothApproximation.toWeakTestFunction happrox n

/-- An explicit supported smooth approximation converges to the exact
representative-to-graph image in `H1Graph`. -/
theorem SupportedSmoothApproximation.tendsto_toH1Graph
    (hU : IsOpen U) (happrox : u.SupportedSmoothApproximation) :
    Tendsto
      (fun n => smoothCompactlySupportedH1Graph hU
        (happrox.toWeakTestFunction n))
      atTop (𝓝 u.toW1pFunction.toW1pGraph) :=
  happrox.tendsto_toW1pGraph hU

/-- An explicit supported smooth approximation puts the representative's
graph image in the canonical complete `H¹₀` carrier. -/
theorem mem_h10Graph_of_supportedSmoothApproximation
    (hU : IsOpen U) (u : H1Function U)
    (happrox : u.SupportedSmoothApproximation) :
    u.toW1pFunction.toW1pGraph ∈ (h10GraphClosedSubmodule hU).toSubmodule :=
  u.toW1pFunction.mem_w10pGraph_of_supportedSmoothApproximation hU happrox

/-- A hidden supported smooth approximation certificate still gives
membership in the canonical complete `H¹₀` carrier. -/
theorem mem_h10Graph_of_hasSupportedSmoothApproximation
    (hU : IsOpen U) (u : H1Function U)
    (happrox : u.HasSupportedSmoothApproximation) :
    u.toW1pFunction.toW1pGraph ∈ (h10GraphClosedSubmodule hU).toSubmodule :=
  u.toW1pFunction.mem_w10pGraph_of_hasSupportedSmoothApproximation hU happrox

end H1Function

namespace H10Function

variable {u : H10Function U}

@[ext]
theorem ext {u v : H10Function U}
    (htoH1Function : u.toH1Function = v.toH1Function)
    (happrox : u.approx = v.approx) : u = v := by
  cases u
  cases v
  cases htoH1Function
  cases happrox
  rfl

/-- Forget the representative-level approximation data. -/
theorem memH1 (u : H10Function U) :
    MemH1 U u.toH1Function.toFun :=
  u.toH1Function.memH1

/-- Every `H10Function` represents a member of the LIH-compatible
representative-level predicate. -/
theorem memH10 (u : H10Function U) :
    MemH10 U u.toH1Function.toFun :=
  ⟨u, rfl⟩

/-- Recover the exact supported smooth approximation certificate bundled by an
`H10Function`. -/
def supportedSmoothApproximation (u : H10Function U) :
    u.toH1Function.SupportedSmoothApproximation where
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_tsupport_subset := u.approx_support_subset
  tendsto_value := u.tendsto_approx
  tendsto_grad := u.tendsto_approx_grad

/-- Every `H10Function` exposes the proposition-valued form of its exact
supported smooth approximation certificate. -/
theorem hasSupportedSmoothApproximation (u : H10Function U) :
    u.toH1Function.HasSupportedSmoothApproximation :=
  ⟨u.supportedSmoothApproximation⟩

@[simp]
theorem supportedSmoothApproximation_toH10Function (u : H10Function U) :
    u.toH1Function.toH10Function u.supportedSmoothApproximation = u := by
  cases u
  rfl

/-- The `n`th approximation bundled by an `H10Function`, exposed as an actual
smooth compactly supported test function. -/
noncomputable abbrev toWeakTestFunction (u : H10Function U) (n : ℕ) :
    WeakTestFunction U :=
  u.supportedSmoothApproximation.toWeakTestFunction n

@[simp]
theorem toWeakTestFunction_toFun (u : H10Function U) (n : ℕ) :
    (u.toWeakTestFunction n).toFun = u.approx n :=
  rfl

/-- The bundled actual test functions converge to the graph image of the
underlying representative. -/
theorem tendsto_toH1Graph (hU : IsOpen U) (u : H10Function U) :
    Tendsto
      (fun n =>
        smoothCompactlySupportedH1Graph hU (u.toWeakTestFunction n))
      atTop (𝓝 u.toH1Function.toW1pFunction.toW1pGraph) :=
  u.supportedSmoothApproximation.tendsto_toH1Graph hU

/-- The graph image of an `H10Function` belongs to the same canonical closed
`H10Graph` used by the quotient-level API. -/
theorem mem_h10Graph (hU : IsOpen U) (u : H10Function U) :
    u.toH1Function.toW1pFunction.toW1pGraph ∈
      (h10GraphClosedSubmodule hU).toSubmodule :=
  u.toH1Function.mem_h10Graph_of_supportedSmoothApproximation
    hU u.supportedSmoothApproximation

/-- Send a representative-level `H10Function` to its canonical complete graph
point. -/
noncomputable def toH10Graph (hU : IsOpen U) (u : H10Function U) :
    H10Graph hU :=
  ⟨u.toH1Function.toW1pFunction.toW1pGraph, u.mem_h10Graph hU⟩

@[simp]
theorem coe_toH10Graph (hU : IsOpen U) (u : H10Function U) :
    (u.toH10Graph hU : H1Graph U) =
      u.toH1Function.toW1pFunction.toW1pGraph :=
  rfl

/-- Package a globally smooth compactly supported function as an
LIH-compatible representative-level `H¹₀` test.

The underlying `H1Function` is the existing `W1pFunction.ofContDiff`
constructor at `p = 2`; the constant approximation sequence is only its
supported-smooth certificate. -/
noncomputable def ofContDiff (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hsub : tsupport f ⊆ U) :
    H10Function U where
  toH1Function :=
    (W1pFunction.ofContDiff hU (hf.of_le (by simp)) hcompact
      (2 : ℝ≥0∞)).toH1Function
  approx := fun _ => f
  approx_smooth := fun _ => hf
  approx_hasCompactSupport := fun _ => hcompact
  approx_support_subset := fun _ => hsub
  tendsto_approx := by
    simpa only [W1pFunction.ofContDiff, W1pFunction.toH1Function_toFun,
      sub_self, MeasureTheory.eLpNorm_fun_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  tendsto_approx_grad := by
    intro i
    simpa only [W1pFunction.ofContDiff, W1pFunction.toH1Function_grad,
      sub_self, MeasureTheory.eLpNorm_fun_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

@[simp]
theorem ofContDiff_toFun (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hsub : tsupport f ⊆ U) :
    (ofContDiff hU hf hcompact hsub).toH1Function.toFun = f :=
  rfl

@[simp]
theorem ofContDiff_grad (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hsub : tsupport f ⊆ U) :
    (ofContDiff hU hf hcompact hsub).toH1Function.grad =
      fun x i => (fderiv ℝ f x) (basisVec i) :=
  rfl

@[simp]
theorem ofContDiff_approx (hU : IsOpen U)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hsub : tsupport f ⊆ U)
    (n : ℕ) :
    (ofContDiff hU hf hcompact hsub).approx n = f :=
  rfl

end H10Function

namespace H1Function

@[simp]
theorem toH10Function_supportedSmoothApproximation
    (u : H1Function U) (happrox : u.SupportedSmoothApproximation) :
    (u.toH10Function happrox).supportedSmoothApproximation = happrox := by
  cases happrox
  rfl

end H1Function

/-- Representative-level `H¹₀` membership implies representative-level
`H¹` membership without changing the concrete function. -/
theorem memH1_of_memH10 {u : Vec d → ℝ} (hu : MemH10 U u) :
    MemH1 U u := by
  rcases hu with ⟨v, rfl⟩
  exact v.memH1

namespace H10Graph

/-- Every complete `H¹₀` graph point is a limit of points in the smooth
test-function range submodule. -/
theorem exists_tendsto_smooth_span (hU : IsOpen U) (u : H10Graph hU) :
    ∃ v : ℕ → H1Graph U,
      (∀ n, v n ∈ smoothCompactlySupportedH1GraphSubmodule hU) ∧
        Tendsto v atTop (𝓝 (u : H1Graph U)) :=
  W10pGraph.exists_tendsto_smooth_span (p := (2 : ℝ≥0∞)) hU u

/-- Every complete `H¹₀` graph point is a limit of actual bundled smooth
compactly supported test functions. -/
theorem exists_tendsto_smooth (hU : IsOpen U) (u : H10Graph hU) :
    ∃ φ : ℕ → WeakTestFunction U,
      Tendsto (fun n => smoothCompactlySupportedH1Graph hU (φ n))
        atTop (𝓝 (u : H1Graph U)) :=
  W10pGraph.exists_tendsto_smooth (p := (2 : ℝ≥0∞)) hU u

end H10Graph

end PDE
