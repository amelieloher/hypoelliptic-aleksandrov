module

public import PDEFoundation.Sobolev.H1.Graph
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Hilbert realization of the complete `H¹` graph

`H1Graph U` deliberately inherits the maximum norm on the product used by the
general-`p` graph.  At `p = 2`, Lax--Milgram and Riesz representation instead
need the equivalent `ℓ²` product norm.  This file pulls the same closed graph
back through `WithLp.prodContinuousLinearEquiv`; it does not conflate the two
norms.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace PDE

/-- The `ℓ²`-normed product ambient for the `p = 2` weak-gradient graph. -/
abbrev H1HilbertAmbient {d : ℕ} (U : Set (Vec d)) :=
  WithLp 2
    (ScalarLp U (2 : ℝ≥0∞) × HilbertVectorLp U (2 : ℝ≥0∞))

/-- The standard continuous linear equivalence from the `ℓ²` product
realization to the ordinary product carrier. -/
abbrev h1HilbertAmbientEquiv {d : ℕ} (U : Set (Vec d)) :
    H1HilbertAmbient U ≃L[ℝ]
      WeakGradientLpPair U (2 : ℝ≥0∞) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ
    (ScalarLp U (2 : ℝ≥0∞))
    (HilbertVectorLp U (2 : ℝ≥0∞))

/-- The same weak-gradient graph, pulled back to the Hilbert product norm. -/
abbrev h1HilbertClosedSubmodule {d : ℕ} (U : Set (Vec d)) :
    ClosedSubmodule ℝ (H1HilbertAmbient U) :=
  (weakGradientGraph U (2 : ℝ≥0∞)).comap
    (h1HilbertAmbientEquiv U).toContinuousLinearMap

/-- Submodule view used to inherit the Hilbert-space instances. -/
abbrev h1HilbertSubmodule {d : ℕ} (U : Set (Vec d)) :
    Submodule ℝ (H1HilbertAmbient U) :=
  (h1HilbertClosedSubmodule U).toSubmodule

/-- The complete Hilbert realization of `H1Graph U`. -/
abbrev H1HilbertGraph {d : ℕ} (U : Set (Vec d)) :=
  ↥(h1HilbertSubmodule U)

namespace H1HilbertGraph

variable {d : ℕ} {U : Set (Vec d)}

noncomputable instance : SeminormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (SeminormedAddCommGroup (h1HilbertSubmodule U))

noncomputable instance : NormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedAddCommGroup (h1HilbertSubmodule U))

noncomputable instance : NormedSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedSpace ℝ (h1HilbertSubmodule U))

noncomputable instance : InnerProductSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (InnerProductSpace ℝ (h1HilbertSubmodule U))

noncomputable instance : CompleteSpace (H1HilbertGraph U) := by
  exact (h1HilbertClosedSubmodule U).isClosed.completeSpace_coe

/-- Forget the Hilbert product norm while retaining the same graph pair. -/
def toH1Graph (z : H1HilbertGraph U) : H1Graph U :=
  ⟨h1HilbertAmbientEquiv U z.1, z.2⟩

/-- Equip a point of the maximum-norm graph with the equivalent Hilbert
product norm. -/
def ofH1Graph (z : H1Graph U) : H1HilbertGraph U :=
  ⟨(h1HilbertAmbientEquiv U).symm z.1, by
    change
      h1HilbertAmbientEquiv U
          ((h1HilbertAmbientEquiv U).symm z.1) ∈
        weakGradientGraph U (2 : ℝ≥0∞)
    rw [(h1HilbertAmbientEquiv U).apply_symm_apply]
    exact z.2⟩

@[simp]
theorem toH1Graph_ofH1Graph (z : H1Graph U) :
    toH1Graph (ofH1Graph z) = z := by
  apply Subtype.ext
  exact (h1HilbertAmbientEquiv U).apply_symm_apply z.1

@[simp]
theorem ofH1Graph_toH1Graph (z : H1HilbertGraph U) :
    ofH1Graph (toH1Graph z) = z := by
  apply Subtype.ext
  exact (h1HilbertAmbientEquiv U).symm_apply_apply z.1

/-- The max-norm and Hilbert-norm graph carriers have exactly the same
elements. Their norms remain intentionally distinct. -/
def equivH1Graph : H1HilbertGraph U ≃ H1Graph U where
  toFun := toH1Graph
  invFun := ofH1Graph
  left_inv := ofH1Graph_toH1Graph
  right_inv := toH1Graph_ofH1Graph

/-- Scalar `L²` value component. -/
abbrev value (z : H1HilbertGraph U) :
    ScalarLp U (2 : ℝ≥0∞) :=
  z.1.fst

/-- Euclidean Hilbert-vector `L²` gradient component. -/
abbrev gradient (z : H1HilbertGraph U) :
    HilbertVectorLp U (2 : ℝ≥0∞) :=
  z.1.snd

/-- Continuous scalar-value projection from the Hilbert graph. -/
def valueCLM :
    H1HilbertGraph U →L[ℝ] ScalarLp U (2 : ℝ≥0∞) :=
  (WithLp.fstL
      (p := 2) (𝕜 := ℝ)
      (α := ScalarLp U (2 : ℝ≥0∞))
      (β := HilbertVectorLp U (2 : ℝ≥0∞))).comp
    (h1HilbertSubmodule U).subtypeL

@[simp]
theorem valueCLM_apply (z : H1HilbertGraph U) :
    valueCLM z = value z :=
  rfl

/-- Continuous Euclidean-gradient projection from the Hilbert graph. -/
def gradientCLM :
    H1HilbertGraph U →L[ℝ]
      HilbertVectorLp U (2 : ℝ≥0∞) :=
  (WithLp.sndL
      (p := 2) (𝕜 := ℝ)
      (α := ScalarLp U (2 : ℝ≥0∞))
      (β := HilbertVectorLp U (2 : ℝ≥0∞))).comp
    (h1HilbertSubmodule U).subtypeL

@[simp]
theorem gradientCLM_apply (z : H1HilbertGraph U) :
    gradientCLM z = gradient z :=
  rfl

end H1HilbertGraph

end PDE
