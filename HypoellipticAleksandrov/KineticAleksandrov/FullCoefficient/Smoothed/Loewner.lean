module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Quadratic
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Defs
import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Matrix
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# The averaged coefficient `β`: Loewner bounds

The smoothed Green measure: `(Bν)^δ_τ = β ν^δ_τ` for a Borel symmetric `β` with
`λ I ≤ β ≤ Λ I`.  The raw Radon-Nikodym coefficient satisfies the two-sided bounds only
`ν^δ_τ`-almost everywhere.  They are tested on a countable dense family of directions, so the
exceptional set is Borel, and `averagedCoefficient` replaces `β` by `λ I` there.  The result is
an `IsAdmissibleCoefficient` (everywhere bounds), equal to the raw coefficient almost everywhere.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped ENNReal NNReal Matrix MatrixOrder

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {τ lam Lam : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- A fixed countable dense family of directions in `ℝ^d`. -/
def denseDirections (d : ℕ) : ℕ → PDE.Vec d :=
  TopologicalSpace.denseSeq (PDE.Vec d)

/-- The two-sided quadratic form bounds, tested on the dense directions. -/
def IsGoodCoefficient (lam Lam : ℝ) (A : PDE.Mat d) : Prop :=
  ∀ n, lam * (denseDirections d n ⬝ᵥ denseDirections d n) ≤
      denseDirections d n ⬝ᵥ (A *ᵥ denseDirections d n) ∧
    denseDirections d n ⬝ᵥ (A *ᵥ denseDirections d n) ≤
      Lam * (denseDirections d n ⬝ᵥ denseDirections d n)

theorem continuous_quadForm (A : PDE.Mat d) :
    Continuous fun x : PDE.Vec d => x ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- The bounds on dense directions give the bounds on all directions. -/
theorem quadForm_bounds_of_isGood {A : PDE.Mat d} (h : IsGoodCoefficient lam Lam A)
    (x : PDE.Vec d) :
    lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) ∧ x ⬝ᵥ (A *ᵥ x) ≤ Lam * (x ⬝ᵥ x) := by
  have hc : Continuous fun x : PDE.Vec d => x ⬝ᵥ x := by
    simp only [dotProduct]; fun_prop
  refine (TopologicalSpace.denseRange_denseSeq (PDE.Vec d)).induction_on x
    (p := fun x => lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) ∧ x ⬝ᵥ (A *ᵥ x) ≤ Lam * (x ⬝ᵥ x)) ?_ h
  exact (isClosed_le (continuous_const.mul hc) (continuous_quadForm A)).inter
    (isClosed_le (continuous_quadForm A) (continuous_const.mul hc))

theorem loewner_of_isGood {A : PDE.Mat d} (hA : A.IsSymm) (h : IsGoodCoefficient lam Lam A) :
    lam • (1 : PDE.Mat d) ≤ A ∧ A ≤ Lam • (1 : PDE.Mat d) := by
  refine ⟨HypoellipticAleksandrov.loewner_lower_of_quadraticForm hA fun x => ?_,
    le_smul_one_of_quadraticForm hA fun x => (quadForm_bounds_of_isGood h x).2⟩
  have := (quadForm_bounds_of_isGood h x).1
  rw [PDE.vecNormSq, PDE.vecDot]
  exact this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
