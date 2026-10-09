module

public import Hormander.Interface
public import HypoellipticAleksandrov.KineticAleksandrov.Hormander

/-!
# Hörmander hypoellipticity from the `hormander` package

The statement `exists_smooth_aeRepresentative_of_hormander` is proved from the public facade
`Hormander.Interface.exists_smooth_aeRepresentative` of the `hormander` package
(amelieloher/hoermander-rothschild-stein, Kohn's proof). The package's copies of `LieWord`,
`LieAlgebraSpansOn`, `HasWeakHormanderEquation` and their dependencies over `Fin N → ℝ` are
definitionally the definitions of `HypoellipticAleksandrov.KineticAleksandrov.Hormander` over
`PDE.Vec N`, except that `LieWord` is a separate inductive type; the bracket condition is
transported along the evident evaluation-preserving map of Lie words.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open HypoellipticAleksandrov

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The copy of a Lie word in the `hormander` package. -/
def LieWord.toInterface {k : ℕ} : LieWord k → Hormander.Interface.LieWord k
  | .generator i => .generator i
  | .bracket p q => .bracket p.toInterface q.toInterface

/-- Copying a Lie word preserves its evaluation. -/
theorem LieWord.eval_toInterface {k N : ℕ}
    (X : Fin (k + 1) → PDE.Vec N → PDE.Vec N) (w : LieWord k) :
    Hormander.Interface.LieWord.eval X w.toInterface = LieWord.eval X w := by
  induction w with
  | generator i => rfl
  | bracket p q hp hq =>
      simp only [LieWord.toInterface, Hormander.Interface.LieWord.eval, LieWord.eval, hp, hq]

/-- The bracket condition implies the bracket condition of the `hormander` package. -/
theorem LieAlgebraSpansOn.toInterface {k N : ℕ} {Ω : Set (PDE.Vec N)}
    {X : Fin (k + 1) → PDE.Vec N → PDE.Vec N} (h : LieAlgebraSpansOn Ω X) :
    Hormander.Interface.LieAlgebraSpansOn Ω X := by
  intro x hx
  rw [eq_top_iff, ← h x hx]
  refine Submodule.span_mono ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨w.toInterface, congrFun (LieWord.eval_toInterface X w) x⟩

/-- Hörmander's hypoellipticity theorem for locally integrable weak solutions, from the
public facade of the `hormander` package. -/
theorem exists_smooth_aeRepresentative_of_hormander_aux
    {k N : ℕ} {Ω : Set (PDE.Vec N)}
    (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → PDE.Vec N → PDE.Vec N)
    (c g u : PDE.Vec N → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hEq : HasWeakHormanderEquation Ω X c g u) :
    ∃ f : PDE.Vec N → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f :=
  Hormander.Interface.exists_smooth_aeRepresentative hΩ X c g u hX hspan.toInterface hc hEq

end HypoellipticAleksandrov.KineticAleksandrov
