module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares

/-!
# Hörmander hypotheses for the transported operator and its regularisation

Packaging of the bracket check (Proposition 2.1) and of the regularised bracket
check (Proposition 2.1) in the exact shape of the hypotheses of the
Hörmander regularity theorem (`ContDiffOn` of every generator on an open set `Ω` and
`LieAlgebraSpansOn Ω X`), for the field families

* `transportedFields B b : Fin (d + 1) → ℝ^{1+2d} → ℝ^{1+2d}` for `Lop = X_0 + ∑ X_i²`;
* `regularizedFields B b ε : Fin (d + d + 1) → ℝ^{1+2d} → ℝ^{1+2d}` for
  `L_ε = X_0 + ∑ X_i² + ∑ Y_l²`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- Spanning on a set implies spanning on any subset. -/
theorem lieAlgebraSpansOn_mono {k N : ℕ} {Ω Ω' : Set (PDE.Vec N)} (h : Ω' ⊆ Ω)
    {X : Fin (k + 1) → PDE.Vec N → PDE.Vec N} (hX : LieAlgebraSpansOn Ω X) :
    LieAlgebraSpansOn Ω' X :=
  fun x hx => hX x (h hx)

/-- **Proposition 2.1.**  Under the standing hypotheses of the evolution problem
(`B` smooth, symmetric, `lam I ≤ B ≤ Lam I`; `b` smooth with `ξ · Db ξ ≥ m`, `m > 0`), the
generators `X_0, X_1, …, X_d` of `Lop` are smooth on `ℝ^{1+2d}` and generate a Lie algebra
spanning every tangent space.  Valid also when `B` depends on `z`. -/
theorem hormander_hypotheses_transportedFields {lam Lam m : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (hb : IsSmoothDrift b) (hm : 0 < m)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) (Ω : Set (EvolutionVec n)) :
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (transportedFields B b i) Ω) ∧
      LieAlgebraSpansOn Ω (transportedFields B b) :=
  ⟨fun i => (contDiff_transportedFields (contDiff_sqrtCoeffAt_entry hlam hB hell) hb i).contDiffOn,
    lieAlgebraSpansOn_mono (Set.subset_univ Ω)
      (lieAlgebraSpansOn_transportedFields hlam hB hell hb hm hcoerc)⟩

/-- **Proposition 2.1 (bracket part).**  For `ε > 0`, the generators
`X_0, X_i, Y_l` of `L_ε` are smooth and their Lie algebra (indeed the generators themselves)
spans every tangent space of `ℝ^{1+2d}`.  Only `0 < lam`, the lower Loewner bound, `B` smooth
and `b` smooth are used (no drift coercivity is needed for `ε > 0`). -/
theorem hormander_hypotheses_regularizedFields {lam Lam ε : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (hb : IsSmoothDrift b) (hε : 0 < ε)
    (Ω : Set (EvolutionVec n)) :
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (regularizedFields B b ε i) Ω) ∧
      LieAlgebraSpansOn Ω (regularizedFields B b ε) :=
  ⟨fun i =>
    (contDiff_regularizedFields (contDiff_sqrtCoeffAt_entry hlam hB hell) hb ε i).contDiffOn,
    lieAlgebraSpansOn_mono (Set.subset_univ Ω)
      (lieAlgebraSpansOn_regularizedFields (b := b) hlam hell hε)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
