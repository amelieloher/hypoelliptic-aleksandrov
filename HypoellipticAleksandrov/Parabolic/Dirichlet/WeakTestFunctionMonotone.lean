module

public import PDEFoundation.Sobolev.WeakDerivative

/-!
# Monotonicity of spatial weak test functions

This module lifts a weak test function to any larger spatial carrier without changing its
underlying global function.
-/

@[expose] public section

namespace PDE

/-- Regard a weak test function on `O` as a weak test function on a larger set `Ω`. -/
def WeakTestFunction.mono {d : ℕ} {O Ω : Set (Vec d)}
    (ψ : WeakTestFunction O) (hOΩ : O ⊆ Ω) : WeakTestFunction Ω where
  toFun := ψ.toFun
  contDiff := ψ.contDiff
  hasCompactSupport := ψ.hasCompactSupport
  tsupport_subset := ψ.tsupport_subset.trans hOΩ

@[simp] theorem WeakTestFunction.mono_apply {d : ℕ} {O Ω : Set (Vec d)}
    (ψ : WeakTestFunction O) (hOΩ : O ⊆ Ω) (y : Vec d) :
    ψ.mono hOΩ y = ψ y :=
  rfl

@[simp] theorem WeakTestFunction.mono_partialDeriv {d : ℕ} {O Ω : Set (Vec d)}
    (ψ : WeakTestFunction O) (hOΩ : O ⊆ Ω) (i : Fin d) (y : Vec d) :
    (ψ.mono hOΩ).partialDeriv i y = ψ.partialDeriv i y :=
  rfl

end PDE
