module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import PDEFoundation.Ambient.Basic

/-!
# Coordinates for the transported evolution operator

The transported operator `Lop = ∂_σ + B(σ,v,z) : D_v² + b(v) · ∇_z` lives on `ℝ^{1+2d}`.
This module fixes the coordinate convention used by the Hörmander bracket check.

A point of `EvolutionVec n = PDE.Vec (n + n + 1)` is read as `(σ, v, z)`:

* index `0` is the time coordinate `σ`;
* indices `succ (castAdd n i)` are the diffused coordinates `v_i` (the `position` field of a
  `KineticPoint`, the `y` variable of `transportedForwardOperator`);
* indices `succ (natAdd n l)` are the transported coordinates `z_l` (the `velocity` field of a
  `KineticPoint`).

`packPoint s v z` assembles a point, and `timeCoord`, `diffusedCoord`, `transportedCoord` are
the (continuous linear) coordinate projections.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

/-- The ambient dimension `1 + 2d` of the transported evolution problem (written
`d + d + 1`, so that `Fin.cons` and `Fin.append` apply). -/
abbrev EvolutionDim (n : ℕ) : ℕ := n + n + 1

/-- The Euclidean carrier `ℝ^{1+2d}` of the transported evolution problem. -/
abbrev EvolutionVec (n : ℕ) : Type := PDE.Vec (EvolutionDim n)

variable {n : ℕ}

/-- Assemble a point `(σ, v, z)` of `ℝ^{1+2d}`: time `σ`, diffused coordinate `v`,
transported coordinate `z`. -/
def packPoint (s : ℝ) (v z : PDE.Vec n) : EvolutionVec n :=
  Fin.cons s (Fin.append v z)

variable (n) in
/-- The time coordinate `σ`. -/
def timeCoord : EvolutionVec n →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (EvolutionDim n) => ℝ) 0

variable (n) in
/-- The diffused coordinate `v ∈ ℝ^d` (the `y` variable of the transported operator). -/
def diffusedCoord : EvolutionVec n →L[ℝ] PDE.Vec n :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (EvolutionDim n) => ℝ)
      (Fin.succ (Fin.castAdd n i))

variable (n) in
/-- The transported coordinate `z ∈ ℝ^d`. -/
def transportedCoord : EvolutionVec n →L[ℝ] PDE.Vec n :=
  ContinuousLinearMap.pi fun l =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (EvolutionDim n) => ℝ)
      (Fin.succ (Fin.natAdd n l))

@[simp] theorem timeCoord_apply (x : EvolutionVec n) : timeCoord n x = x 0 := rfl

@[simp] theorem diffusedCoord_apply (x : EvolutionVec n) (i : Fin n) :
    diffusedCoord n x i = x (Fin.succ (Fin.castAdd n i)) := rfl

@[simp] theorem transportedCoord_apply (x : EvolutionVec n) (l : Fin n) :
    transportedCoord n x l = x (Fin.succ (Fin.natAdd n l)) := rfl

@[simp] theorem packPoint_zero_apply (s : ℝ) (v z : PDE.Vec n) : packPoint s v z 0 = s := by
  simp only [packPoint, Fin.cons_zero]

@[simp] theorem packPoint_diffused_apply (s : ℝ) (v z : PDE.Vec n) (i : Fin n) :
    packPoint s v z (Fin.succ (Fin.castAdd n i)) = v i := by
  simp only [packPoint, Fin.cons_succ, Fin.append_left]

@[simp] theorem packPoint_transported_apply (s : ℝ) (v z : PDE.Vec n) (l : Fin n) :
    packPoint s v z (Fin.succ (Fin.natAdd n l)) = z l := by
  simp only [packPoint, Fin.cons_succ, Fin.append_right]

@[simp] theorem timeCoord_packPoint (s : ℝ) (v z : PDE.Vec n) :
    timeCoord n (packPoint s v z) = s := by
  rw [timeCoord_apply, packPoint_zero_apply]

@[simp] theorem diffusedCoord_packPoint (s : ℝ) (v z : PDE.Vec n) :
    diffusedCoord n (packPoint s v z) = v := by
  ext i
  rw [diffusedCoord_apply, packPoint_diffused_apply]

@[simp] theorem transportedCoord_packPoint (s : ℝ) (v z : PDE.Vec n) :
    transportedCoord n (packPoint s v z) = z := by
  ext l
  rw [transportedCoord_apply, packPoint_transported_apply]

/-- Two points are equal iff their three coordinate blocks are equal. -/
theorem ext_coords {x y : EvolutionVec n} (ht : timeCoord n x = timeCoord n y)
    (hv : diffusedCoord n x = diffusedCoord n y)
    (hz : transportedCoord n x = transportedCoord n y) : x = y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ht
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simpa using congrFun hv a
    · simpa using congrFun hz b

/-- Every point is the pack of its coordinates. -/
@[simp] theorem packPoint_coords (x : EvolutionVec n) :
    packPoint (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) = x :=
  ext_coords (by simp) (by simp) (by simp)

theorem packPoint_injective {s s' : ℝ} {v v' z z' : PDE.Vec n}
    (h : packPoint s v z = packPoint s' v' z') : s = s' ∧ v = v' ∧ z = z' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (timeCoord n) h
  · simpa using congrArg (diffusedCoord n) h
  · simpa using congrArg (transportedCoord n) h

theorem packPoint_add (s s' : ℝ) (v v' z z' : PDE.Vec n) :
    packPoint (s + s') (v + v') (z + z') = packPoint s v z + packPoint s' v' z' :=
  ext_coords (by simp) (by simp) (by simp)

theorem packPoint_smul (c s : ℝ) (v z : PDE.Vec n) :
    packPoint (c * s) (c • v) (c • z) = c • packPoint s v z :=
  ext_coords (by simp) (by simp) (by simp)

@[simp] theorem packPoint_zero : packPoint (0 : ℝ) (0 : PDE.Vec n) (0 : PDE.Vec n) = 0 :=
  ext_coords (by simp) (by simp) (by simp)

theorem packPoint_sub (s s' : ℝ) (v v' z z' : PDE.Vec n) :
    packPoint (s - s') (v - v') (z - z') = packPoint s v z - packPoint s' v' z' :=
  ext_coords (by simp) (by simp) (by simp)

/-- A point splits as time part, diffused part and transported part. -/
theorem packPoint_eq_add (s : ℝ) (v z : PDE.Vec n) :
    packPoint s v z = packPoint s 0 0 + packPoint 0 v 0 + packPoint 0 0 z := by
  rw [← packPoint_add, ← packPoint_add]
  simp

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
