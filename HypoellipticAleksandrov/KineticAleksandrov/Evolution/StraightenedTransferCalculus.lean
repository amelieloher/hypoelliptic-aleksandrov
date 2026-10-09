module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import PDEFoundation.Sobolev.ClassicalGradient
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.SpatialBlock

/-!
# Chain rule for the block coordinate embeddings

Gradients and Hessians of the restrictions `y ↦ f (pack (y - c) z)` and
`z ↦ f (pack y z)` of a function `f` on `PDE.Vec (n + n)` to the two coordinate blocks are the
corresponding blocks of the gradient and Hessian of `f`.  These are the spatial parts of the
transfer between the straightened variables `(Y, z)` and the absolute variables `(y, z)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov

section CLM

variable (n : ℕ)

/-- The linear inclusion `y ↦ (y, 0)` of the diffused block. -/
def embedYCLM : PDE.Vec n →L[ℝ] PDE.Vec (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => spatialPack y 0
      map_add' := fun y y' => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
      map_smul' := fun c y => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp }

/-- The linear inclusion `z ↦ (0, z)` of the transported block. -/
def embedZCLM : PDE.Vec n →L[ℝ] PDE.Vec (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => spatialPack 0 z
      map_add' := fun z z' => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
      map_smul' := fun c z => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp }

/-- The linear projection onto the diffused block. -/
def projYCLM : PDE.Vec (n + n) →L[ℝ] PDE.Vec n :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialY
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The linear projection onto the transported block. -/
def projZCLM : PDE.Vec (n + n) →L[ℝ] PDE.Vec n :=
  LinearMap.toContinuousLinearMap
    { toFun := spatialZ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable {n}

@[simp] theorem embedYCLM_apply (y : PDE.Vec n) : embedYCLM n y = spatialPack y 0 :=
  rfl

@[simp] theorem embedZCLM_apply (z : PDE.Vec n) : embedZCLM n z = spatialPack 0 z :=
  rfl

@[simp] theorem projYCLM_apply (x : PDE.Vec (n + n)) : projYCLM n x = spatialY x :=
  rfl

@[simp] theorem projZCLM_apply (x : PDE.Vec (n + n)) : projZCLM n x = spatialZ x :=
  rfl

theorem embedYCLM_basisVec (i : Fin n) :
    embedYCLM n (PDE.basisVec i) = PDE.basisVec (Fin.castAdd n i) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [PDE.basisVec_apply, Fin.ext_iff]
  · simp only [embedYCLM_apply, PDE.basisVec_apply]
    have hne : ¬ j.addNat n = Fin.castAdd n i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_addNat] at this
      omega
    simp [hne]

theorem embedZCLM_basisVec (i : Fin n) :
    embedZCLM n (PDE.basisVec i) = PDE.basisVec (Fin.natAdd n i) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [embedZCLM_apply, spatialPack_castAdd, PDE.basisVec_apply, Pi.zero_apply]
    have hne : ¬ Fin.castAdd n j = i.addNat n := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_addNat] at this
      omega
    simp [hne]
  · simp [PDE.basisVec_apply, Fin.ext_iff]

end CLM

section Slices

variable {n : ℕ}

theorem hasFDerivAt_pack_left (c z y : PDE.Vec n) :
    HasFDerivAt (fun y' : PDE.Vec n => spatialPack (y' - c) z) (embedYCLM n) y := by
  have h := (embedYCLM n).hasFDerivAt (x := y) |>.add_const (spatialPack (-c) z)
  convert h using 1
  funext y'
  rw [embedYCLM_apply, ← spatialPack_add, sub_eq_add_neg, zero_add]

theorem hasFDerivAt_pack_right (w z : PDE.Vec n) :
    HasFDerivAt (fun z' : PDE.Vec n => spatialPack w z') (embedZCLM n) z := by
  have h := (embedZCLM n).hasFDerivAt (x := z) |>.add_const (spatialPack w 0)
  convert h using 1
  funext z'
  rw [embedZCLM_apply, ← spatialPack_add, add_zero, zero_add]

/-- Gradient of a restriction along an affine block embedding. -/
theorem classicalGradient_comp_block
    {f : PDE.Vec (n + n) → ℝ} {ι : PDE.Vec n → PDE.Vec (n + n)}
    {E : PDE.Vec n →L[ℝ] PDE.Vec (n + n)} {y : PDE.Vec n} (hι : HasFDerivAt ι E y)
    (hf : DifferentiableAt ℝ f (ι y)) {e : Fin n → Fin (n + n)}
    (he : ∀ i, E (PDE.basisVec i) = PDE.basisVec (e i)) :
    PDE.classicalGradient (fun y' => f (ι y')) y =
      fun i => PDE.classicalGradient f (ι y) (e i) := by
  funext i
  have h := hf.hasFDerivAt.comp y hι
  simp only [PDE.classicalGradient_apply]
  rw [show fderiv ℝ (fun y' => f (ι y')) y = (fderiv ℝ f (ι y)).comp E from h.fderiv]
  simp [he]

/-- The gradient of a `C²` function is differentiable. -/
theorem differentiableAt_classicalGradient {m : ℕ} {f : PDE.Vec m → ℝ} {x : PDE.Vec m}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (PDE.classicalGradient f) x := by
  refine differentiableAt_pi.2 fun i => ?_
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero

/-- Hessian of a restriction along an affine block embedding. -/
theorem hessian_comp_block
    {f : PDE.Vec (n + n) → ℝ} {ι : PDE.Vec n → PDE.Vec (n + n)}
    {E : PDE.Vec n →L[ℝ] PDE.Vec (n + n)} {y : PDE.Vec n} (hι : ∀ y', HasFDerivAt ι E y')
    (hf : ContDiffAt ℝ 2 f (ι y)) {e : Fin n → Fin (n + n)}
    (he : ∀ i, E (PDE.basisVec i) = PDE.basisVec (e i)) (i j : Fin n) :
    (fderiv ℝ (fun y' => PDE.classicalGradient (fun w => f (ι w)) y') y (PDE.basisVec i)) j =
      (fderiv ℝ (PDE.classicalGradient f) (ι y) (PDE.basisVec (e i))) (e j) := by
  set P : PDE.Vec (n + n) →L[ℝ] PDE.Vec n :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) (e j)
    with hP
  have hPapply : ∀ v j, P v j = v (e j) := fun v j => rfl
  have hev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ f (ι y') := by
    have h1 : ∀ᶠ x in 𝓝 (ι y), ContDiffAt ℝ 2 f x := hf.eventually (by simp)
    exact (hι y).continuousAt.eventually h1 |>.mono fun y' h => h.differentiableAt (by norm_num)
  have heq : (fun y' => PDE.classicalGradient (fun w => f (ι w)) y') =ᶠ[𝓝 y]
      fun y' => P (PDE.classicalGradient f (ι y')) := by
    filter_upwards [hev] with y' hy'
    rw [classicalGradient_comp_block (hι y') hy' he]
    rfl
  have hD := (differentiableAt_classicalGradient hf).hasFDerivAt
  have hcomp : HasFDerivAt (fun y' => P (PDE.classicalGradient f (ι y')))
      (P.comp ((fderiv ℝ (PDE.classicalGradient f) (ι y)).comp E)) y :=
    P.hasFDerivAt.comp y (hD.comp y (hι y))
  have hfin := hcomp.congr_of_eventuallyEq heq
  rw [hfin.fderiv]
  change P (fderiv ℝ (PDE.classicalGradient f) (ι y) (E (PDE.basisVec i))) j = _
  rw [he i, hPapply]

end Slices

end HypoellipticAleksandrov.KineticAleksandrov
