module

public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketCoord
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSqrt
public import HypoellipticAleksandrov.KineticAleksandrov.Hormander

/-!
# The Hörmander vector fields of the transported operator

For the transported operator `Lop = ∂_σ + B(σ,v,z) : D_v² + b(v) · ∇_z` with `β = B^{1/2}` the
smooth positive square root, the source (Proposition 2.1) puts

* `X_i = ∑_j β_ij ∂_{v_j}`, `i = 1, …, d`;
* `c_k = ∑_{i,j} β_ij ∂_{v_j} β_ik`;
* `X_0 = ∂_σ + b(v) · ∇_z - ∑_k c_k ∂_{v_k}`,

so that `Lop = X_0 + ∑_i X_i²`.  For the regularised operator `L_ε = Lop + ε Δ_z`
(Proposition 2.1) one adds the constant fields `Y_l = √ε ∂_{z_l}`.

This module defines these fields as maps `ℝ^{1+2d} → ℝ^{1+2d}` in the coordinates of
`BracketCoord`, with the generator ordering expected by the Hörmander carriers
(`X 0` is the drift, `X i.succ` are the squared fields), and proves smoothness.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- The matrix `β(x) = B(σ,v,z)^{1/2}` at the point `x = (σ, v, z)` (positive square root
of the coefficient matrix). -/
def sqrtCoeffAt (B : FullKineticCoefficient n) (x : EvolutionVec n) : PDE.Mat n :=
  CFC.sqrt (B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x))

/-- The diffusion field `X_i = ∑_j β_ij ∂_{v_j}`. -/
def diffusionField (B : FullKineticCoefficient n) (i : Fin n) (x : EvolutionVec n) :
    EvolutionVec n :=
  packPoint 0 (fun j => sqrtCoeffAt B x i j) 0

/-- The drift correction `c_k = ∑_{i,j} β_ij ∂_{v_j} β_ik`. -/
def driftCorrection (B : FullKineticCoefficient n) (k : Fin n) (x : EvolutionVec n) : ℝ :=
  ∑ i, ∑ j, sqrtCoeffAt B x i j *
    fderiv ℝ (fun y => sqrtCoeffAt B y i k) x (packPoint 0 (Pi.single j 1) 0)

/-- The drift field `X_0 = ∂_σ + b(v) · ∇_z - ∑_k c_k ∂_{v_k}`. -/
def driftField (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (x : EvolutionVec n) : EvolutionVec n :=
  packPoint 1 (fun k => - driftCorrection B k x) (b (diffusedCoord n x))

/-- The constant regularising field `Y_l = √ε ∂_{z_l}` of `L_ε = Lop + ε Δ_z`. -/
def regularizingField (ε : ℝ) (l : Fin n) (_x : EvolutionVec n) : EvolutionVec n :=
  packPoint 0 0 (Pi.single l (Real.sqrt ε))

/-- The Hörmander generators of `Lop = X_0 + ∑ X_i²`: `X 0` is the drift `X_0` and
`X i.succ = X_i`.  (`k = d`, so this is a `Fin (d + 1)`-indexed family.) -/
def transportedFields (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) :
    Fin (n + 1) → EvolutionVec n → EvolutionVec n :=
  Fin.cons (driftField B b) (diffusionField B)

/-- The Hörmander generators of `L_ε = Lop + ε Δ_z = X_0 + ∑ X_i² + ∑ Y_l²`: `X 0` is the
drift `X_0`, then the `d` fields `X_i`, then the `d` fields `Y_l = √ε ∂_{z_l}`. -/
def regularizedFields (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ) :
    Fin (n + n + 1) → EvolutionVec n → EvolutionVec n :=
  Fin.cons (driftField B b) (Fin.append (diffusionField B) (regularizingField ε))

/-! ## Smoothness -/

theorem contDiff_packPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : WithTop ℕ∞} {f : E → ℝ} {g h : E → PDE.Vec n}
    (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) (hh : ContDiff ℝ m h) :
    ContDiff ℝ m (fun x => packPoint (f x) (g x) (h x)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [packPoint_zero_apply] using hf
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · simpa only [packPoint_diffused_apply] using contDiff_pi.1 hg a
    · simpa only [packPoint_transported_apply] using contDiff_pi.1 hh b

/-- The coefficient matrix, read in packed coordinates, is entrywise smooth. -/
theorem contDiff_coeffAt_entry {B : FullKineticCoefficient n}
    (hB : IsSmoothFullKineticCoefficient B) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EvolutionVec n =>
        B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x) i j) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionVec n =>
      (timeCoord n x, (diffusedCoord n x, transportedCoord n x))) :=
    (timeCoord n).contDiff.prodMk
      ((diffusedCoord n).contDiff.prodMk (transportedCoord n).contDiff)
  exact (hB i j).comp hlin

/-- The positive square root `β` of the coefficient is entrywise smooth in packed
coordinates, under the standing ellipticity hypotheses. -/
theorem contDiff_sqrtCoeffAt_entry {lam Lam : ℝ} {B : FullKineticCoefficient n}
    (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j) :=
  contDiff_sqrt_entry
    (fun x : EvolutionVec n => B (timeCoord n x) (diffusedCoord n x) (transportedCoord n x))
    (fun i j => contDiff_coeffAt_entry hB i j)
    (fun _ => posDef_of_smul_one_le hlam (hell _ _ _).1) i j

/-- The drift corrections `c_k` are smooth, as soon as `β` is entrywise smooth. -/
theorem contDiff_driftCorrection {B : FullKineticCoefficient n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j)) (k : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => driftCorrection B k x) := by
  unfold driftCorrection
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun y => sqrtCoeffAt B y i k)) :=
    (hβ i k).fderiv_right (by simp)
  exact (hβ i j).mul (h1.clm_apply contDiff_const)

theorem contDiff_diffusionField {B : FullKineticCoefficient n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j)) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (diffusionField B i) :=
  contDiff_packPoint contDiff_const (contDiff_pi.2 fun j => hβ i j) contDiff_const

theorem contDiff_driftField {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (driftField B b) :=
  contDiff_packPoint contDiff_const
    (contDiff_pi.2 fun k => (contDiff_driftCorrection hβ k).neg)
    (hb.comp (diffusedCoord n).contDiff)

theorem contDiff_regularizingField (ε : ℝ) (l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizingField ε l) :=
  contDiff_const

/-- The generators of `Lop` are smooth. -/
theorem contDiff_transportedFields {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (i : Fin (n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedFields B b i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [transportedFields] using contDiff_driftField hβ hb
  · simpa [transportedFields] using contDiff_diffusionField hβ j

/-- The generators of `L_ε` are smooth. -/
theorem contDiff_regularizedFields {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => sqrtCoeffAt B x i j))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (ε : ℝ) (i : Fin (n + n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedFields B b ε i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [regularizedFields] using contDiff_driftField hβ hb
  · refine Fin.addCases (fun a => ?_) (fun c => ?_) j
    · simpa only [regularizedFields, Fin.cons_succ, Fin.append_left] using
        contDiff_diffusionField hβ a
    · simpa only [regularizedFields, Fin.cons_succ, Fin.append_right] using
        contDiff_regularizingField ε c

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
