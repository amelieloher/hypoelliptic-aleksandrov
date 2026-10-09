module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares

/-!
# Divergence in packed coordinates

The Euclidean divergence `euclideanDivergence` of the Hörmander carriers (a sum over the
`1 + 2d` canonical basis vectors) is rewritten in the packed coordinates `(σ, v, z)` of
`BracketCoord`: for a field `V = packPoint s g h`,
`div V = ∂_σ s + ∑_j ∂_{v_j} g_j + ∑_l ∂_{z_l} h_l`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

theorem basisT_eq_basisVec : (basisT : EvolutionVec n) = PDE.basisVec 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [basisT, PDE.basisVec]
  · rw [basisT, PDE.basisVec_apply, ite_eq_right_of_eq_false _ _ (eq_false (Fin.succ_ne_zero _))]
    refine Fin.addCases (fun a => ?_) (fun c => ?_) j <;>
      simp only [packPoint_diffused_apply, packPoint_transported_apply] <;> rfl

theorem basisV_eq_basisVec (j : Fin n) :
    (basisV j : EvolutionVec n) = PDE.basisVec (Fin.succ (Fin.castAdd n j)) := by
  funext i
  rw [PDE.basisVec_apply]
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (Fin.succ_ne_zero _).symm)]
    simp [basisV]
  · refine Fin.addCases (fun a => ?_) (fun c => ?_) k
    · simp only [basisV, packPoint_diffused_apply, Pi.single_apply, Fin.succ_inj,
        Fin.castAdd_inj]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]
      · simp only [basisV, packPoint_transported_apply]; rfl
      · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_natAdd, Fin.val_castAdd]
        omega

theorem basisZ_eq_basisVec (l : Fin n) :
    (basisZ l : EvolutionVec n) = PDE.basisVec (Fin.succ (Fin.natAdd n l)) := by
  funext i
  rw [PDE.basisVec_apply]
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (Fin.succ_ne_zero _).symm)]
    simp [basisZ]
  · refine Fin.addCases (fun a => ?_) (fun c => ?_) k
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]
      · simp only [basisZ, packPoint_diffused_apply]; rfl
      · simp only [Fin.ext_iff, Fin.val_succ, Fin.val_natAdd, Fin.val_castAdd]
        omega
    · simp only [basisZ, packPoint_transported_apply, Pi.single_apply, Fin.succ_inj,
        Fin.natAdd_inj]

/-- The divergence of a differentiable field, split over the three coordinate blocks. -/
theorem euclideanDivergence_eq {V : EvolutionVec n → EvolutionVec n} {x : EvolutionVec n}
    (hV : DifferentiableAt ℝ V x) :
    euclideanDivergence V x =
      fderiv ℝ (fun y => V y 0) x basisT +
        ∑ j, fderiv ℝ (fun y => V y (Fin.succ (Fin.castAdd n j))) x (basisV j) +
        ∑ l, fderiv ℝ (fun y => V y (Fin.succ (Fin.natAdd n l))) x (basisZ l) := by
  have hcomp : ∀ i, DifferentiableAt ℝ (fun y => V y i) x := differentiableAt_pi.1 hV
  have key : ∀ (i : Fin (EvolutionDim n)) (w : EvolutionVec n),
      fderiv ℝ V x w i = fderiv ℝ (fun y => V y i) x w := by
    intro i w
    have := fderiv_pi (𝕜 := ℝ) (φ := fun i y => V y i) (x := x) hcomp
    have h2 : fderiv ℝ V x = fderiv ℝ (fun y i => V y i) x := rfl
    rw [h2, this]
    rfl
  unfold euclideanDivergence
  rw [Fin.sum_univ_succ, Fin.sum_univ_add]
  simp only [key, basisT_eq_basisVec, basisV_eq_basisVec, basisZ_eq_basisVec]
  ring

/-- The divergence of a field in the packed form `packPoint s g h`. -/
theorem euclideanDivergence_packPoint {s : EvolutionVec n → ℝ} {g h : EvolutionVec n → PDE.Vec n}
    {x : EvolutionVec n} (hs : DifferentiableAt ℝ s x)
    (hg : ∀ j, DifferentiableAt ℝ (fun y => g y j) x)
    (hh : ∀ l, DifferentiableAt ℝ (fun y => h y l) x) :
    euclideanDivergence (fun y => packPoint (s y) (g y) (h y)) x =
      fderiv ℝ s x basisT + ∑ j, fderiv ℝ (fun y => g y j) x (basisV j) +
        ∑ l, fderiv ℝ (fun y => h y l) x (basisZ l) := by
  have hV : DifferentiableAt ℝ (fun y => packPoint (s y) (g y) (h y)) x := by
    refine differentiableAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [packPoint_zero_apply] using hs
    · refine Fin.addCases (fun a => ?_) (fun c => ?_) j
      · simpa only [packPoint_diffused_apply] using hg a
      · simpa only [packPoint_transported_apply] using hh c
  rw [euclideanDivergence_eq hV]
  simp only [packPoint_zero_apply, packPoint_diffused_apply, packPoint_transported_apply]

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
