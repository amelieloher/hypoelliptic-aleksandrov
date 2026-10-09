module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord

/-!
# The packed operators and the project's `transportedForwardOperator`

For `u : KineticPoint n → ℝ` write `U = u ∘ evolutionHomeomorph n` for its packed pullback
`(σ, v, z) ↦ u ⟨σ, v, z⟩`.  If `U` is `C²` at `x`, then
`transportedOperator B b U x = transportedForwardOperator B b u (e x)` and
`regularizedOperator B b ε U x = transportedForwardOperator B b u (e x)
  + ε ∑_l kineticVelocityHessian u (e x) l l`.
The proof rewrites each of the `kinetic…` derivative surfaces (time derivative, position and
velocity gradients, the position and velocity Hessians) along an affine slice of the packed space.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-! ### Slices of the packed space -/

variable (n) in
/-- The time step `s ↦ s ∂_σ`. -/
def stepT : ℝ →L[ℝ] EvolutionVec n := (ContinuousLinearMap.id ℝ ℝ).smulRight basisT

variable (n) in
/-- The embedding `w ↦ (0, w, 0)` of the diffused block. -/
def embedDiffused : PDE.Vec n →L[ℝ] EvolutionVec n :=
  ((evolutionProdCLE n).symm : ℝ × (PDE.Vec n × PDE.Vec n) →L[ℝ] EvolutionVec n).comp
    ((ContinuousLinearMap.inr ℝ ℝ (PDE.Vec n × PDE.Vec n)).comp
      (ContinuousLinearMap.inl ℝ (PDE.Vec n) (PDE.Vec n)))

variable (n) in
/-- The embedding `w ↦ (0, 0, w)` of the transported block. -/
def embedTransported : PDE.Vec n →L[ℝ] EvolutionVec n :=
  ((evolutionProdCLE n).symm : ℝ × (PDE.Vec n × PDE.Vec n) →L[ℝ] EvolutionVec n).comp
    ((ContinuousLinearMap.inr ℝ ℝ (PDE.Vec n × PDE.Vec n)).comp
      (ContinuousLinearMap.inr ℝ (PDE.Vec n) (PDE.Vec n)))

@[simp] theorem stepT_apply (s : ℝ) : stepT n s = packPoint s 0 0 := by
  refine ext_coords ?_ ?_ ?_
  · simp [stepT, basisT]
  · simp only [stepT, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul,
      basisT, diffusedCoord_packPoint, diffusedCoord_packPoint]
    simp
  · simp only [stepT, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul,
      basisT, transportedCoord_packPoint]
    simp

@[simp] theorem embedDiffused_apply (w : PDE.Vec n) : embedDiffused n w = packPoint 0 w 0 := rfl

@[simp] theorem embedTransported_apply (w : PDE.Vec n) :
    embedTransported n w = packPoint 0 0 w := rfl

theorem add_stepT (x : EvolutionVec n) (s : ℝ) :
    x + stepT n s = packPoint (timeCoord n x + s) (diffusedCoord n x) (transportedCoord n x) := by
  rw [stepT_apply]
  refine ext_coords ?_ ?_ ?_ <;> simp

theorem add_embedDiffused (x : EvolutionVec n) (w : PDE.Vec n) :
    x + embedDiffused n w =
      packPoint (timeCoord n x) (diffusedCoord n x + w) (transportedCoord n x) := by
  rw [embedDiffused_apply]
  refine ext_coords ?_ ?_ ?_ <;> simp

theorem add_embedTransported (x : EvolutionVec n) (w : PDE.Vec n) :
    x + embedTransported n w =
      packPoint (timeCoord n x) (diffusedCoord n x) (transportedCoord n x + w) := by
  rw [embedTransported_apply]
  refine ext_coords ?_ ?_ ?_ <;> simp

/-- Derivative of a function along an affine slice `y ↦ a + ι (y - p)`. -/
theorem fderiv_comp_affine {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : F →L[ℝ] E) (a : E) (p : F) {V : E → ℝ}
    (hV : DifferentiableAt ℝ V a) :
    fderiv ℝ (fun y => V (a + ι (y - p))) p = (fderiv ℝ V a).comp ι := by
  have h : HasFDerivAt (fun y => a + ι (y - p)) ι p := by
    have := (ι.hasFDerivAt).comp p ((hasFDerivAt_id p).sub_const p)
    simpa using this.const_add a
  have hV' : HasFDerivAt V (fderiv ℝ V a) (a + ι (p - p)) := by simpa using hV.hasFDerivAt
  exact (hV'.comp p h).fderiv

/-- Smoothness along an affine slice. -/
theorem contDiffAt_comp_affine {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : F →L[ℝ] E) (a : E) (p : F) {V : E → ℝ}
    (hV : ContDiffAt ℝ 2 V a) : ContDiffAt ℝ 2 (fun y => V (a + ι (y - p))) p := by
  have haff : ContDiff ℝ 2 (fun y : F => a + ι (y - p)) := by fun_prop
  have hV' : ContDiffAt ℝ 2 V ((fun y : F => a + ι (y - p)) p) := by simpa using hV
  exact hV'.comp p haff.contDiffAt

/-- Second derivative along an affine slice. -/
theorem fderiv_fderiv_comp_affine {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : F →L[ℝ] E) (a : E) (p : F) {V : E → ℝ}
    (hV : ContDiffAt ℝ 2 V a) (v w : F) :
    fderiv ℝ (fun y => fderiv ℝ (fun x' => V (a + ι (x' - p))) y w) p v =
      fderiv ℝ (fun z => fderiv ℝ V z (ι w)) a (ι v) := by
  have hev : ∀ᶠ z in nhds a, ContDiffAt ℝ 2 V z := hV.eventually (by simp)
  have haff : Filter.Tendsto (fun y : F => a + ι (y - p)) (nhds p) (nhds a) := by
    have hc : ContinuousAt (fun y : F => a + ι (y - p)) p := by fun_prop
    have := hc.tendsto
    rwa [show a + ι (p - p) = a by simp] at this
  have hev' : ∀ᶠ y in nhds p, ContDiffAt ℝ 2 V (a + ι (y - p)) := haff.eventually hev
  have hslice : ∀ y, (fun x' => V (a + ι (x' - p))) =
      fun x' => V ((a + ι (y - p)) + ι (x' - y)) := by
    intro y
    funext x'
    congr 1
    rw [add_assoc, ← map_add]
    congr 2
    abel
  have heq : (fun y => fderiv ℝ (fun x' => V (a + ι (x' - p))) y w) =ᶠ[nhds p]
      fun y => fderiv ℝ V (a + ι (y - p)) (ι w) := by
    filter_upwards [hev'] with y hy
    rw [hslice y, fderiv_comp_affine ι (a + ι (y - p)) y
      (hy.differentiableAt (by norm_num))]
    rfl
  rw [heq.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun z => fderiv ℝ V z (ι w)) a :=
    ((hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have := fderiv_comp_affine ι a p hg
  rw [show (fun y => fderiv ℝ V (a + ι (y - p)) (ι w)) =
      fun y => (fun z => fderiv ℝ V z (ι w)) (a + ι (y - p)) from rfl, this]
  rfl

/-! ### The `kinetic…` derivative surfaces along the bridge -/

section Surfaces

variable {u : KineticPoint n → ℝ} {x : EvolutionVec n}

theorem slice_time (x : EvolutionVec n) (r : ℝ) :
    u ⟨r, diffusedCoord n x, transportedCoord n x⟩ =
      (u ∘ evolutionHomeomorph n) (x + stepT n (r - timeCoord n x)) := by
  rw [add_stepT, Function.comp_apply, evolutionHomeomorph_apply]
  simp

theorem slice_position (x : EvolutionVec n) (y : PDE.Vec n) :
    u ⟨timeCoord n x, y, transportedCoord n x⟩ =
      (u ∘ evolutionHomeomorph n) (x + embedDiffused n (y - diffusedCoord n x)) := by
  rw [add_embedDiffused, Function.comp_apply, evolutionHomeomorph_apply]
  simp

theorem slice_velocity (x : EvolutionVec n) (y : PDE.Vec n) :
    u ⟨timeCoord n x, diffusedCoord n x, y⟩ =
      (u ∘ evolutionHomeomorph n) (x + embedTransported n (y - transportedCoord n x)) := by
  rw [add_embedTransported, Function.comp_apply, evolutionHomeomorph_apply]
  simp

/-- The kinetic time derivative is `∂_σ` of the packed pullback. -/
theorem kineticTimeDerivative_comp (hU : DifferentiableAt ℝ (u ∘ evolutionHomeomorph n) x) :
    kineticTimeDerivative u (evolutionHomeomorph n x) =
      fderiv ℝ (u ∘ evolutionHomeomorph n) x basisT := by
  unfold kineticTimeDerivative
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph]
  rw [show (fun r => u ⟨r, diffusedCoord n x, transportedCoord n x⟩) =
      fun r => (u ∘ evolutionHomeomorph n) (x + stepT n (r - timeCoord n x)) from
        funext fun r => slice_time x r, ← fderiv_apply_one_eq_deriv,
    fderiv_comp_affine (stepT n) x (timeCoord n x) hU]
  simp [stepT_apply, basisT]

/-- The kinetic position gradient is the `∂_{v_j}` gradient of the packed pullback. -/
theorem kineticPositionGradient_comp (hU : DifferentiableAt ℝ (u ∘ evolutionHomeomorph n) x)
    (j : Fin n) :
    kineticPositionGradient u (evolutionHomeomorph n x) j =
      fderiv ℝ (u ∘ evolutionHomeomorph n) x (basisV j) := by
  unfold kineticPositionGradient
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph, PDE.classicalGradient_apply]
  rw [show (fun y => u ⟨timeCoord n x, y, transportedCoord n x⟩) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedDiffused n (y - diffusedCoord n x)) from
        funext fun y => slice_position x y, fderiv_comp_affine (embedDiffused n) x _ hU]
  simp [basisV, PDE.basisVec]

/-- The kinetic velocity gradient is the `∂_{z_l}` gradient of the packed pullback. -/
theorem kineticVelocityGradient_comp (hU : DifferentiableAt ℝ (u ∘ evolutionHomeomorph n) x)
    (l : Fin n) :
    kineticVelocityGradient u (evolutionHomeomorph n x) l =
      fderiv ℝ (u ∘ evolutionHomeomorph n) x (basisZ l) := by
  unfold kineticVelocityGradient
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph, PDE.classicalGradient_apply]
  rw [show (fun y => u ⟨timeCoord n x, diffusedCoord n x, y⟩) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedTransported n (y - transportedCoord n x))
        from funext fun y => slice_velocity x y, fderiv_comp_affine (embedTransported n) x _ hU]
  simp [basisZ, PDE.basisVec]

/-- Entries of a gradient-valued function along a slice are derivatives of its entries. -/
theorem fderiv_classicalGradient_apply {f : PDE.Vec n → ℝ} {p : PDE.Vec n}
    (hf : ContDiffAt ℝ 2 f p) (v : PDE.Vec n) (j : Fin n) :
    fderiv ℝ (fun y => PDE.classicalGradient f y) p v j =
      fderiv ℝ (fun y => fderiv ℝ f y (PDE.basisVec j)) p v := by
  have hd : ∀ j', DifferentiableAt ℝ (fun y => fderiv ℝ f y (PDE.basisVec j')) p := fun j' =>
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have := fderiv_pi (𝕜 := ℝ) (φ := fun j' y => fderiv ℝ f y (PDE.basisVec j')) (x := p) hd
  have h2 : (fun y => PDE.classicalGradient f y) = fun y j' => fderiv ℝ f y (PDE.basisVec j') :=
    rfl
  rw [h2, this]
  rfl

/-- The position Hessian of the kinetic pullback is the `∂_{v_i} ∂_{v_j}` Hessian. -/
theorem diffusedHessian_comp (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x) (i j : Fin n) :
    diffusedHessian u (evolutionHomeomorph n x) i j =
      fderiv ℝ (fun y => fderiv ℝ (u ∘ evolutionHomeomorph n) y (basisV j)) x (basisV i) := by
  have hS : (fun y => u ⟨timeCoord n x, y, transportedCoord n x⟩) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedDiffused n (y - diffusedCoord n x)) :=
    funext fun y => slice_position x y
  have hSc : ContDiffAt ℝ 2 (fun y => u ⟨timeCoord n x, y, transportedCoord n x⟩)
      (diffusedCoord n x) := by
    rw [hS]
    exact contDiffAt_comp_affine (embedDiffused n) x (diffusedCoord n x) hU
  rw [diffusedHessian_apply]
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph, kineticPositionGradient]
  rw [fderiv_classicalGradient_apply hSc]
  rw [hS]
  have := fderiv_fderiv_comp_affine (embedDiffused n) x (diffusedCoord n x) hU
    (PDE.basisVec i) (PDE.basisVec j)
  exact this

/-- The velocity Hessian of the kinetic pullback is the `∂_{z_i} ∂_{z_j}` Hessian. -/
theorem kineticVelocityHessian_comp (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x)
    (i j : Fin n) :
    kineticVelocityHessian u (evolutionHomeomorph n x) i j =
      fderiv ℝ (fun y => fderiv ℝ (u ∘ evolutionHomeomorph n) y (basisZ j)) x (basisZ i) := by
  have hS : (fun y => u ⟨timeCoord n x, diffusedCoord n x, y⟩) =
      fun y => (u ∘ evolutionHomeomorph n) (x + embedTransported n (y - transportedCoord n x)) :=
    funext fun y => slice_velocity x y
  have hSc : ContDiffAt ℝ 2 (fun y => u ⟨timeCoord n x, diffusedCoord n x, y⟩)
      (transportedCoord n x) := by
    rw [hS]
    exact contDiffAt_comp_affine (embedTransported n) x (transportedCoord n x) hU
  unfold kineticVelocityHessian
  simp only [time_evolutionHomeomorph, position_evolutionHomeomorph,
    velocity_evolutionHomeomorph]
  rw [fderiv_classicalGradient_apply hSc, hS]
  exact fderiv_fderiv_comp_affine (embedTransported n) x (transportedCoord n x) hU
    (PDE.basisVec i) (PDE.basisVec j)

end Surfaces

/-! ### The operators -/

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- **Coordinate bridge for `Lop`.**  For `u : KineticPoint n → ℝ` whose packed pullback
`u ∘ evolutionHomeomorph n` is `C²` at `x`, the packed operator `transportedOperator` of the
Hörmander bracket files agrees with the project's `transportedForwardOperator` at the kinetic
point `⟨σ, v, z⟩` of `x`. -/
theorem transportedOperator_comp {u : KineticPoint n → ℝ} {x : EvolutionVec n}
    (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x) :
    transportedOperator B b (u ∘ evolutionHomeomorph n) x =
      transportedForwardOperator B b u (evolutionHomeomorph n x) := by
  have hd : DifferentiableAt ℝ (u ∘ evolutionHomeomorph n) x :=
    hU.differentiableAt (by norm_num)
  rw [transportedForwardOperator_apply, kineticTimeDerivative_comp hd, transportedOperator]
  congr 1
  congr 1
  · unfold matrixContraction
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [diffusedHessian_comp hU i j]
    rfl
  · unfold PDE.vecDot
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [kineticVelocityGradient_comp hd l]
    rfl

/-- **Coordinate bridge for `L_ε = Lop + ε Δ_z`.** -/
theorem regularizedOperator_comp {u : KineticPoint n → ℝ} {x : EvolutionVec n} (ε : ℝ)
    (hU : ContDiffAt ℝ 2 (u ∘ evolutionHomeomorph n) x) :
    regularizedOperator B b ε (u ∘ evolutionHomeomorph n) x =
      transportedForwardOperator B b u (evolutionHomeomorph n x) +
        ε * ∑ l, kineticVelocityHessian u (evolutionHomeomorph n x) l l := by
  rw [regularizedOperator, transportedOperator_comp hU]
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [kineticVelocityHessian_comp hU l l]

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
