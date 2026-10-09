module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedTransferOperator
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Classical solutions: straightened variables versus absolute variables

Chain-rule transfer.  A classical solution
`ũ` of the straightened problem, with drift `-g'(σ) · ∇_Y`, pulls back along
`Y = y - g(σ)` to a classical solution `u(σ, y, z) = ũ(σ, (y - g(σ), z))` of the absolute
problem in the sense of the comparison theorems and of `IsClassicalViscousTerminalSolution`.

* `isClassicalViscousTerminalSolution_straightenedPullback`: the straightened problem on the
  whole past cylinder `{σ ≤ τ, Y ∈ closure Ω}` (all `z`) gives `IsClassicalViscousTerminalSolution`
  for the moving domain `g + Ω`; at `ε = 0` this is `IsClassicalTerminalSolution`.
* `straightenedPullback_of_dirichlet`: the finite-slab Dirichlet problem on an arbitrary open
  spatial base `D` of `(Y, z)` (for instance the truncation ellipsoid) gives, in absolute
  variables, continuity, slice regularity, joint smoothness, `L_ε u = 0` and the terminal and
  lateral values on the corresponding absolute cylinder, which are the hypotheses of
  `bounded_comparison` and `two_barriers`.

Interior smoothness of `ũ` is a hypothesis of the transfer; it is what the weak formulation and
the Hörmander theorem supply for the Dirichlet solution, and it is exactly the regularity
demanded by the classical-solution predicates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov

variable {n : ℕ}

/-- Membership of a point in the frontier of the moving domain. -/
theorem mem_frontier_movingDomain_iff {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {σ : ℝ}
    {y : PDE.Vec n} : y ∈ frontier (movingDomain Ω γ σ) ↔ y - γ σ ∈ frontier Ω := by
  have h : movingDomain Ω γ σ = (Homeomorph.subRight (γ σ)) ⁻¹' Ω := by
    rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
    rfl
  rw [h, ← Homeomorph.preimage_frontier]
  rfl

/-- Smoothness of `ũ` at a point gives joint differentiability and `C²` regularity of the
spatial slice there. -/
theorem straightened_regular_of_contDiffAt {ũ : TimeVelocity (n + n) → ℝ}
    {z : TimeVelocity (n + n)} (h : ContDiffAt ℝ (⊤ : ℕ∞) ũ z) :
    DifferentiableAt ℝ ũ z ∧ ContDiffAt ℝ 2 (fun X => ũ (z.1, X)) z.2 := by
  have h2 : ContDiffAt ℝ 2 ũ z := h.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  refine ⟨h2.differentiableAt (by norm_num), ?_⟩
  exact ContDiffAt.comp (g := ũ) (f := fun X : PDE.Vec (n + n) => (z.1, X)) z.2 h2
    (contDiffAt_const.prodMk contDiffAt_id)

/-- The map `(σ, (y, z)) ↦ (σ, (y - g(σ), z))` is smooth for smooth `g`. -/
theorem contDiff_straightenedRaw {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec n × PDE.Vec n) =>
      (q.1, spatialPack (q.2.1 - g q.1) q.2.2)) :=
  contDiff_fst.prodMk (contDiff_spatialPack
    ((contDiff_fst.comp contDiff_snd).sub (hg.comp contDiff_fst))
    (contDiff_snd.comp contDiff_snd))

/-- The terminal datum composed with the straightening is the original datum. -/
theorem terminalDatum_straightened (c y z : PDE.Vec n) {α : Type*}
    (F : PDE.Vec n × PDE.Vec n → α) :
    F (c + spatialY (spatialPack (y - c) z), spatialZ (spatialPack (y - c) z)) = F (y, z) := by
  simp

section Dirichlet

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε : ℝ}
  {g : ℝ → PDE.Vec n} {ũ : TimeVelocity (n + n) → ℝ} {D : Set (PDE.Vec (n + n))}

/-- **Chain-rule transfer for the finite-slab Dirichlet problem.**  Let `D` be an open spatial
base in the `(Y, z)` variables and let `ũ` solve the backward Dirichlet problem
`∂σ ũ + diag(B, ε I) : D² ũ + (-g', b(g + Y)) · ∇ ũ = 0` on `(a, τ) × D` with zero lateral data
and terminal datum `x ↦ F (g(τ) + Y, z)`, and let `ũ` be smooth in the interior.  Then the
pullback `u(σ, y, z) = ũ(σ, (y - g(σ), z))` is, on the absolute cylinder
`{a < σ < τ, (y - g(σ), z) ∈ D}`, slice regular, jointly smooth and a solution of `L_ε u = 0`,
continuous up to the closed absolute cylinder, equal to `F` on the terminal face and `0` on the
lateral face. -/
theorem straightenedPullback_of_dirichlet (hD : IsOpen D) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {a τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hu : IsClassicalBackwardDirichletSolution a τ D
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0) (fun x => F (g τ + spatialY x, spatialZ x))
      (fun _ => 0) ũ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) ũ (scalarParabolicOpenCylinder a τ D)) :
    ContinuousOn (straightenedPullback g ũ)
        (straightenedPoint g ⁻¹' scalarParabolicClosedCylinder a τ D) ∧
      (∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicOpenCylinder a τ D,
        IsSliceRegularAt (straightenedPullback g ũ) p ∧
          viscousTransportedOperator B b ε (straightenedPullback g ũ) p = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => straightenedPullback g ũ ⟨q.1, q.2.1, q.2.2⟩)
        {q | (q.1, spatialPack (q.2.1 - g q.1) q.2.2) ∈ scalarParabolicOpenCylinder a τ D} ∧
      (∀ p : KineticPoint n, p.time = τ → spatialPack (p.position - g τ) p.velocity ∈ closure D →
        straightenedPullback g ũ p = F (p.position, p.velocity)) ∧
      (∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicLateralFace a τ D,
        straightenedPullback g ũ p = 0) := by
  have hopen : IsOpen (scalarParabolicOpenCylinder a τ D) := isOpen_Ioo.prod hD
  have hgc : Continuous g := hg.continuous
  refine ⟨hu.1.comp (continuous_straightenedPoint hgc).continuousOn (fun p hp => hp), ?_, ?_,
    ?_, ?_⟩
  · intro p hp
    obtain ⟨hdiff, hslice⟩ := straightened_regular_of_contDiffAt
      (hsm.contDiffAt (hopen.mem_nhds hp))
    have hgd : DifferentiableAt ℝ g p.time := (hg.differentiable (by simp)) p.time
    refine ⟨isSliceRegularAt_straightenedPullback hgd hdiff hslice, ?_⟩
    rw [viscousTransportedOperator_straightenedPullback hgd hdiff hslice]
    have h := hu.2.2.1 (straightenedPoint g p) hp
    simpa using h
  · exact hsm.comp (contDiff_straightenedRaw hg).contDiffOn (fun q hq => hq)
  · intro p hpτ hpD
    have h := hu.2.2.2.1 (spatialPack (p.position - g τ) p.velocity) hpD
    have hp : straightenedPullback g ũ p = ũ (τ, spatialPack (p.position - g τ) p.velocity) := by
      rw [straightenedPullback_apply, straightenedPoint, hpτ]
    rw [hp, h]
    exact terminalDatum_straightened (g τ) p.position p.velocity (fun q => F q)
  · intro p hp
    exact hu.2.2.2.2 (straightenedPoint g p) hp

end Dirichlet

section Past

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε : ℝ}
  {g : ℝ → PDE.Vec n} {ũ : TimeVelocity (n + n) → ℝ}

/-- **Chain-rule transfer to `IsClassicalViscousTerminalSolution`.**  Let `ũ` be a classical
solution of the straightened problem on the whole past cylinder `{σ ≤ τ, Y ∈ closure Ω}` (all
transported coordinates `z`): bounded, continuous, smooth in the interior, solving
`∂σ ũ + diag(B, ε I) : D² ũ + (-g', b(g + Y)) · ∇ ũ = 0`, equal to the terminal datum
`F (g(τ) + Y, z)` at `σ = τ` and to `0` on the lateral frontier `Y ∈ frontier Ω`.  Then
`u(σ, y, z) = ũ(σ, (y - g(σ), z))` is an `IsClassicalViscousTerminalSolution` for the moving
domain `g + Ω`. -/
theorem isClassicalViscousTerminalSolution_straightenedPullback {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) (hg : ContDiff ℝ (⊤ : ℕ∞) g) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : TimeVelocity (n + n), z.1 ≤ τ → spatialY z.2 ∈ closure Ω →
      |ũ z| ≤ C)
    (hcont : ContinuousOn ũ {z | z.1 ≤ τ ∧ spatialY z.2 ∈ closure Ω})
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) ũ {z | z.1 < τ ∧ spatialY z.2 ∈ Ω})
    (heq : ∀ z : TimeVelocity (n + n), z.1 < τ → spatialY z.2 ∈ Ω →
      scalarParabolicOperator (straightenedCoefficient B g ε) (straightenedDrift b g) ũ z = 0)
    (hterm : ∀ X : PDE.Vec (n + n), spatialY X ∈ closure Ω →
      ũ (τ, X) = F (g τ + spatialY X, spatialZ X))
    (hlat : ∀ z : TimeVelocity (n + n), z.1 ≤ τ → spatialY z.2 ∈ frontier Ω → ũ z = 0) :
    IsClassicalViscousTerminalSolution Ω g B b ε τ F (straightenedPullback g ũ) := by
  have hgc : Continuous g := hg.continuous
  have hopen : IsOpen {z : TimeVelocity (n + n) | z.1 < τ ∧ spatialY z.2 ∈ Ω} :=
    (isOpen_lt continuous_fst continuous_const).inter
      (hΩ.preimage ((contDiff_spatialY (m := 0)).continuous.comp continuous_snd))
  have hY : ∀ p : KineticPoint n, spatialY (straightenedPoint g p).2 = p.position - g p.time :=
    fun p => by simp [straightenedPoint]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hbd
    refine ⟨C, hC0, fun p hp => ?_⟩
    refine hC (straightenedPoint g p) hp.1 ?_
    rw [hY]
    exact mem_closure_movingDomain_iff.1 hp.2
  · refine hcont.comp (continuous_straightenedPoint hgc).continuousOn (fun p hp => ?_)
    refine ⟨hp.1, ?_⟩
    change spatialY (straightenedPoint g p).2 ∈ closure Ω
    rw [hY]
    exact mem_closure_movingDomain_iff.1 hp.2
  · refine hsm.comp (contDiff_straightenedRaw hg).contDiffOn (fun q hq => ?_)
    refine ⟨hq.1, ?_⟩
    simpa using mem_movingDomain_iff.1 hq.2
  · intro p hp
    have hp' : straightenedPoint g p ∈ {z : TimeVelocity (n + n) | z.1 < τ ∧ spatialY z.2 ∈ Ω} :=
      ⟨hp.1, by rw [hY]; exact mem_movingDomain_iff.1 hp.2⟩
    obtain ⟨hdiff, hslice⟩ := straightened_regular_of_contDiffAt
      (hsm.contDiffAt (hopen.mem_nhds hp'))
    have hgd : DifferentiableAt ℝ g p.time := (hg.differentiable (by simp)) p.time
    rw [viscousTransportedOperator_straightenedPullback hgd hdiff hslice]
    exact heq _ hp'.1 hp'.2
  · intro p hp
    obtain ⟨hpτ, hpc⟩ := hp
    have hcl : spatialY (spatialPack (p.position - g τ) p.velocity) ∈ closure Ω := by
      simpa [hpτ] using mem_closure_movingDomain_iff.1 hpc
    have h := hterm _ hcl
    have hp2 : straightenedPullback g ũ p = ũ (τ, spatialPack (p.position - g τ) p.velocity) := by
      rw [straightenedPullback_apply, straightenedPoint, hpτ]
    rw [hp2, h]
    exact terminalDatum_straightened (g τ) p.position p.velocity (fun q => F q)
  · intro p hp
    refine hlat (straightenedPoint g p) hp.1 ?_
    rw [hY]
    exact mem_frontier_movingDomain_iff.1 hp.2

/-- At `ε = 0` the transfer gives `IsClassicalTerminalSolution` for the transported operator. -/
theorem isClassicalTerminalSolution_straightenedPullback {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) (hg : ContDiff ℝ (⊤ : ℕ∞) g) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : TimeVelocity (n + n), z.1 ≤ τ → spatialY z.2 ∈ closure Ω →
      |ũ z| ≤ C)
    (hcont : ContinuousOn ũ {z | z.1 ≤ τ ∧ spatialY z.2 ∈ closure Ω})
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) ũ {z | z.1 < τ ∧ spatialY z.2 ∈ Ω})
    (heq : ∀ z : TimeVelocity (n + n), z.1 < τ → spatialY z.2 ∈ Ω →
      scalarParabolicOperator (straightenedCoefficient B g 0) (straightenedDrift b g) ũ z = 0)
    (hterm : ∀ X : PDE.Vec (n + n), spatialY X ∈ closure Ω →
      ũ (τ, X) = F (g τ + spatialY X, spatialZ X))
    (hlat : ∀ z : TimeVelocity (n + n), z.1 ≤ τ → spatialY z.2 ∈ frontier Ω → ũ z = 0) :
    IsClassicalTerminalSolution Ω g B b τ F (straightenedPullback g ũ) :=
  (isClassicalViscousTerminalSolution_zero_iff Ω g B b τ F _).1
    (isClassicalViscousTerminalSolution_straightenedPullback hΩ hg hbd hcont hsm heq hterm hlat)

end Past

/-- A smooth curve is continuous and piecewise `C¹` (with a single piece). -/
theorem isContinuousPiecewiseC1_of_contDiff {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : IsContinuousPiecewiseC1 g := by
  refine ⟨hg.continuous, fun a b hab => ⟨0, ![a, b], ?_, rfl, rfl, fun i => ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact (hg.contDiffOn (s := Set.Icc _ _)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))

end HypoellipticAleksandrov.KineticAleksandrov
