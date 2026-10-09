module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Whole-past classical recovery for the actual expanding-ball limit -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- Translating the whole diffused space leaves the actual moving domain equal to univ. -/
theorem movingDomain_univ_eq {n : ℕ} (Γ : ℝ → PDE.Vec n) (t : ℝ) :
    movingDomain univ Γ t = univ := by
  ext y
  rw [mem_movingDomain_iff]
  simp only [mem_univ]

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- The actual expanding-ball limit is a bounded classical whole-space solution,
including its exact terminal values, relative to the explicit Hörmander input. -/
theorem isClassicalViscousTerminalSolution_wholeSpace_ball_limit
    (hH : HormanderHypoellipticityStatement) :
    IsClassicalViscousTerminalSolution univ (fun _ => 0) B b ε τ F
      (fun p => limUnder atTop (fun j => v j p)) ∧
    ∀ p ∈ evolutionPastClosedCylinder univ (fun _ => 0) τ,
      |limUnder atTop (fun j => v j p)| ≤ C := by
  let f (p : KineticPoint n) := limUnder atTop (fun j => v j p)
  have hUnif (α S : ℝ) := tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S)
    hlam hB hb hε.le hε1 hC F hFC r hrlim v hv
  have hLocal (α S : ℝ) := classical_wholeSpace_ball_limit (α := α) (S0 := S)
    hlam hB hb hε hε1 hC F hFC r hrlim v hv hBs hBsym hbs hH
  have hcl (p : KineticPoint n) (hp : p.time ≤ τ) :
      p ∈ movingClosedSlab univ (fun _ => 0) (p.time - 1) τ := by
    refine ⟨by linarith, hp, ?_⟩
    rw [movingDomain_univ_eq, closure_univ]
    trivial
  have hbnd : ∀ p ∈ evolutionPastClosedCylinder univ (fun _ => 0) τ, |f p| ≤ C := by
    intro p hp
    obtain ⟨S, -, hrad, -⟩ := exists_wholeSpace_closedCylinder_mem_nhdsWithin (hcl p hp.1)
    exact (hUnif (p.time - 1) S).2.2 p ⟨hcl p hp.1, hrad.le⟩
  refine ⟨⟨⟨C, hC, hbnd⟩, ?_, ?_, ?_, ?_, ?_⟩, hbnd⟩
  · intro p hp
    let α := p.time - 1
    obtain ⟨S, -, hrad, hKmem⟩ := exists_wholeSpace_closedCylinder_mem_nhdsWithin (hcl p hp.1)
    have hc := (hUnif α S).2.1 p ⟨hcl p hp.1, hrad.le⟩
    have hslab : movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∈
        𝓝[evolutionPastClosedCylinder univ (fun _ => 0) τ] p := by
      filter_upwards [self_mem_nhdsWithin,
        (continuous_time.continuousAt.eventually (lt_mem_nhds (by
          dsimp [α]; linarith : α < p.time))).filter_mono nhdsWithin_le_nhds]
        with q hq ht
      exact ⟨ht.le, hq.1, hq.2⟩
    have hKe : ∀ᶠ q in 𝓝[movingClosedSlab univ
        (fun _ : ℝ => (0 : PDE.Vec n)) α τ] p,
        q ∈ movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
          {p | radialSq p ≤ S ^ 2} := hKmem
    exact hc.mono_of_mem_nhdsWithin (hKe.filter_mono (nhdsWithin_le_of_mem hslab))
  · intro q hq
    let p : KineticPoint n := ⟨q.1, q.2.1, q.2.2⟩
    let α := p.time - 1
    let S := radialSq p + 1
    have hrad0 : 0 ≤ radialSq p :=
      add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
    have hpU : p ∈ wholeSpaceInnerCylinder α τ S :=
      ⟨by dsimp [α]; linarith, hq.1, by dsimp [S]; nlinarith⟩
    let x := (evolutionProdCLE n).symm q
    have hxp : evolutionHomeomorph n x = p := by
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    have hx : x ∈ evolutionHomeomorph n ⁻¹' wholeSpaceInnerCylinder α τ S := by
      change evolutionHomeomorph n x ∈ wholeSpaceInnerCylinder α τ S
      rw [hxp]
      exact hpU
    have hV := (isOpen_wholeSpaceInnerCylinder (n := n) α τ S).preimage
      (evolutionHomeomorph n).continuous
    have hc := ((hLocal α S).1.contDiffAt (hV.mem_nhds hx)).comp q
      (evolutionProdCLE n).symm.contDiff.contDiffAt
    have hfun : (f ∘ evolutionHomeomorph n) ∘ (evolutionProdCLE n).symm =
        fun q => f ⟨q.1, q.2.1, q.2.2⟩ := by
      funext q
      change f (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) = f ⟨q.1, q.2.1, q.2.2⟩
      apply congrArg f
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    change ContDiffAt ℝ (⊤ : ℕ∞) ((f ∘ evolutionHomeomorph n) ∘
      (evolutionProdCLE n).symm) q at hc
    rw [hfun] at hc
    exact hc.contDiffWithinAt
  · intro p hp
    let S := radialSq p + 1
    have hrad0 : 0 ≤ radialSq p :=
      add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
    exact (hLocal (p.time - 1) S).2 p
      ⟨by linarith, hp.1, by dsimp [S]; nlinarith⟩
  · intro p hp
    let α := τ - 1
    obtain ⟨S, -, hrad, -⟩ := exists_wholeSpace_closedCylinder_mem_nhdsWithin
      (hcl p hp.1.le)
    have hpK : p ∈ movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
        {p | radialSq p ≤ S ^ 2} := by
      refine ⟨⟨by dsimp [α]; rw [hp.1]; linarith, hp.1.le, ?_⟩, hrad.le⟩
      rw [movingDomain_univ_eq, closure_univ]
      trivial
    have he : ∀ᶠ j : ℕ in atTop, v j p = F (p.position, p.velocity) := by
      filter_upwards [hrlim.eventually (eventually_gt_atTop |S|)] with j hj
      have hi := mem_movingBall_of_radialSq_le (abs_nonneg S) hj
        (by simpa only [sq_abs] using hrad.le)
      exact (hv j).2.2.2.2.1 p
        ⟨hp.1, by simpa only [hp.1] using subset_closure hi⟩
    exact tendsto_nhds_unique ((hUnif α S).1.tendsto_at hpK)
      (tendsto_const_nhds.congr' (he.mono fun j hj => hj.symm))
  · intro p hp
    have hfr := hp.2
    rw [movingDomain_univ_eq, frontier_univ] at hfr
    exact hfr.elim

end Data

end HypoellipticAleksandrov.KineticAleksandrov
