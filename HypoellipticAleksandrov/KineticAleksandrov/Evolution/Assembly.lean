module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.AssemblyAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalExistence
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionKernel
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorel

/-! # The terminal evolution, relative to Hörmander and Lieberman

Classical existence, the Riesz measures, integral operators, covariance, domain domination
and the complete marginal theorem are consumed directly. Composition and joint
measurability discharge the earlier integration skeleton below. The final export
has only the Lieberman and Hörmander inputs as explicit premises.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open scoped ProbabilityTheory

/-- Integration skeleton for the terminal evolution; the composition identity and the joint
measurability of the master kernel remain explicit premises. -/
theorem exists_terminalEvolution_aux
    (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
    (hComp : ∀
    (n : ℕ) (hn : 1 ≤ n)
    (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω)
    (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b)
    (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b),
      let hEx := classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH
      let T := terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      ∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
        T σ τ (hσr.trans hrτ) = (T σ r hσr).comp (T r τ hrτ))
    (hKComp : ∀
    (n : ℕ) (hn : 1 ≤ n)
    (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω)
    (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b)
    (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b),
      let hEx := classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH
      let T := terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      ∀ (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ),
        T σ τ (hσr.trans hrτ) = T r τ hrτ ∘ₖ T σ r hσr)
    (hJoint : ∀
    (n : ℕ) (hn : 1 ≤ n)
    (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω)
    (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b)
    (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b),
      let hEx := classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH
      Measurable (fun q : EvolutionQuery Ω γ =>
        terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
          hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q)) :
    SectionTwo.TerminalEvolutionConclusion := by
  intro n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
  let hEx := classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH
  exact construction_terminalEvolution_assembly n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hH
    (hComp n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive)
    (hKComp n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive)
    (hJoint n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive)

/-- The proof of the terminal evolution statement (companion paper, Proposition 2.1), relative
only to classical Dirichlet solvability on ellipsoids (Lieberman, Theorem 5.14) and
Hörmander's hypoellipticity theorem. All intermediate existence, composition and
joint-measurability premises are discharged by proved results. -/
theorem exists_terminalEvolution_of_classical
    (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement) :
    SectionTwo.TerminalEvolutionConclusion := by
  apply exists_terminalEvolution_aux hLE hH
  · intro n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
    exact terminalOperators_comp n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
      (classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH)
  · intro n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
    exact terminalFiberKernel_comp n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
      (classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH)
  · intro n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
    exact measurable_terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
      (classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH)

end HypoellipticAleksandrov.KineticAleksandrov
