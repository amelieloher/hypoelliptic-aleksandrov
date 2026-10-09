module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSequence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluing

/-!
# Constructed whole-space classical viscous evolution

Actual moving-ball solutions are constructed internally from the two explicit
inputs. Their growing radii and pure-growth comparison yield a classical
whole-space limit with the original terminal bound and uniqueness.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ

/-- The whole-space branch of Actual bounded classical viscous evolution,
relative only to the two analytic hypotheses. -/
theorem exists_viscous_terminalSolution_wholeSpace
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum univ Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution univ Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder univ Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution univ Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder univ Γ τ)) := by
  obtain ⟨Z0, hZ0⟩ := hF.2.1.bddAbove_image
    (PDE.continuous_vecEuclideanNorm.comp continuous_fst).continuousOn
  let Z := max Z0 0
  have hZ : 0 ≤ Z := le_max_right _ _
  let r (j : ℕ) := Z + (j : ℝ) + 1
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hrZ (j : ℕ) : Z < r j := by
    dsimp [r]
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hrlim : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun j => by dsimp [r]; linarith) tendsto_natCast_atTop_atTop
  have hΓ0 : IsContinuousPiecewiseC1 (fun _ : ℝ => (0 : PDE.Vec n)) :=
    isContinuousPiecewiseC1_of_contDiff contDiff_const
  have hex (j : ℕ) : ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
        (fun _ => 0) B b ε τ F v := by
    have hFj : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 (r j))
        (fun _ => 0) τ F := by
      refine ⟨hF.1, hF.2.1, fun q hq => ⟨?_, mem_univ _⟩⟩
      apply (mem_movingBall_iff_norm_lt (hr j)).mpr
      simp only [sub_zero]
      exact ((hZ0 ⟨q, hq, rfl⟩).trans (le_max_left _ _)).trans_lt (hrZ j)
    obtain ⟨v, hv, -, -⟩ := exists_viscous_terminalSolution_innerBall
      hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ0 (hr j)
      τ F hFj ε hε hε1 C hC hFC
    exact ⟨v, hv⟩
  choose v hv using hex
  obtain ⟨hf, hbound⟩ := isClassicalViscousTerminalSolution_wholeSpace_ball_limit
    hlam hB hb hε hε1 hC F hFC r hrlim v hv hBs hBsym hbs hH
  have hsame (w : KineticPoint n → ℝ) :
      IsClassicalViscousTerminalSolution univ Γ B b ε τ F w ↔
        IsClassicalViscousTerminalSolution univ (fun _ => 0) B b ε τ F w := by
    simp only [IsClassicalViscousTerminalSolution, evolutionPastClosedCylinder,
      evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
      evolutionLateralFrontier, movingDomain_univ_eq]
  have hK : evolutionPastClosedCylinder univ Γ τ =
      evolutionPastClosedCylinder univ (fun _ : ℝ => (0 : PDE.Vec n)) τ := by
    simp only [evolutionPastClosedCylinder, movingDomain_univ_eq]
  have hfΓ := (hsame _).mpr hf
  refine ⟨fun p => limUnder atTop (fun j => v j p), hfΓ, ?_, ?_⟩
  · simpa only [hK] using hbound
  · intro w hw
    exact classical_unique isOpen_univ hΓ.1 hlam hB hb hε.le hε1 hw hfΓ

end Data

end HypoellipticAleksandrov.KineticAleksandrov
