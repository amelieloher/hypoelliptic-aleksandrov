module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolution
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TranslationCovarianceSolution
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Position translation of the actual ball boundary solution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA Parabolic

/-- Physical position translation, preserving time and velocity. -/
def boundaryPositionShift {d : ℕ} (h : PDE.Vec d) (P : KineticPoint d) : KineticPoint d :=
  ⟨P.time, P.position + h, P.velocity⟩

/-- Physical position translation as a homeomorphism. -/
def boundaryPositionHomeomorph {d : ℕ} (h : PDE.Vec d) :
    KineticPoint d ≃ₜ KineticPoint d :=
  (KineticPoint.homeomorphProd d).trans
    (((Homeomorph.refl ℝ).prodCongr
      ((Homeomorph.addRight h).prodCongr (Homeomorph.refl (PDE.Vec d)))).trans
        (KineticPoint.homeomorphProd d).symm)

/-- Position translation preserves the prescribed smooth test class. -/
theorem boundary_shift_smooth {d : ℕ} (h : PDE.Vec d) (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm)) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((φ ∘ boundaryPositionShift h) ∘ (KineticPoint.equivProd d).symm) :=
  hφ.comp (contDiff_fst.prodMk
    ((contDiff_snd.fst.add contDiff_const).prodMk contDiff_snd.snd))

/-- The physical operator commutes with position translation. -/
theorem boundary_shift_operator {d : ℕ} (B : CoefficientField d)
    (h : PDE.Vec d) (φ : KineticPoint d → ℝ) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) (φ ∘ boundaryPositionShift h) P =
      forwardKineticOperator (ofTimeVelocityCoefficient B) φ (boundaryPositionShift h P) := by
  rw [forwardKineticOperator_apply, forwardKineticOperator_apply]
  have ht : kineticTimeDerivative (φ ∘ boundaryPositionShift h) P =
      kineticTimeDerivative φ (boundaryPositionShift h P) := rfl
  have hv : kineticVelocityHessian (φ ∘ boundaryPositionShift h) P =
      kineticVelocityHessian φ (boundaryPositionShift h P) := rfl
  have hx : kineticPositionGradient (φ ∘ boundaryPositionShift h) P =
      kineticPositionGradient φ (boundaryPositionShift h P) := by
    funext i
    simp only [kineticPositionGradient, PDE.classicalGradient_apply]
    exact congrArg (fun L => L (PDE.basisVec i))
      (fderiv_comp_add_right (𝕜 := ℝ)
        (f := fun x : PDE.Vec d => φ ⟨P.time, x, P.velocity⟩) (x := P.position) h)
  rw [ht, hv, hx]
  rfl

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Canonical kernel covariance follows from existence and unique realization. -/
theorem boundary_ballKernel_covariant :
    IsTranslationCovariantEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (localBallKernel hH hLE hd hlam hLam B hB v₀ hR) := by
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hb := identityDrift_bounds d
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, hcov, -, -⟩ :=
    exists_terminalEvolution_of_classical hLE hH d hd lam Lam 1 1 hlam hLam
      one_pos le_rfl (PDE.euclideanBall v₀ R) (fun _ => 0)
      (zIndependentCoefficient B) (identityDrift d) (localBall_admissible v₀ hR)
      (zeroCurve_piecewiseC1 d) hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2
  have hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K := ⟨hc, hi, he, hcomp⟩
  have hK := congrArg Prod.snd
    (localBallEvolution_unique hH hLE hd hlam hLam B hB v₀ hR (S, K) hreal)
  change K = localBallKernel hH hLE hd hlam hLam B hB v₀ hR at hK
  rw [← hK]
  exact hcov (fun _ _ _ _ => rfl)

/-- Translation of the actual absolute-time source integral. -/
theorem boundary_duhamel_translation (h : PDE.Vec d) (T : ℝ)
    (g : KineticPoint d → ℝ) (hg : Measurable g) (p : KineticPoint d) :
    duhamelPotential (localBallKernel hH hLE hd hlam hLam B hB v₀ hR) T g
      (kineticVelocityShift h p) =
    duhamelPotential (localBallKernel hH hLE hd hlam hLam B hB v₀ hR) T
      (g ∘ kineticVelocityShift h) p := by
  classical
  let K := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
  unfold duhamelPotential
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  unfold duhamelIntegrand
  by_cases hp : p.time ≤ r ∧ p.position ∈
      movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) p.time
  · rw [dite_eq_left hp]
    split
    · change duhamelSourceIntegral K g
        ⟨(p.time, r, p.position, p.velocity + h), hp.1, hp.2, mem_univ _⟩ =
        duhamelSourceIntegral K (g ∘ kineticVelocityShift h)
          ⟨(p.time, r, p.position, p.velocity), hp.1, hp.2, mem_univ _⟩
      let w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) p.time :=
        ⟨(p.position, p.velocity), hp.2, mem_univ _⟩
      have ht := master_translation (PDE.isOpen_euclideanBall v₀ R).measurableSet K
        (boundary_ballKernel_covariant hH hLE hd hlam hLam B hB v₀ hR)
        p.time r hp.1 w h
      change Measure.map (evolutionAmbientStateShift h)
        (K.master ⟨(p.time, r, p.position, p.velocity), hp.1, hp.2, mem_univ _⟩) =
        K.master ⟨(p.time, r, p.position, p.velocity + h), hp.1, hp.2, mem_univ _⟩ at ht
      unfold duhamelSourceIntegral
      rw [← ht, integral_map (measurable_evolutionAmbientStateShift h).aemeasurable]
      · rfl
      · exact (hg.comp (KineticPoint.continuous_mk continuous_const continuous_fst
          continuous_snd).measurable).aestronglyMeasurable
    · rename_i hn
      exact (hn hp).elim
  · rw [dite_eq_right hp]
    split
    · rename_i hs
      exact (hp hs).elim
    · rfl

/-- The finite-strip source cutoff commutes with physical position translation. -/
theorem ballSourcePotential_translation (h : PDE.Vec d) (a T : ℝ)
    (F : KineticPoint d → ℝ) (hF : Measurable F) (P : KineticPoint d) :
    ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F
      (boundaryPositionShift h P) =
    ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T
      (F ∘ boundaryPositionShift h) P := by
  have hg : Measurable ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint) :=
    (hF.indicator (isOpen_localStrip a T v₀ R).measurableSet).comp
      (sectionTwoHomeomorph d).measurable
  have ht := boundary_duhamel_translation hH hLE hd hlam hLam B hB v₀ hR
    h T ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint) hg (sectionTwoPoint P)
  have he : ((localStrip a T v₀ R).indicator F ∘ sectionTwoPoint) ∘
      kineticVelocityShift h =
      (localStrip a T v₀ R).indicator (F ∘ boundaryPositionShift h) ∘ sectionTwoPoint := by
    funext Q
    by_cases hQ : sectionTwoPoint Q ∈ localStrip a T v₀ R
    · simp only [Function.comp_apply, indicator_of_mem hQ]
      rw [indicator_of_mem (show sectionTwoPoint (kineticVelocityShift h Q) ∈
        localStrip a T v₀ R from hQ)]
      rfl
    · simp only [Function.comp_apply, indicator_of_notMem hQ]
      rw [indicator_of_notMem (show sectionTwoPoint (kineticVelocityShift h Q) ∉
        localStrip a T v₀ R from hQ)]
  rw [he] at ht
  exact ht

/-- Position covariance of the literal smooth boundary solution. -/
theorem ballBoundarySolution_translation (h : PDE.Vec d) (a T : ℝ)
    (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) (P : KineticPoint d) :
    ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ
      (boundaryPositionShift h P) =
    ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T
      (φ ∘ boundaryPositionShift h) P := by
  unfold ballBoundarySolution
  rw [ballSourcePotential_translation hH hLE hd hlam hLam B hB v₀ hR h a T _
    (boundary_probe_operator_bounded B hB φ hφ hc).1.measurable]
  congr 1
  congr 1
  funext Q
  exact (boundary_shift_operator B h φ Q).symm

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
