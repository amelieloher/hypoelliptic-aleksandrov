module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsSource
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceInterior
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Final
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusionConsumers
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FourierDecay
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier

/-! # Uniform Green bounds for the actual signed corrector potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA Evolution Green Filter
open scoped Topology ENNReal Matrix.Norms.Elementwise

/-- The absolute signed physical potential is bounded by the potential of its absolute source. -/
theorem borelCorrectorPotential_abs_le {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (T : ℝ) (F : KineticPoint d → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ P, |F P| ≤ M) (P : KineticPoint d) :
    |borelCorrectorPotential K T F P| ≤
      borelCorrectorPotential K T (fun Q => |F Q|) P := by
  let g := F ∘ sectionTwoPoint
  have hgm : Measurable g := hF.comp (continuous_sectionTwoPoint d).measurable
  have hgb : ∀ Q, |g Q| ≤ M := fun Q => hFb _
  have hi := integrableOn_duhamelIntegrand_bounded K MeasurableSet.univ continuous_const
    g hgm M hM hgb (sectionTwoPoint P) T
  have hia := integrableOn_duhamelIntegrand_bounded K MeasurableSet.univ continuous_const
    (fun Q => |g Q|) (by simpa only [Real.norm_eq_abs] using hgm.norm) M hM
    (fun Q => by rw [abs_abs]; exact hgb Q) (sectionTwoPoint P) T
  have hb : ∀ r, |duhamelIntegrand K g (sectionTwoPoint P) r| ≤
      duhamelIntegrand K (fun Q => |g Q|) (sectionTwoPoint P) r := by
    intro r
    unfold duhamelIntegrand
    split
    · unfold duhamelSourceIntegral
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun w : EvolutionAmbientState d => g ⟨r, w.1, w.2⟩)
    · simp only [abs_zero, le_refl]
  change |∫ r in Ioc P.time T, duhamelIntegrand K g (sectionTwoPoint P) r| ≤ _
  have hn : |∫ r in Ioc P.time T, duhamelIntegrand K g (sectionTwoPoint P) r| ≤
      ∫ r in Ioc P.time T, |duhamelIntegrand K g (sectionTwoPoint P) r| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun r => duhamelIntegrand K g (sectionTwoPoint P) r)
  exact hn.trans (integral_mono
    (by simpa only [Real.norm_eq_abs, sectionTwoPoint] using hi.norm)
    (by simpa only [IntegrableOn, sectionTwoPoint, g, Function.comp_def] using hia) hb)

/-- The three analytic hypotheses give a coefficient-uniform bound for signed compact sources. -/
theorem borelCorrectorPotential_uniform_bound
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R),
      ∀ (F : KineticPoint d → ℝ), Continuous F → HasCompactSupport F →
        tsupport F ⊆ forwardCylinder Z₀ R hR →
        MemLp F (ENNReal.ofReal p) volume →
      ∀ P ∈ forwardCylinder Z₀ R hR,
        |borelCorrectorPotential K (Z₀.time + R ^ 2) F P| ≤
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
            (eLpNorm F (ENNReal.ofReal p) volume).toReal := by
  have hEv := exists_terminalEvolution_of_classical hLE hH
  have hIter := SectionTwo.iterationEvolutionStatement_of_conclusion hEv
  have hOcc := Occupation.parabolicOccupationFamily_holds
    (SectionTwo.occupationEvolutionStatement_of_conclusion hEv) hH hd lam Lam hlam hLam
  have hBlock := Decay.unit_frequency_block_W hIter d hd lam Lam hlam hLam
  have hDecay := Decay.fourierDecayFamily_of_unitBlock d hd lam Lam hlam hLam hIter hBlock
  obtain ⟨C, hC, hgreen⟩ := green_density_bound_of_slabFourierBounds hd lam Lam p
    hlam hLam hp (Green.slabFourierBounds_of_occupation_decay hd lam Lam hOcc hDecay)
  have hp1 : 1 < p := by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  let q := p / (p - 1)
  have hq : 1 < q := by
    dsimp only [q]
    rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hqp : q.HolderConjugate p := (Real.HolderConjugate.conjExponent hp1).symm
  refine ⟨C, hC, ?_⟩
  intro B hB S K hreal Z₀ R hR F hF hFc hFs hFLp P hP
  let Q := forwardCylinder Z₀ R hR
  let Γ := cylinderGreenMeasure K Z₀ R hR P
  let a := 2 - (4 * (d : ℝ) + 2) / p
  have ht : P.time < Z₀.time + R ^ 2 := hP.2.1
  let GP := greenMeasure K P.time (ENNReal.ofReal (remainingTime Z₀ P R))
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
  have hGP := greenMeasure_spec K P.time _
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
  let A := kineticReflectedCoefficient B
  have hBs : IsSmoothCoefficient B := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (hB.2.2.1 i j).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk
        (contDiff_const (c := (0 : PDE.Vec d)))))
  have hAs := isSmoothCoefficient_kineticReflectedCoefficient B hBs
  have hAreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient (kineticReflectedCoefficient A))
      (identityDrift d) S K := by
    have hBB : kineticReflectedCoefficient A = B := by
      funext t v
      simp only [A, kineticReflectedCoefficient, neg_neg]
    rw [hBB]
    exact hreal
  have hgreenB := hgreen (kineticReflection Z₀) R hR A hAs
    (isSymmetricCoefficient_kineticReflectedCoefficient B hB.2.2.2.1)
    (fun t v => hB.2.2.2.2.1 (-t) v) (fun t v => hB.2.2.2.2.2 (-t) v)
    S K hAreal
  rw [kineticReflection_involutive Z₀] at hgreenB
  obtain ⟨G, hG, hden, hn, hscale⟩ := hgreenB P hP GP hGP
  have hnorm : eLpNorm G (ENNReal.ofReal q) (volume.restrict Q) ≤
      ENNReal.ofReal (C * R ^ a) := by
    exact hn.trans (ENNReal.ofReal_le_ofReal hscale)
  have hden' : Γ = (volume.restrict Q).withDensity G := by
    dsimp only [Γ, cylinderGreenMeasure]
    rw [dite_eq_left ht]
    exact hden
  obtain ⟨g, hgm, hgn, hgd, hgb, hgLp⟩ := real_density_of_eLpNorm_bound
    (volume.restrict Q) Γ G hG hden' q (C * R ^ a) (lt_trans zero_lt_one hq)
    (mul_nonneg hC (Real.rpow_nonneg hR.le _)) hnorm
  have habs : MemLp (fun Q => |F Q|) (ENNReal.ofReal p) (volume.restrict Q) := by
    simpa only [Real.norm_eq_abs] using hFLp.norm.restrict Q
  have hpair := abp_potential_holder (volume.restrict Q) Γ g (fun Q => |F Q|) hqp
    hgm hgn (Eventually.of_forall fun Q => abs_nonneg (F Q)) hgd hgLp habs hgb
  have hsabs : tsupport (fun Q => |F Q|) ⊆ forwardCylinder Z₀ R hR := by
    apply Subset.trans _ hFs
    apply closure_mono
    intro P hP
    exact abs_ne_zero.mp hP
  have heq := integral_cylinderGreenMeasure K Z₀ R hR (fun Q => |F Q|)
    (fun Q => abs_nonneg _) hF.abs hFc.abs hsabs P ht
  obtain ⟨M, hM⟩ := hFc.exists_bound_of_continuous hF
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hFb : ∀ Q, |F Q| ≤ max M 0 := fun Q => (hM Q).trans (le_max_left _ _)
  have hfirst := borelCorrectorPotential_abs_le K (Z₀.time + R ^ 2) F hF.measurable
    (max M 0) hM0 hFb P
  have hlast : (eLpNorm (fun Q => |F Q|) (ENNReal.ofReal p)
      (volume.restrict Q)).toReal ≤ (eLpNorm F (ENNReal.ofReal p) volume).toReal := by
    rw [show (fun Q => |F Q|) = (fun Q => ‖F Q‖) from funext fun Q =>
      (Real.norm_eq_abs _).symm, eLpNorm_norm F hFLp.aestronglyMeasurable.restrict]
    exact ENNReal.toReal_mono hFLp.eLpNorm_ne_top (eLpNorm_mono_measure F Measure.restrict_le_self)
  exact hfirst.trans (by
    change borelCorrectorPotential K (Z₀.time + R ^ 2) (fun Q => |F Q|) P ≤ _
    change duhamelPotential K _ _ _ ≤ _
    rw [← heq]
    exact hpair.trans (mul_le_mul_of_nonneg_left hlast
      (mul_nonneg hC (Real.rpow_nonneg hR.le _))))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
