module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionUniformBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSpacetimeConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyOperator

/-! # Joint measurability of the selected raw source and its literal zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set HypoellipticAleksandrov.Parabolic

/-- The explicit raw time representative is continuous jointly in time and native space. -/
theorem construction_rawTimeJet_joint_continuous {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) :
    Continuous (fun z : ℝ × XV d => kineticTimeDerivative
      (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨z.1, z.2.1, z.2.2⟩) := by
  simp_rw [timeCutoffProfile_timeDerivative, barrier_timeDerivative]
  have hv : Continuous (fun z : ℝ × XV d => PDE.vecNormSq z.2.2) :=
    PDE.contDiff_vecNormSq.continuous.comp continuous_snd.snd
  have he : Continuous (fun z : ℝ × XV d => Real.exp (-mu * z.1)) :=
    (continuous_const.mul continuous_fst).rexp
  have hb : Continuous (fun z : ℝ × XV d => barrier mu R ⟨z.1, z.2.1, z.2.2⟩) :=
    he.mul (continuous_const.sub (hv.div_const _))
  have hs := ((continuous_selectedFlatProfile h r).comp continuous_snd).sub hb
  exact ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs).neg.mul
    ((continuous_const.mul he).mul (continuous_const.sub (hv.div_const _)))

/-- The explicit raw source is jointly measurable, with the original selected flat jets. -/
theorem construction_rawSource_joint_measurable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) :
    Measurable (fun z : ℝ × XV d =>
      timeCutoffSourceRepresentative h r mu R ⟨z.1, z.2.1, z.2.2⟩) := by
  obtain ⟨hx, hv, hh⟩ := measurable_flatProfile_jets h r
  have hA := (selectedProfile_spec h).2.2.2.2.1
  have he : Continuous (fun z : ℝ × XV d => Real.exp (-mu * z.1)) :=
    (continuous_const.mul continuous_fst).rexp
  have hvs : Continuous (fun z : ℝ × XV d => PDE.vecNormSq z.2.2) :=
    PDE.contDiff_vecNormSq.continuous.comp continuous_snd.snd
  have hb : Continuous (fun z : ℝ × XV d => barrier mu R ⟨z.1, z.2.1, z.2.2⟩) :=
    he.mul (continuous_const.sub (hvs.div_const _))
  have hs := ((continuous_selectedFlatProfile h r).comp continuous_snd).sub hb
  have ht := ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs).measurable
  have ht2 : Measurable (fun z : ℝ × XV d => deriv (deriv timeCutoffTheta)
      (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩)) := by
    simp_rw [deriv2_timeCutoffTheta]
    exact measurable_const.mul
      (((contDiff_flatteningSlope.continuous_deriv (by simp)).comp
        ((continuous_const.mul hs).add continuous_const)).measurable)
  have hBG (i : Fin d) : Measurable (fun z : ℝ × XV d =>
      kineticVelocityGradient (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i) := by
    simp_rw [barrier_velocityGradient]
    exact (((continuous_const.mul he).div_const _).neg.mul
      ((continuous_apply i).comp continuous_snd.snd)).measurable
  have hBH (i k : Fin d) : Measurable (fun z : ℝ × XV d =>
      kineticVelocityHessian (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i k) := by
    simp only [barrier_velocityHessian, Matrix.smul_apply, smul_eq_mul]
    exact (((continuous_const.mul he).div_const _).neg.mul continuous_const).measurable
  have hpos (i : Fin d) : Measurable (fun z : ℝ × XV d =>
      flatProfilePositionJet h r z.2 i) :=
    (((measurable_pi_apply i).comp hx).comp measurable_snd)
  have hvel (i : Fin d) : Measurable (fun z : ℝ × XV d =>
      flatProfileVelocityJet h r z.2 i) :=
    (((measurable_pi_apply i).comp hv).comp measurable_snd)
  have htime := (construction_rawTimeJet_joint_continuous h r mu R).measurable
  have htransport : Measurable (fun z : ℝ × XV d => PDE.vecDot z.2.2
      (fun i => deriv timeCutoffTheta
        (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩) *
          flatProfilePositionJet h r z.2 i)) := by
    unfold PDE.vecDot
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd.snd).mul (ht.mul (hpos i)))
  have hcontraction : Measurable (fun z : ℝ × XV d => matrixContraction
      (profileMatrix h z.2) (fun i k =>
        deriv timeCutoffTheta
          (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩) *
            (flatProfileHessian h r z.2 i k -
              kineticVelocityHessian (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i k) +
        deriv (deriv timeCutoffTheta)
          (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩) *
            (flatProfileVelocityJet h r z.2 i -
              kineticVelocityGradient (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i) *
            (flatProfileVelocityJet h r z.2 k -
              kineticVelocityGradient (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ k))) := by
    unfold matrixContraction
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun k _ =>
      ((hA i k).comp measurable_snd).mul
        ((ht.mul (((hh i k).comp measurable_snd).sub (hBH i k))).add
          ((ht2.mul ((hvel i).sub (hBG i))).mul ((hvel k).sub (hBG k))))))
  simpa only [timeCutoffSourceRepresentative, timeCutoffProfile_timeDerivative,
    Pi.sub_apply, Prod.mk.eta] using! (htime.add htransport).sub hcontraction

/-- A measurable representative of the full extended source, including the boundary. -/
def constructionIndicatorSource {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (z : ℝ × XV d) : ℝ :=
  {y | profileFunction h y.2 < 1}.indicator
    (fun y => timeCutoffSourceRepresentative h r mu R ⟨y.1, y.2.1, y.2.2⟩) z

/-- The selected zero-extended source is jointly measurable. -/
theorem construction_indicatorSource_measurable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) :
    Measurable (constructionIndicatorSource h r mu R) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  exact (construction_rawSource_joint_measurable h r mu R).indicator
    (isOpen_lt (hH.comp continuous_snd) continuous_const).measurableSet

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
