module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationGreen
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity

/-! # Exit representation for a solution defined only on its kinetic cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic SectionTwo

/-- The actual velocity-ball exit measure represents the source's local solution class. -/
theorem local_cone_representation
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (Z₀ : KineticPoint d) (U : KineticPoint d → ℝ)
    (hUc : ContinuousOn U (closure (forwardCylinder Z₀ R hR)))
    (hUs : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (hUe : ∀ Q ∈ forwardCylinder Z₀ R hR,
      forwardKineticOperator (ofTimeVelocityCoefficient B) U Q = 0)
    (P : LocalBallStart v₀ R) (hPv : v₀ = Z₀.velocity)
    (hP : P.1 ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (T : {t : ℝ // P.1.time < t}) (hT : T.1 - P.1.time = R ^ 2 / 8) :
    U P.1 = ∫ Q, U Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T := by
  subst v₀
  obtain ⟨χ, hχ, _hχcompact, hs, _hχb, hχone⟩ := exists_local_position_cutoff (d := d) hR
  let V := localCutoffSolution Z₀ χ U
  let F := (localStrip P.1.time T.1 Z₀.velocity R).indicator
    (fun Q => localCutoffTransport Z₀ χ Q * U Q)
  have ha : Z₀.time < P.1.time := hP.1
  have htop : T.1 < Z₀.time + R ^ 2 := by
    have hpt := hP.2.1
    nlinarith only [hpt, hT, sq_pos_of_pos hR]
  have hrel : Continuous (relativePosition Z₀) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have hVc := localCutoffSolution_continuousOn Z₀ hR ha.le htop.le U hUc χ hχ.continuous hs
  have hUb := localRepresentation_supported_mul_bounded Z₀ hR ha.le htop.le U hUc χ hs
    (localPositionCutoff Z₀ χ) (hχ.continuous.comp hrel)
    (fun Q hx => by
      change χ (relativePosition Z₀ Q) = 0
      exact image_eq_zero_of_notMem_tsupport hx)
  obtain ⟨L, _hL, hVb⟩ := hUb
  have hsm := mass_classical_homogeneous_smooth hH B hB
    (isOpen_forwardCylinder Z₀ R hR) U hUs hUe
  have hVs := localCutoffSolution_contDiffOn Z₀ hR ha htop U hsm χ hχ hs
  have hVr : IsKineticC112On V (localStrip P.1.time T.1 Z₀.velocity R) :=
    TheoremA.isKineticC112On_of_contDiffOn (isOpen_localStrip P.1.time T.1 Z₀.velocity R)
      (boundary_physical_smooth_to_native hVs)
  have hfc := localRepresentation_supported_mul_continuousOn Z₀ hR ha.le htop.le U hUc
    χ hs (localCutoffTransport Z₀ χ) (continuous_localCutoffTransport Z₀ hχ)
    (fun Q hx => localCutoffTransport_zero Z₀ Q χ hx)
  have hFm : Measurable F := localRepresentation_indicator_measurable _ _ _ _ _
    (hfc.mono (localStrip_subset_closed P.1.time T.1 Z₀.velocity R))
  obtain ⟨M, hM, hFb⟩ := localRepresentation_supported_mul_bounded Z₀ hR ha.le htop.le
    U hUc χ hs (localCutoffTransport Z₀ χ) (continuous_localCutoffTransport Z₀ hχ)
    (fun Q hx => localCutoffTransport_zero Z₀ Q χ hx)
  have hFe : ∀ Q ∈ localStrip P.1.time T.1 Z₀.velocity R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) V Q = F Q := by
    intro Q hQ
    change forwardKineticOperator (ofTimeVelocityCoefficient B)
      (localCutoffSolution Z₀ χ U) Q =
      (localStrip P.1.time T.1 Z₀.velocity R).indicator
        (fun Q => localCutoffTransport Z₀ χ Q * U Q) Q
    rw [indicator_of_mem hQ]
    by_cases hx : relativePosition Z₀ Q ∈ tsupport χ
    · have houter : Q ∈ forwardCylinder Z₀ R hR :=
        ⟨ha.trans hQ.1, hQ.2.1.trans htop, hQ.2.2, hs hx⟩
      rw [localCutoffSolution_operator Z₀ _ hχ hUs houter, hUe Q houter,
        mul_zero, zero_add]
    · rw [localCutoffSolution_operator_zero Z₀ Q _ χ U hx,
        localCutoffTransport_zero Z₀ Q χ hx, zero_mul]
  have hFbound : ∀ Q ∈ localStrip P.1.time T.1 Z₀.velocity R, |F Q| ≤ M := by
    intro Q hQ
    change |(localStrip P.1.time T.1 Z₀.velocity R).indicator
      (fun Q => localCutoffTransport Z₀ χ Q * U Q) Q| ≤ M
    rw [indicator_of_mem hQ]
    exact hFb Q (localStrip_subset_closed _ _ _ _ hQ)
  have hid := localRepresentation_bounded_source_formula hH hLE hd hlam hLam B hB
    Z₀.velocity hR P T V hVr hVc ⟨L, hVb⟩ F hFm hFe M hM hFbound
  have hz := ballSourcePotential_local_cutoff_zero hH hLE hd hlam hLam B hB
    Z₀ hR P hP T hT χ hχone U
  change V P.1 + ballSourcePotential hH hLE hd hlam hLam B hB Z₀.velocity hR
    P.1.time T.1 F P.1 = _ at hid
  rw [hz, add_zero] at hid
  have hstart : V P.1 = U P.1 := by
    have hx := local_cone_cutoff_mem Z₀ P.1 P.1 hR hP le_rfl
      (by nlinarith only [sq_nonneg R]) (by
        have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
          PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
        simp only [sub_self, zero_smul, hz, mul_zero]
        exact le_rfl)
    change χ (relativePosition Z₀ P.1) * U P.1 = U P.1
    rw [hχone _ (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx), one_mul]
  rw [hstart] at hid
  refine hid.trans (integral_congr_ae ?_)
  filter_upwards [ballExitRaw_cone hH hLE hd hlam hLam B hB Z₀.velocity hR P T]
    with Q hQ
  have ht : Q.time ≤ P.1.time + R ^ 2 / 8 := by linarith only [hQ.2.1, hT]
  have hx := local_cone_cutoff_mem Z₀ P.1 Q hR hP hQ.1 ht hQ.2.2
  change χ (relativePosition Z₀ Q) * U Q = U Q
  rw [hχone _ (PDE.euclideanBall_subset_euclideanClosedBall _ _ hx), one_mul]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
