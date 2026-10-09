module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
import Mathlib.Tactic

/-! # Normalization of the actual canonical autonomous solution at arbitrary scales -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory SectionTwo Evolution TheoremA

/-- The kinetic scaling keeps physical position translations and does not shift velocity. -/
def returnScaling (r : ℝ) (hr : 0 < r) (X : ℝ) : Scaling.KineticAffineScaling 1 :=
  ⟨r ^ 2, r, r ^ 3, 0, 0, fun _ => X, 0, by positivity, hr, by positivity⟩

/-- The scaled autonomous coefficient retains exactly the original ellipticity constants. -/
def returnScaledCoefficient {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (r X : ℝ) :
    SmoothAutonomous lam Lam where
  a x v := A.a (X + r ^ 3 * x) (r * v)
  smooth := by
    change ContDiff ℝ (⊤ : ℕ∞)
      ((Function.uncurry A.a) ∘ fun z : ℝ × ℝ => (X + r ^ 3 * z.1, r * z.2))
    exact A.smooth.comp (by fun_prop)
  bounds x v := A.bounds _ _

/-- The scaled full coefficient is the literal autonomous coefficient of the scaled scalar. -/
theorem returnScaling_coefficient {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (r : ℝ) (hr : 0 < r) (X : ℝ) :
    (returnScaling r hr X).coefficient (evolutionCoefficient A.a) =
      evolutionCoefficient (returnScaledCoefficient A r X).a := by
  ext s y z i j
  simp [Scaling.KineticAffineScaling.coefficient, Scaling.KineticAffineScaling.time,
    Scaling.KineticAffineScaling.position, Scaling.KineticAffineScaling.transport,
    returnScaling, evolutionCoefficient, returnScaledCoefficient, hr.ne']

/-- Kinetic scaling preserves the identity drift exactly. -/
theorem returnScaling_drift (r : ℝ) (hr : 0 < r) (X : ℝ) :
    (returnScaling r hr X).drift (identityDrift 1) = identityDrift 1 := by
  funext y
  ext i
  simp [Scaling.KineticAffineScaling.drift, Scaling.KineticAffineScaling.position,
    returnScaling, identityDrift]
  field_simp

/-- A normalized classical homogeneous solution represents the original canonical action.
The existence assertion is proved from the full-space producer; it is not a premise. -/
theorem exists_return_scaled_solution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z)
    (hF0 : ∀ z, 0 ≤ F z) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (r : ℝ) (hr : 0 < r) (X : ℝ) :
    ∃ U : Point → ℝ, IsNonnegativeHomogeneousSolution
      (returnReflectedCoefficient (returnScaledCoefficient A r X)) U ∧
      ∀ p : Point, 0 < p.time →
        U p = S hH hLE hlam hLam A (r ^ 2 * p.time) F
          (X - r ^ 3 * p.position 0, r * p.velocity 0) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let G := physicalTerminalDatum (scalarTerminalDatum F)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (scalarTerminalDatum_smooth F hF).comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨w, hw, hrep⟩ := fullspace_bounded_smooth_solution hH hlam hLam A E
    (fullSpaceEvolution_spec hH hLE hlam hLam A) 0 G hG
  let Φ := returnScaling r hr X
  let W : Point → ℝ := w ∘ Φ.point
  let U : Point → ℝ := W ∘ autonomousReversal ∘ autonomousPositionReflection
  have heq (p : Point) (hp : 0 < p.time) :
      U p = S hH hLE hlam hLam A (r ^ 2 * p.time) F
        (X - r ^ 3 * p.position 0, r * p.velocity 0) := by
    have ht : 0 ≤ r ^ 2 * p.time := by positivity
    have hpoint : Φ.point (autonomousReversal (autonomousPositionReflection p)) =
        ⟨-(r ^ 2 * p.time), fun _ => r * p.velocity 0,
          fun _ => X - r ^ 3 * p.position 0⟩ := by
      apply KineticPoint.ext
      · simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
          Scaling.KineticAffineScaling.time, autonomousReversal, autonomousPositionReflection]
      · funext i
        rw [Fin.eq_zero i]
        simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
          Scaling.KineticAffineScaling.position, autonomousReversal, autonomousPositionReflection]
      · funext i
        rw [Fin.eq_zero i]
        simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
          Scaling.KineticAffineScaling.transport, autonomousReversal,
          autonomousPositionReflection, sub_eq_add_neg]
    dsimp only [U, W, Function.comp_apply]
    rw [hpoint]
    unfold S fullSpaceAction
    split
    · exact hrep (wholeSpaceQuery (-(r ^ 2 * p.time)) 0 (neg_nonpos.mpr ht)
      (fun _ => r * p.velocity 0) (fun _ => X - r ^ 3 * p.position 0)) rfl
    · rename_i h
      exact False.elim (h ht)
  let O : Set Point := {p | 0 < p.time}
  let T : EvolutionVec 1 → ℝ × (PDE.Vec 1 × PDE.Vec 1) := fun q =>
    (-(r ^ 2 * timeCoord 1 q), r • transportedCoord 1 q,
      (fun _ => X) - r ^ 3 • diffusedCoord 1 q)
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by unfold T; fun_prop
  have hmaps : MapsTo T (evolutionHomeomorph 1 ⁻¹' O)
      (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
    intro q hq
    refine ⟨?_, ?_⟩
    · change -(r ^ 2 * timeCoord 1 q) < 0
      change 0 < timeCoord 1 q at hq
      nlinarith [sq_pos_of_pos hr]
    · change r • transportedCoord 1 q ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
      rw [movingDomain_wholeSpace]
      trivial
  have hraw := hw.2.2.1.comp hT.contDiffOn hmaps
  have hreg : IsKineticC112On U O := by
    apply isKineticC112On_of_contDiffOn (isOpen_lt continuous_const continuous_time)
    convert hraw using 1
    funext q
    dsimp [U, W, Φ, returnScaling, Scaling.KineticAffineScaling.point,
      Scaling.KineticAffineScaling.time, Scaling.KineticAffineScaling.position,
      Scaling.KineticAffineScaling.transport, autonomousReversal,
      autonomousPositionReflection, T]
    congr 1
    apply KineticPoint.ext
    · change 0 + r ^ 2 * (-q 0) = -(r ^ 2 * q 0)
      ring
    · funext i
      change 0 + r * transportedCoord 1 q i = r * transportedCoord 1 q i
      ring
    · funext i
      change X + (r ^ 2 * -q 0) * 0 + r ^ 3 * -(diffusedCoord 1 q i) =
        X - r ^ 3 * diffusedCoord 1 q i
      ring
  obtain ⟨M, hM, hbound⟩ := F.exists_bound
  refine ⟨U, ⟨⟨M, ?_⟩, ?_, hreg, ?_⟩, heq⟩
  · intro p hp
    rw [heq p hp, S_eq_integral hH hLE hlam hLam A _ (by positivity)]
    exact abs_integral_boundedBorel_le F _
      (Kphysical_mass_one hH hLE hlam hLam A _ (by positivity) _).le hM hbound
  · intro p hp
    rw [heq p hp, S_eq_integral hH hLE hlam hLam A _ (by positivity)]
    exact integral_nonneg hF0
  · intro p hp
    change autonomousScalarOperator (reflectedAutonomous (returnScaledCoefficient A r X).a)
      ((W ∘ autonomousReversal) ∘ autonomousPositionReflection) p = 0
    rw [autonomous_generator_positionReflection, autonomous_generator_reversal]
    let q := autonomousReversal (autonomousPositionReflection p)
    have hq : Φ.point q ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) 0 := by
      refine ⟨?_, ?_⟩
      · change 0 + r ^ 2 * (-p.time) < 0
        nlinarith [sq_pos_of_pos hr]
      · change (Φ.point q).position ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
        rw [movingDomain_wholeSpace]
        trivial
    have hrawmem : Scaling.rawPoint (Φ.point q) ∈
        evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0 := hq
    have hopen : IsOpen (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
      have he : evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0 =
          {x : ℝ × (PDE.Vec 1 × PDE.Vec 1) | x.1 < 0} := by
        ext x
        simp [evolutionPastInteriorRaw, autonomousWholeDomain, movingDomain]
      rw [he]
      exact isOpen_lt continuous_fst continuous_const
    have hw2 := (hw.2.2.1.contDiffAt (hopen.mem_nhds hrawmem)).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
    have hscaled := Scaling.KineticAffineScaling.transportedForwardOperator_comp_point (Φ := Φ)
      (u := w) (p := q) (evolutionCoefficient A.a) (identityDrift 1) hw2
    rw [returnScaling_coefficient A r hr X, returnScaling_drift r hr X] at hscaled
    rw [show transportedForwardOperator (evolutionCoefficient (returnScaledCoefficient A r X).a)
        (identityDrift 1) W q = r ^ 2 *
          transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) w
            (Φ.point q) from hscaled,
      hw.2.2.2.1 _ hq, mul_zero, neg_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
