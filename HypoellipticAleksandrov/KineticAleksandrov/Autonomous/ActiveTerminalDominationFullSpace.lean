module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFullSpace

/-! # Full-space terminal actions in native and physical coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Time autonomy identifies an absolute native query with the scalar elapsed kernel. -/
theorem enlargedFullSpace_native_elapsed_integral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (t : ℝ) (ht : 0 ≤ t)
    (F : Point → ℝ) (hF : Measurable F) :
    (∫ w, F ⟨P.time + t, w.2, w.1⟩
      ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
        (wholeSpaceQuery P.time (P.time + t) (by linarith) P.velocity P.position)) =
      ∫ z, F (enlargedTerminalPoint (P.time + t) z)
        ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
          (P.position 0, P.velocity 0) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let q := wholeSpaceQuery P.time (P.time + t) (by linarith) P.velocity P.position
  have hq : autonomousQueryShift (-P.time) q =
      wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0) := by
    apply Subtype.ext
    dsimp [autonomousQueryShift, q, wholeQuery, wholeSpaceQuery]
    rw [max_eq_left ht]
    have hx : (fun _ : Fin 1 => P.position 0) = P.position := by
      funext i
      exact congrArg P.position (Subsingleton.elim 0 i)
    have hv : (fun _ : Fin 1 => P.velocity 0) = P.velocity := by
      funext i
      exact congrArg P.velocity (Subsingleton.elim 0 i)
    rw [hx, hv]
    congr 1 <;> ring
  have hk := fullspace_kernel_timeShift A E
    (fullSpaceEvolution_spec hH hLE hlam hLam A) (-P.time) q
  rw [hq] at hk
  change (∫ w, F ⟨P.time + t, w.2, w.1⟩ ∂E.2.master q) =
    ∫ z, F (enlargedTerminalPoint (P.time + t) z)
      ∂(E.2.master (wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0))).map nativeToXV
  have hm := integral_map nativeToXV_measurable.aemeasurable
    (hF.comp (enlargedTerminalPoint_measurable (P.time + t))).aestronglyMeasurable
      (μ := E.2.master (wholeQuery (Real.toNNReal t) (P.position 0, P.velocity 0)))
  change _ = ∫ z, (F ∘ enlargedTerminalPoint (P.time + t)) z ∂_
  rw [hm, hk]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change F ⟨P.time + t, w.2, w.1⟩ = F (enlargedTerminalPoint (P.time + t) (nativeToXV w))
  congr 1
  apply KineticPoint.ext
  · rfl
  · funext i
    exact congrArg w.2 (Subsingleton.elim i 0)
  · funext i
    exact congrArg w.1 (Subsingleton.elim i 0)


/-- Time autonomy identifies an absolute native query with the scalar elapsed kernel. -/
theorem enlargedFullSpace_native_terminal_integral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (b : ℝ) (hb : P.time ≤ b)
    (F : Point → ℝ) (hF : Measurable F) :
    (∫ w, F ⟨b, w.2, w.1⟩
      ∂(fullSpaceEvolution hH hLE hlam hLam A).2.master
        (wholeSpaceQuery P.time b hb P.velocity P.position)) =
      ∫ z, F (enlargedTerminalPoint b z)
        ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal (b - P.time))
          (P.position 0, P.velocity 0) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let q := wholeSpaceQuery P.time b hb P.velocity P.position
  have hq : autonomousQueryShift (-P.time) q =
      wholeQuery (Real.toNNReal (b - P.time)) (P.position 0, P.velocity 0) := by
    apply Subtype.ext
    dsimp [autonomousQueryShift, q, wholeQuery, wholeSpaceQuery]
    rw [max_eq_left (sub_nonneg.mpr hb)]
    have hx : (fun _ : Fin 1 => P.position 0) = P.position := by
      funext i
      exact congrArg P.position (Subsingleton.elim 0 i)
    have hv : (fun _ : Fin 1 => P.velocity 0) = P.velocity := by
      funext i
      exact congrArg P.velocity (Subsingleton.elim 0 i)
    rw [hx, hv]
    congr 1
    ring
  have hk := fullspace_kernel_timeShift A E
    (fullSpaceEvolution_spec hH hLE hlam hLam A) (-P.time) q
  rw [hq] at hk
  change (∫ w, F ⟨b, w.2, w.1⟩ ∂E.2.master q) =
    ∫ z, F (enlargedTerminalPoint b z)
      ∂(E.2.master (wholeQuery (Real.toNNReal (b - P.time))
        (P.position 0, P.velocity 0))).map nativeToXV
  have hm := integral_map nativeToXV_measurable.aemeasurable
    (hF.comp (enlargedTerminalPoint_measurable b)).aestronglyMeasurable
      (μ := E.2.master (wholeQuery (Real.toNNReal (b - P.time)) (P.position 0, P.velocity 0)))
  change _ = ∫ z, (F ∘ enlargedTerminalPoint b) z ∂_
  rw [hm, hk]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change F ⟨b, w.2, w.1⟩ = F (enlargedTerminalPoint b (nativeToXV w))
  congr 1
  apply KineticPoint.ext
  · rfl
  · funext i
    exact congrArg w.2 (Subsingleton.elim i 0)
  · funext i
    exact congrArg w.1 (Subsingleton.elim i 0)


end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
