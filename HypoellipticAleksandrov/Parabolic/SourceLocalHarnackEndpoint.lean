module

public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnack
public import HypoellipticAleksandrov.Parabolic.LocalHarnackEndpoint

/-!
# Terminal endpoint for the source-aware local parabolic Harnack estimate

This module removes strict source positivity from the one-carrier
source-aware estimate by constant perturbation and terminal-face continuity.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The source-aware local parabolic Harnack estimate extends from strictly
positive source values to nonnegative data at the exact terminal face. -/
theorem exists_source_local_parabolic_harnack_nonnegative
    (d : Nat) (hd : 1 ≤ d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) :
    ∃ hBox C : Real, 0 < hBox ∧ hBox ≤ 1 ∧ 0 < C ∧
      ∀ (K U : Set (TimeVelocity d)) (B : CoefficientField d)
        (q F : TimeVelocity d → Real),
        IsCompact K → K ⊆ U → IsOpen U →
        parabolicClosedBox 2 2 0 0 ⊆ K →
        IsContinuousCoefficientOn B U → ContDiffOn Real 2 q U →
        ContinuousOn F U → IsNonnegativeOn q K →
        HasLowerEllipticityOn lam B K → HasUpperEllipticityOn Lam B K →
        (∀ x ∈ K, parabolicOperator B q x = F x) →
        ∀ v : PDE.Vec d, v ∈ velocityCube (0 : PDE.Vec d) 1 →
          hBox * q (4, (0 : PDE.Vec d)) ≤
            q (8, v) + C * parabolicLpNormOn d F K := by
  obtain ⟨hBox, C, hhBox0, hhBox1, hC, hpositive⟩ :=
    exists_source_local_parabolic_harnack_positive d hd lam hlam Lam hlamLam
  refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
  intro K U B q F hK hKU hU hbox hB hq hF hnonneg hlower hupper heq v hv
  have hqClosed : ContinuousOn q (parabolicClosedBox 2 2 0 0) :=
    hq.continuousOn.mono (hbox.trans hKU)
  have hsource : (4, (0 : PDE.Vec d)) ∈ parabolicClosedBox 2 2 0 0 := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro i
    norm_num
  apply le_of_forall_pos_le_add
  intro eps heps
  have hstrictEps : 0 < q (4, (0 : PDE.Vec d)) + eps :=
    add_pos_of_nonneg_of_pos (hnonneg _ (hbox hsource)) heps
  have hlimitEps : hBox * (q (4, (0 : PDE.Vec d)) + eps) ≤
      q (8, v) + eps + C * parabolicLpNormOn d F K := by
    exact le_of_tendsto_of_tendsto'
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => hBox * (q (4, (0 : PDE.Vec d)) + eps)) atTop
        (_root_.nhds (hBox * (q (4, (0 : PDE.Vec d)) + eps))))
      (((ContinuousOn.tendsto_localHarnackTerminalApprox hqClosed hv).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => eps) atTop (_root_.nhds eps))).add
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => C * parabolicLpNormOn d F K) atTop
          (_root_.nhds (C * parabolicLpNormOn d F K))))
      (fun j => hpositive K U B (fun z => q z + eps) F hK hKU hU hbox hB
        (hq.add contDiffOn_const) hF
        (fun z hz => add_nonneg (hnonneg z hz) heps.le) hlower hupper
        (fun z hz => by rw [parabolicOperator_add_const, heq z hz]) hstrictEps j v hv)
  calc
    hBox * q (4, (0 : PDE.Vec d)) ≤ hBox * (q (4, (0 : PDE.Vec d)) + eps) := by
      gcongr
      linarith
    _ ≤ q (8, v) + C * parabolicLpNormOn d F K + eps := by
      linarith

end

end HypoellipticAleksandrov.Parabolic
