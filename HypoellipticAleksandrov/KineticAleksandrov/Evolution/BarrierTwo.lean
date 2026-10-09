module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierChain
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound

/-!
# (A.1): the lateral and terminal barriers

For a viscous classical terminal solution `u_ε` on the moving ball `B_{r₀}` with smooth
compactly supported terminal datum `F`:

* `|u_ε| ≤ ‖F‖ min {1, w(d)/w(d_*)}`, where `d = r₀ - |y - γ(σ) - c|` is the distance to the
  lateral boundary;
* `|u_ε - F| ≤ (τ - σ) M_F` for `τ - σ ≤ d_*/(1 + L_γ)`.

The proof compares `u_ε` with the constant `‖F‖`, the collar supersolution
`‖F‖ w(d)/w(d_*)` (on each smooth piece of `γ`, `collar_chain`), and the terminal barriers
`F ± (τ - σ) M_F`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology MatrixOrder

/-- In the collar, the terminal datum vanishes (the support of `F` is at distance at least
`2 d_*` from the terminal boundary). -/
theorem terminalDatum_eq_zero_of_collar {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * dstar ≤ r₀ - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    {p : KineticPoint n} (hpt : p.time = τ) (hS : (r₀ - dstar) ^ 2 ≤ centreSq c γ p) :
    F (p.position, p.velocity) = 0 := by
  by_contra hne
  have hmem : (p.position, p.velocity) ∈ tsupport (F : EvolutionAmbientState n → ℝ) :=
    subset_tsupport _ (Function.mem_support.mpr hne)
  have h1 := hsupp _ hmem
  have h2 : r₀ - dstar ≤ PDE.vecEuclideanNorm (p.position - (γ τ + c)) := by
    unfold PDE.vecEuclideanNorm
    have h3 : (r₀ - dstar) ^ 2 ≤ PDE.vecNormSq (p.position - (γ τ + c)) := by
      rw [← hpt]
      exact hS
    calc r₀ - dstar = Real.sqrt ((r₀ - dstar) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h3
  simp only at h1
  linarith

/-- The profile `w` is strictly increasing. -/
theorem barrierW_strictMono {κ : ℝ} (hκ : 0 < κ) {s t : ℝ} (h : s < t) :
    barrierW κ s < barrierW κ t := by
  unfold barrierW
  have : Real.exp (-κ * t) < Real.exp (-κ * s) := Real.exp_lt_exp.mpr (by nlinarith)
  exact div_lt_div_of_pos_right (by linarith) hκ

/-- Order reflection for the profile `w`. -/
theorem le_of_barrierW_le {κ : ℝ} (hκ : 0 < κ) {s t : ℝ} (h : barrierW κ s ≤ barrierW κ t) :
    s ≤ t := by
  by_contra hst
  exact absurd (barrierW_strictMono hκ (not_le.mp hst)) (not_lt.mpr h)

/-- Lateral barrier for a viscous classical solution, in the collar. -/
theorem classical_le_collarSupersolution {n : ℕ} {c : PDE.Vec n} {r₀ dstar : ℝ} (hd : 0 < dstar)
    (hdr : dstar < r₀) {γ : ℝ → PDE.Vec n} (hγpw : IsContinuousPiecewiseC1 γ) {Lγ : ℝ}
    (hLγ : 0 ≤ Lγ) (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r₀) γ B b ε τ F u)
    {FB : ℝ} (hFB : 0 ≤ FB)
    (hle : ∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ, u p ≤ FB)
    (hterm0 : ∀ p ∈ evolutionTerminalClosure (PDE.euclideanBall c r₀) γ τ,
      (r₀ - dstar) ^ 2 ≤ centreSq c γ p → u p ≤ 0) :
    ∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      (r₀ - dstar) ^ 2 ≤ centreSq c γ p → u p ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
  have hΩo : IsOpen (PDE.euclideanBall c r₀) := PDE.isOpen_euclideanBall c r₀
  have hγ : Continuous γ := hγpw.1
  have hκ : 0 < collarKappa Lγ lam := div_pos (by linarith) hlam
  have hc0 : 0 ≤ FB / barrierW (collarKappa Lγ lam) dstar :=
    div_nonneg hFB (barrierW_pos hκ hd).le
  have hr₀ : 0 ≤ r₀ := by linarith
  intro p₀ hp₀ hS₀
  have hGnn : ∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      0 ≤ collarSupersolution c r₀ dstar Lγ lam FB γ p := by
    intro p hp
    exact mul_nonneg hc0 (collarBarrier_nonneg hκ hr₀
      (vecNormSq_le_of_mem_closure_movingDomain hp.2))
  by_cases hτ : p₀.time = τ
  · have := hterm0 p₀ ⟨hτ, hτ ▸ hp₀.2⟩ hS₀
    have := hGnn p₀ hp₀
    linarith
  have hlt : p₀.time < τ := lt_of_le_of_ne hp₀.1 hτ
  have hslab : movingClosedSlab (PDE.euclideanBall c r₀) γ p₀.time τ ⊆
      evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ :=
    fun p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : movingActiveSlab (PDE.euclideanBall c r₀) γ p₀.time τ ⊆
      evolutionPastOpenCylinder (PDE.euclideanBall c r₀) γ τ :=
    fun p hp => ⟨hp.2.1, hp.2.2⟩
  obtain ⟨C₁, -, hC₁⟩ := hu.1
  have hchain := collar_chain (v := u) hd hdr hγpw hLγ hγL hlt hlam hB hb hε0 hε1 hFB
    ⟨C₁, fun p hp => (le_abs_self _).trans (hC₁ p (hslab hp))⟩
    (hu.2.1.mono hslab)
    (fun p hp => hu.isSliceRegularAt hΩo hγ (hact hp))
    (fun p hp => by rw [hu.2.2.2.1 p (hact hp)])
    (fun p hp hfr => by
      rw [hu.2.2.2.2.2 p ⟨hp.2.1, hfr⟩])
    (fun p hp => hle p (hslab hp))
    (fun p hp hpt => by
      have h1 := hterm0 p ⟨hpt, hpt ▸ hp.1.2.2⟩ hp.2
      have h2 := hGnn p ⟨hpt.le, hp.1.2.2⟩
      linarith)
  exact hchain p₀ ⟨⟨le_rfl, hp₀.1, hp₀.2⟩, hS₀⟩

/-- The `σ`-independent extension `F(y, z)` of a smooth terminal datum is slice regular. -/
theorem isSliceRegularAt_terminalDatum {n : ℕ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (p : KineticPoint n) :
    IsSliceRegularAt (fun q : KineticPoint n => F (q.position, q.velocity)) p := by
  have h2 : ContDiff ℝ 2 (F : EvolutionAmbientState n → ℝ) :=
    hF.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  refine ⟨?_, ?_, ?_⟩
  · exact differentiableAt_const (F (p.position, p.velocity))
  · have : ContDiff ℝ 2 (fun y : PDE.Vec n => F (y, p.velocity)) :=
      h2.comp (contDiff_id.prodMk contDiff_const)
    exact this.contDiffAt
  · have : ContDiff ℝ 2 (fun z : PDE.Vec n => F (p.position, z)) :=
      h2.comp (contDiff_const.prodMk contDiff_id)
    exact this.contDiffAt

/-- Terminal barrier core: if the terminal datum vanishes on the lateral frontier of the slab
`[a, τ]`, then `|u - F| ≤ (τ - σ) M` there. -/
theorem classical_sub_terminalDatum_le_core {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {FB M : ℝ} (hFB : ∀ q, |F q| ≤ FB)
    (hM : ∀ p : KineticPoint n, p.time ≤ τ →
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ} (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) {a : ℝ}
    (hlatF : ∀ p ∈ movingClosedSlab Ω γ a τ,
      p.position ∈ frontier (movingDomain Ω γ p.time) → F (p.position, p.velocity) = 0) :
    ∀ p ∈ movingClosedSlab Ω γ a τ, |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨τ, 0, 0⟩ le_rfl)
  obtain ⟨C₁, -, hC₁⟩ := hu.1
  have hFcont : Continuous (fun q : KineticPoint n => F (q.position, q.velocity)) :=
    hF.continuous.comp (continuous_position.prodMk continuous_velocity)
  have hslab : ∀ a, movingClosedSlab Ω γ a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω γ a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  intro p₀ hp₀
  have side : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      s * (u p₀ - F (p₀.position, p₀.velocity)) + M * (p₀.time - τ) ≤ 0 := by
    intro s hs
    have hres := growth_comparison (a := a) (T := τ)
      (u := fun q => s * (u q - F (q.position, q.velocity)) + M * (q.time - τ))
      hΩ hγ hlam hB hb hε0 hε1 ?_ ?_ ?_ ?_ ?_ ?_ p₀ hp₀
    · exact hres
    · refine ⟨C₁ + FB, fun p hp => ?_⟩
      have h1 := hC₁ p (hslab _ hp)
      have h2 := hFB (p.position, p.velocity)
      have h3 : M * (p.time - τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0 (by linarith [hp.2.1])
      have h4 := abs_le.mp h1
      have h5 := abs_le.mp h2
      show s * (u p - F (p.position, p.velocity)) + M * (p.time - τ) ≤ C₁ + FB
      rcases hs with rfl | rfl <;> nlinarith [h4.1, h4.2, h5.1, h5.2]
    · exact (((hu.2.1.mono (hslab _)).sub hFcont.continuousOn).const_smul s).add
        ((continuous_const.mul (continuous_time.sub continuous_const)).continuousOn)
    · intro p hp
      have hr := hu.isSliceRegularAt hΩ hγ (hact _ hp)
      exact (((hr.sub (isSliceRegularAt_terminalDatum hF p)).const_mul s).add
        ((isSliceRegularAt_time_sub τ p).const_mul M))
    · intro p hp
      have hr := hu.isSliceRegularAt hΩ hγ (hact _ hp)
      have hF' := isSliceRegularAt_terminalDatum hF p
      have hT := isSliceRegularAt_time_sub (n := n) τ p
      have e1 : viscousTransportedOperator B b ε
          (fun q => s * (u q - F (q.position, q.velocity)) + M * (q.time - τ)) p =
          viscousTransportedOperator B b ε (fun q => s * (u q - F (q.position, q.velocity))) p +
          viscousTransportedOperator B b ε (fun q => M * (q.time - τ)) p :=
        viscousTransportedOperator_add (u := fun q => s * (u q - F (q.position, q.velocity)))
          (v := fun q => M * (q.time - τ)) ((hr.sub hF').const_mul s) (hT.const_mul M)
      have e2 : viscousTransportedOperator B b ε
          (fun q => s * (u q - F (q.position, q.velocity))) p =
          s * viscousTransportedOperator B b ε (fun q => u q - F (q.position, q.velocity)) p :=
        viscousTransportedOperator_const_mul s (hr.sub hF')
      have e3 := viscousTransportedOperator_sub (B := B) (b := b) (ε := ε) hr hF'
      have e4 : viscousTransportedOperator B b ε (fun q => M * (q.time - τ)) p = M :=
        by
          rw [viscousTransportedOperator_const_mul M hT, viscousTransportedOperator_time_sub]
          ring
      have hop := hu.2.2.2.1 p (hact _ hp)
      have hMp := abs_le.mp (hM p hp.2.1.le)
      rw [e1, e2, e3, e4, hop]
      rcases hs with rfl | rfl <;> nlinarith [hMp.1, hMp.2]
    · intro p hp hpT
      have hterm : p ∈ evolutionTerminalClosure (Ω) γ τ :=
        ⟨hpT, hpT ▸ hp.2.2⟩
      have e1 := hu.2.2.2.2.1 p hterm
      show s * (u p - F (p.position, p.velocity)) + M * (p.time - τ) ≤ 0
      rw [e1, hpT]
      simp
    · intro p hp hfr
      have hlat : p ∈ evolutionLateralFrontier (Ω) γ τ := ⟨hp.2.1, hfr⟩
      show s * (u p - F (p.position, p.velocity)) + M * (p.time - τ) ≤ 0
      rw [hu.2.2.2.2.2 p hlat, hlatF p hp hfr]
      have : M * (p.time - τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0 (by linarith [hp.2.1])
      simpa using this
  have h1 := side 1 (Or.inl rfl)
  have h2 := side (-1) (Or.inr rfl)
  rw [abs_le]
  constructor <;> nlinarith [h1, h2]


/-- Terminal barrier: `|u - F| ≤ (τ - σ) M` for `τ - σ ≤ d_*/(1 + L_γ)`. -/
theorem classical_sub_terminalDatum_le {n : ℕ} {c : PDE.Vec n} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {Lγ : ℝ} (hLγ : 0 ≤ Lγ)
    (hγL : ∀ s t, PDE.vecEuclideanNorm (γ s - γ t) ≤ Lγ * |s - t|)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r₀) γ τ F)
    {dstar : ℝ} (hd : 0 < dstar)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * dstar ≤ r₀ - PDE.vecEuclideanNorm (q.1 - (γ τ + c)))
    {FB M : ℝ} (hFB : ∀ q, |F q| ≤ FB)
    (hM : ∀ p : KineticPoint n, p.time ≤ τ →
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution (PDE.euclideanBall c r₀) γ B b ε τ F u) :
    ∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r₀) γ τ,
      τ - dstar / (1 + Lγ) ≤ p.time →
        |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  have hΩo : IsOpen (PDE.euclideanBall c r₀) := PDE.isOpen_euclideanBall c r₀
  have hL1 : 0 < 1 + Lγ := by linarith
  -- the terminal datum vanishes on the lateral frontier near the terminal time
  have hFzero : ∀ p : KineticPoint n, τ - dstar / (1 + Lγ) ≤ p.time → p.time ≤ τ →
      p.position ∈ frontier (movingDomain (PDE.euclideanBall c r₀) γ p.time) →
        F (p.position, p.velocity) = 0 := by
    intro p h1 h2 hfr
    by_contra hne
    have hmem : (p.position, p.velocity) ∈ tsupport (F : EvolutionAmbientState n → ℝ) :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have h3 := hsupp _ hmem
    simp only at h3
    have hS := vecNormSq_eq_of_mem_frontier_movingDomain hfr
    have hnorm : PDE.vecEuclideanNorm (p.position - (γ p.time + c)) = r₀ := by
      unfold PDE.vecEuclideanNorm
      rw [hS, Real.sqrt_sq hr₀.le]
    have htri : p.position - (γ p.time + c) =
        (p.position - (γ τ + c)) + (γ τ - γ p.time) := by abel
    have h4 := PDE.vecEuclideanNorm_add_le (p.position - (γ τ + c)) (γ τ - γ p.time)
    rw [← htri, hnorm] at h4
    have h5 := hγL τ p.time
    have h6 : |τ - p.time| = τ - p.time := abs_of_nonneg (by linarith)
    rw [h6] at h5
    have h7 : Lγ * (τ - p.time) ≤ Lγ * (dstar / (1 + Lγ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hLγ
    have h8 : Lγ * (dstar / (1 + Lγ)) < dstar := by
      rw [← mul_div_assoc, div_lt_iff₀ hL1]
      nlinarith
    linarith
  intro p₀ hp₀ hδ
  exact classical_sub_terminalDatum_le_core hΩo hγ hlam hB hb hε0 hε1 hF.1 hFB hM hu
    (a := τ - dstar / (1 + Lγ)) (fun p hp hfr => hFzero p hp.1 hp.2.1 hfr) p₀ ⟨hδ, hp₀.1, hp₀.2⟩

/-- Terminal barrier for the whole space: there is no lateral boundary, and
`|u - F| ≤ (τ - σ) M` holds throughout the interval. -/
theorem classical_sub_terminalDatum_le_univ {n : ℕ} {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum (Set.univ : Set (PDE.Vec n)) γ τ F)
    {FB M : ℝ} (hFB : ∀ q, |F q| ≤ FB)
    (hM : ∀ p : KineticPoint n, p.time ≤ τ →
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M)
    {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousTerminalSolution Set.univ γ B b ε τ F u) :
    ∀ p ∈ evolutionPastClosedCylinder (Set.univ : Set (PDE.Vec n)) γ τ,
      |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  intro p hp
  have hfr : ∀ q : KineticPoint n,
      q.position ∉ frontier (movingDomain (Set.univ : Set (PDE.Vec n)) γ q.time) := by
    intro q
    have : movingDomain (Set.univ : Set (PDE.Vec n)) γ q.time = Set.univ := by
      ext y
      simp [mem_movingDomain_iff]
    rw [this, frontier_univ]
    exact notMem_empty _
  exact classical_sub_terminalDatum_le_core isOpen_univ hγ hlam hB hb hε0 hε1 hF.1 hFB hM hu
    (a := p.time) (fun q _ hq => absurd hq (hfr q)) p ⟨le_rfl, hp.1, hp.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
