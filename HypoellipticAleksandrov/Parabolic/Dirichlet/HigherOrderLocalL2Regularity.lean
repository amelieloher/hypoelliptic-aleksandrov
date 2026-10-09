module

public import HypoellipticAleksandrov.Parabolic.HigherOrderSourceWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.HigherOrderNestedProductBoxChain
public import HypoellipticAleksandrov.Parabolic.GenericPreLiftWeakDerivativeFamilyIteration
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamilyEquation

/-!
# Higher-order local L2 regularity

This module assembles the finite interior weak-derivative bootstrap from a
local strong jet, and then connects it to the original-time variational
solution and its globally selected value representative.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set MeasureTheory
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise

private theorem closure_outerBox_subset_closedCylinder
    {d : ℕ} {Ω O₀ : Set (PDE.Vec d)} {r₀ q₀ q₁ r₁ : ℝ}
    (hr₀q₀ : r₀ < q₀) (hq₀q₁ : q₀ < q₁) (hq₁r₁ : q₁ < r₁)
    (hO₀Ω : closure O₀ ⊆ Ω) :
    closure (Set.Ioo q₀ q₁ ×ˢ O₀) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
  rw [closure_prod_eq, closure_Ioo hq₀q₁.ne]
  rintro z ⟨hz, hy⟩
  exact ⟨⟨hr₀q₀.le.trans hz.1, hz.2.trans hq₁r₁.le⟩, subset_closure (hO₀Ω hy)⟩

private theorem outerBox_closure_compact
    {d : ℕ} {O₀ : Set (PDE.Vec d)} {q₀ q₁ : ℝ}
    (hq₀q₁ : q₀ < q₁) (hO₀compact : IsCompact (closure O₀)) :
    IsCompact (closure (Set.Ioo q₀ q₁ ×ˢ O₀)) := by
  rw [closure_prod_eq, closure_Ioo hq₀q₁.ne]
  exact isCompact_Icc.prod hO₀compact

private theorem smooth_matrix_entry
    {d M : ℕ} {K Q : Set (TimeVelocity d)}
    {a : CoefficientField d}
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) K)
    (hQK : Q ⊆ K) (i j : Fin d) :
    ContDiffOn ℝ M (fun z : TimeVelocity d => a z.1 z.2 i j) Q := by
  obtain ⟨U, hUopen, hKU, haU⟩ := ha
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i) U :=
    (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp haU (fun _ _ => Set.mem_univ _)
  have hij : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => a z.1 z.2 i j) U :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hi (fun _ _ => Set.mem_univ _)
  exact (hij.of_le (by exact_mod_cast le_top)).mono (hQK.trans hKU)

private theorem smooth_vector_entry
    {d M : ℕ} {K Q : Set (TimeVelocity d)}
    {b : ℝ → PDE.Vec d → PDE.Vec d}
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) K)
    (hQK : Q ⊆ K) (j : Fin d) :
    ContDiffOn ℝ M (fun z : TimeVelocity d => b z.1 z.2 j) Q := by
  obtain ⟨U, hUopen, hKU, hbU⟩ := hb
  have hj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2 j) U :=
    (contDiffOn_apply ℝ ℝ j Set.univ).comp hbU (fun _ _ => Set.mem_univ _)
  exact (hj.of_le (by exact_mod_cast le_top)).mono (hQK.trans hKU)

private theorem smooth_scalar
    {d M : ℕ} {K Q : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ}
    (hf : IsSmoothOnNeighborhood f K) (hQK : Q ⊆ K) :
    ContDiffOn ℝ M f Q := by
  obtain ⟨U, _, hKU, hfU⟩ := hf
  exact (hfU.of_le (by exact_mod_cast le_top)).mono (hQK.trans hKU)

private theorem chain_left_le_right_le_spatial_subset_zero
    {d N : ℕ} {q₀ s₀ s₁ q₁ : ℝ} {Ω O₀ O : Set (PDE.Vec d)}
    {left right : ℕ → ℝ} {spatial : ℕ → Set (PDE.Vec d)}
    (h : IsHigherOrderNestedProductBoxChain
      d N q₀ s₀ s₁ q₁ Ω O₀ O left right spatial)
    {k : ℕ} (hk : k ≤ N + 2) :
    left 0 ≤ left k ∧ right k ≤ right 0 ∧ spatial k ⊆ spatial 0 := by
  induction k with
  | zero => exact ⟨le_rfl, le_rfl, Subset.rfl⟩
  | succ k ih =>
      rcases ih (Nat.le_trans (Nat.le_succ k) hk) with ⟨hl, hr, hs⟩
      rcases h.step (Nat.lt_of_succ_le hk) with
        ⟨hlstep, _, hrstep, _, _, _, _, hspstep⟩
      exact ⟨hl.trans hlstep.le, hrstep.le.trans hr,
        (subset_closure.trans hspstep).trans hs⟩

/-- A supplied local weight-two strong jet bootstraps to the finite
higher-order weak-derivative family on a larger box around the target. -/
theorem exists_higherOrderLocalL2WeakDerivativeFamily_of_strongJet
    {d : ℕ} {Ω O₀ O : Set (PDE.Vec d)}
    (r₀ q₀ s₀ s₁ q₁ r₁ : ℝ)
    (hr₀q₀ : r₀ < q₀) (hq₀s₀ : q₀ < s₀) (hs₀s₁ : s₀ < s₁)
    (hs₁q₁ : s₁ < q₁) (hq₁r₁ : q₁ < r₁)
    (hΩopen : IsOpen Ω) (hO₀open : IsOpen O₀)
    (hO₀compact : IsCompact (closure O₀)) (hO₀Ω : closure O₀ ⊆ Ω)
    (hOopen : IsOpen O) (hOne : O.Nonempty)
    (hOcompact : IsCompact (closure O)) (hOO₀ : closure O ⊆ O₀)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)) :
    ∃ Citer : ℝ, 0 ≤ Citer ∧
      ∀ (F : ℝ → PDE.Vec d → ℝ)
        (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
          (scalarParabolicClosedCylinder r₀ r₁ Ω))
        (J : ParabolicW12Function d (Set.Ioo q₀ q₁ ×ˢ O₀) (2 : ℝ≥0∞)),
        (∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀),
          J.timeDeriv z + (∑ i : Fin d, ∑ j : Fin d,
            a z.1 z.2 i j * J.velocityHessian z j i) +
          (∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j) +
          c z.1 z.2 * J.toFun z = F z.1 z.2) →
        ∃ (coreLeft coreRight : ℝ) (Ocore : Set (PDE.Vec d))
          (B : ParabolicDerivativeIndex d (2 * d + 6) → ℝ)
          (Emax : ParabolicWeakDerivativeFamily d (2 * d + 6)
            (Set.Ioo q₀ q₁ ×ˢ O₀) (fun z : TimeVelocity d => F z.1 z.2))
          (Dcore : ParabolicWeakDerivativeFamily d (2 * d + 8)
            (Set.Ioo coreLeft coreRight ×ˢ Ocore) J.toFun),
          q₀ < coreLeft ∧ coreLeft < s₀ ∧ s₁ < coreRight ∧ coreRight < q₁ ∧
          IsOpen Ocore ∧ Ocore.Nonempty ∧ IsCompact (closure Ocore) ∧
          closure O ⊆ Ocore ∧ closure Ocore ⊆ O₀ ∧
          (∀ beta, 0 ≤ B beta) ∧
          (∀ beta z, z ∈ closure (Set.Ioo q₀ q₁ ×ˢ O₀) →
            |TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
              (fun x : TimeVelocity d => F x.1 x.2) z| ≤ B beta) ∧
          (∀ beta, Emax.representative beta =
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
              (fun x : TimeVelocity d => F x.1 x.2)) ∧
          ParabolicWeakDerivativeFamily.squaredL2Norm Emax ≤
            volume.real (Set.Ioo q₀ q₁ ×ˢ O₀) *
              ∑ beta : ParabolicDerivativeIndex d (2 * d + 6), (B beta) ^ 2 ∧
          (∀ alpha : ParabolicDerivativeIndex d 2,
            Dcore.representative (ParabolicDerivativeIndex.castLE
              (by omega : 2 ≤ 2 * d + 8) alpha) =
            (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)).representative alpha) ∧
          ParabolicWeakDerivativeFamily.squaredL2Norm Dcore ≤ Citer *
            (ParabolicWeakDerivativeFamily.squaredL2Norm
              (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)) +
             ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
  classical
  let N := 2 * d + 6
  let Q := Set.Ioo q₀ q₁ ×ˢ O₀
  have hq₀q₁ : q₀ < q₁ := hq₀s₀.trans (hs₀s₁.trans hs₁q₁)
  have hQcompact : IsCompact (closure Q) := outerBox_closure_compact hq₀q₁ hO₀compact
  have hQK : closure Q ⊆ scalarParabolicClosedCylinder r₀ r₁ Ω :=
    closure_outerBox_subset_closedCylinder hr₀q₀ hq₀q₁ hq₁r₁ hO₀Ω
  obtain ⟨left, right, spatial, hchain⟩ :=
    exists_higherOrderNestedProductBoxChain d N q₀ s₀ s₁ q₁ Ω O₀ O
      hq₀s₀ hs₀s₁ hs₁q₁ hO₀open hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀
  have hchainData := hchain
  rcases hchainData with ⟨hl0, hr0, hs0, hle, hre, hse, hboxes, hsteps⟩
  subst q₀
  subst q₁
  subst O₀
  obtain ⟨Ua, hUa, hKa, haUa⟩ := haSmooth
  obtain ⟨Ub, hUb, hKb, hbUb⟩ := hbSmooth
  obtain ⟨Uc, hUc, hKc, hcUc⟩ := hcSmooth
  let U := Ua ∩ Ub ∩ Uc
  have hU : IsOpen U := (hUa.inter hUb).inter hUc
  have hKU : closure Q ⊆ U := fun z hz =>
    ⟨⟨hKa (hQK hz), hKb (hQK hz)⟩, hKc (hQK hz)⟩
  have ha : ∀ i j, ContDiffOn ℝ (N + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U := by
    intro i j
    have hi := (contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp haUa
      (fun _ _ => Set.mem_univ _)
    have hij := (contDiffOn_apply ℝ ℝ j Set.univ).comp hi
      (fun _ _ => Set.mem_univ _)
    exact (hij.of_le (by exact_mod_cast le_top)).mono (inter_subset_left.trans inter_subset_left)
  have hb : ∀ j, ContDiffOn ℝ N
      (fun z : TimeVelocity d => b z.1 z.2 j) U := by
    intro j
    have hj := (contDiffOn_apply ℝ ℝ j Set.univ).comp hbUb
      (fun _ _ => Set.mem_univ _)
    exact (hj.of_le (by exact_mod_cast le_top)).mono (inter_subset_left.trans inter_subset_right)
  have hc : ContDiffOn ℝ N (fun z : TimeVelocity d => c z.1 z.2) U :=
    (hcUc.of_le (by exact_mod_cast le_top)).mono inter_subset_right
  obtain ⟨V, Ba, Bb, Bc, _, hQV, _, _, hBa0, hBb0, hBc0, hBa, hBb, hBc⟩ :=
    GenericPreLiftDifferentiatedWeakEquationSupport.exists_precompactOpen_coefficient_majorants
      hU hQcompact hKU a b c ha hb hc
  obtain ⟨Citer, hCiter, hrun⟩ :=
    exists_iterated_genericPrelift_weakDerivativeFamily_estimate d N (by simp [N])
      (left 0) s₀ s₁ (right 0) Ω (spatial 0) O left right spatial hchain
      lam Lam hlam hlamLam
      Ba Bb Bc hBa0 hBb0 hBc0
  refine ⟨Citer, hCiter, ?_⟩
  intro F hFSmooth J hEq
  obtain ⟨B, Emax, hB0, hB, hErep, hEnorm⟩ :=
    exists_higherOrderSourceWeakDerivativeFamily d
      (scalarParabolicClosedCylinder r₀ r₁ Ω) Q F
      (isOpen_Ioo.prod hO₀open) hQcompact hQK hFSmooth
  have hEll : ∀ z ∈ Set.Ioo (left 0) (right 0) ×ˢ spatial 0,
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2 ∧ a z.1 z.2 ≤ Lam • (1 : PDE.Mat d) := by
    intro z hz
    exact ⟨hLower z (subset_closure.trans hQK hz),
      hUpper z (subset_closure.trans hQK hz)⟩
  have hBaQ : ∀ i j alpha z, z ∈ Set.Ioo (left 0) (right 0) ×ˢ spatial 0 →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => a x.1 x.2 i j) z| ≤ Ba i j alpha := by
    intro i j alpha z hz
    apply hBa i j alpha z
    exact subset_closure (hQV (subset_closure hz))
  have hBbQ : ∀ j alpha z, z ∈ Set.Ioo (left 0) (right 0) ×ˢ spatial 0 →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => b x.1 x.2 j) z| ≤ Bb j alpha := by
    intro j alpha z hz
    apply hBb j alpha z
    exact subset_closure (hQV (subset_closure hz))
  have hBcQ : ∀ alpha z, z ∈ Set.Ioo (left 0) (right 0) ×ˢ spatial 0 →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d => c x.1 x.2) z| ≤ Bc alpha := by
    intro alpha z hz
    apply hBc alpha z
    exact subset_closure (hQV (subset_closure hz))
  let Dseed := J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)
  let Eseed : ParabolicWeakDerivativeFamily d N
      (Set.Ioo (left 0) (right 0) ×ˢ spatial 0)
      (fun z : TimeVelocity d => F z.1 z.2) := by simpa only [N, Q] using Emax
  have hrun' := hrun a b c F J.toFun Dseed Eseed
  obtain ⟨Dcore, hDseed, hDnorm⟩ := hrun'
    hEll
    (fun i j => (ha i j).mono (subset_closure.trans hKU))
    (fun j => (hb j).mono (subset_closure.trans hKU))
    (hc.mono (subset_closure.trans hKU))
    hBaQ hBbQ hBcQ
    (by
      exact ParabolicW12Function.toWeakDerivativeFamily_originalTimeEquation
        (isOpen_Ioo.prod hO₀open) J a b c F hEq)
  rcases hsteps (N - 1) (by simp [N]) with ⟨hlN, _, hrN, hsN⟩
  rcases hboxes N (by omega) with ⟨hONopen, hONne, hONcompact, _, _⟩
  have hmonoN := chain_left_le_right_le_spatial_subset_zero hchain
    (show N ≤ N + 2 by omega)
  have hprev := chain_left_le_right_le_spatial_subset_zero hchain
    (show N - 1 ≤ N + 2 by omega)
  have hprevStep := hchain.step (show N - 1 < N + 2 by omega)
  have hNm1 : N - 1 + 1 = N := by simp [N]
  have hleft : left 0 < left N := by
    exact hprev.1.trans_lt (by simpa only [hNm1] using hprevStep.1)
  have hright : right N < right 0 := by
    have hstepRight : right N < right (N - 1) := by
      simpa only [hNm1] using hprevStep.2.2.1
    exact hstepRight.trans_le hprev.2.1
  have hleftTarget : left N < s₀ := by
    have hend := hchain.step (show N < N + 2 by omega)
    have hlastLeft : left (N + 1) < s₀ := by
      simpa only [hle] using (hchain.step (show N + 1 < N + 2 by omega)).1
    exact hend.1.trans hlastLeft
  have hrightTarget : s₁ < right N := by
    have hlastRight : s₁ < right (N + 1) := by
      simpa only [hre] using (hchain.step (show N + 1 < N + 2 by omega)).2.2.1
    exact hlastRight.trans (hchain.step (show N < N + 2 by omega)).2.2.1
  have hOtarget : closure O ⊆ spatial N := by
    have hlastSpatial : closure O ⊆ spatial (N + 1) := by
      simpa only [hse] using
        (hchain.step (show N + 1 < N + 2 by omega)).2.2.2.2.2.2.2
    exact hlastSpatial.trans
      (subset_closure.trans (hchain.step (show N < N + 2 by omega)).2.2.2.2.2.2.2)
  have hprevSpatial : closure (spatial N) ⊆ spatial (N - 1) := by
    simpa only [hNm1] using hprevStep.2.2.2.2.2.2.2
  have hONsub : closure (spatial N) ⊆ spatial 0 := hprevSpatial.trans hprev.2.2
  have hN2 : N + 2 = 2 * d + 8 := by dsimp [N]
  refine ⟨left N, right N, spatial N, B, Emax, Dcore,
    hleft, hleftTarget, hrightTarget, hright, hONopen, hONne, hONcompact,
    hOtarget, ?_, hB0, hB, hErep, hEnorm, ?_, ?_⟩
  exact hONsub
  · intro alpha
    simpa only [hN2, Dseed] using hDseed alpha
  · simpa only [Eseed, Dseed, hN2, N, Q, id_eq] using hDnorm

/-- A selected global value representative admits a compatible local
higher-order weak-derivative family. -/
theorem exists_higherOrderLocalL2WeakDerivativeFamily_of_valueRepresentative
    {d : ℕ} {Ω O₀ O : Set (PDE.Vec d)} (hd : 0 < d)
    (r₀ q₀ s₀ s₁ q₁ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hr₀q₀ : r₀ < q₀)
    (hq₀s₀ : q₀ < s₀) (hs₀s₁ : s₀ < s₁) (hs₁q₁ : s₁ < q₁) (hq₁r₁ : q₁ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hO₀open : IsOpen O₀) (hO₀ne : O₀.Nonempty)
    (hO₀compact : IsCompact (closure O₀)) (hO₀Ω : closure O₀ ⊆ Ω)
    (hOopen : IsOpen O) (hOne : O.Nonempty) (hOcompact : IsCompact (closure O))
    (hOO₀ : closure O ⊆ O₀) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      c z.1 z.2 ≤ 0) :
    ∃ Citer : ℝ, 0 ≤ Citer ∧ ∀ (F : ℝ → PDE.Vec d → ℝ)
      (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
        (scalarParabolicClosedCylinder r₀ r₁ Ω))
      (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (u : ReverseTimeL2V hΩ (r₁ - r₀))
      (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
      (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
      (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
        a b c F hFSmooth initial u g hdu) (w : TimeVelocity d → ℝ)
      (hwmem : MemLp w (2 : ℝ≥0∞) (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
      (hwslice : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (r₁ - r)) y),
      ∃ (J : ParabolicW12Function d (Set.Ioo q₀ q₁ ×ˢ O₀) (2 : ℝ≥0∞))
        (coreLeft coreRight : ℝ) (Ocore : Set (PDE.Vec d))
        (B : ParabolicDerivativeIndex d (2 * d + 6) → ℝ)
        (Emax : ParabolicWeakDerivativeFamily d (2 * d + 6) (Set.Ioo q₀ q₁ ×ˢ O₀)
          (fun z : TimeVelocity d => F z.1 z.2))
        (Dcore : ParabolicWeakDerivativeFamily d (2 * d + 8)
          (Set.Ioo coreLeft coreRight ×ˢ Ocore) J.toFun),
        J.toFun =ᵐ[timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀)] w ∧
        (∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀),
          J.timeDeriv z + (∑ i : Fin d, ∑ j : Fin d, a z.1 z.2 i j * J.velocityHessian z j i) +
            (∑ j : Fin d, b z.1 z.2 j * J.velocityGrad z j) + c z.1 z.2 * J.toFun z = F z.1 z.2) ∧
        q₀ < coreLeft ∧ coreLeft < s₀ ∧ s₁ < coreRight ∧ coreRight < q₁ ∧
        IsOpen Ocore ∧ Ocore.Nonempty ∧ IsCompact (closure Ocore) ∧
        closure O ⊆ Ocore ∧ closure Ocore ⊆ O₀ ∧ (∀ beta, 0 ≤ B beta) ∧
        (∀ beta z, z ∈ closure (Set.Ioo q₀ q₁ ×ˢ O₀) →
          |TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
            (fun x : TimeVelocity d => F x.1 x.2) z| ≤ B beta) ∧
        (∀ beta, Emax.representative beta = TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (fun x : TimeVelocity d => F x.1 x.2)) ∧
        ParabolicWeakDerivativeFamily.squaredL2Norm Emax ≤
          volume.real (Set.Ioo q₀ q₁ ×ˢ O₀) * ∑ beta, (B beta) ^ 2 ∧
        (∀ alpha : ParabolicDerivativeIndex d 2, Dcore.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ 2 * d + 8) alpha) =
          (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)).representative alpha) ∧
        ParabolicWeakDerivativeFamily.squaredL2Norm Dcore ≤ Citer *
          (ParabolicWeakDerivativeFamily.squaredL2Norm
            (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)) +
           ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
  obtain ⟨Citer, hCiter, hrun⟩ := exists_higherOrderLocalL2WeakDerivativeFamily_of_strongJet
    r₀ q₀ s₀ s₁ q₁ r₁ hr₀q₀ hq₀s₀ hs₀s₁ hs₁q₁ hq₁r₁ hΩ hO₀open
    hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀ lam Lam hlam hlamLam a b c
    haSmooth hbSmooth hcSmooth hLower hUpper
  refine ⟨Citer, hCiter, ?_⟩
  intro F hFSmooth initial u g hdu hu w hwmem hwslice
  obtain ⟨J, hJw, hEq⟩ := exists_originalTimeLocalL2StrongJet_of_valueRepresentative
    hd r₀ q₀ q₁ r₁ h₀₁ hr₀q₀ (hq₀s₀.trans (hs₀s₁.trans hs₁q₁)) hq₁r₁
    hΩ hΩbounded hO₀open hO₀ne hO₀compact hO₀Ω lam Lam hlam hlamLam a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos initial u g hdu hu
    w hwmem hwslice
  obtain ⟨coreLeft, coreRight, Ocore, B, Emax, Dcore, hrest⟩ := hrun F hFSmooth J hEq
  exact ⟨J, coreLeft, coreRight, Ocore, B, Emax, Dcore, hJw, hEq, hrest⟩

/-- A supplied variational solution has one global value representative whose
local strong jet bootstraps to the higher-order weak-derivative family. -/
theorem exists_higherOrderLocalL2WeakDerivativeFamily
    {d : ℕ} {Ω O₀ O : Set (PDE.Vec d)}
    (hd : 0 < d)
    (r₀ q₀ s₀ s₁ q₁ r₁ : ℝ)
    (h₀₁ : r₀ < r₁)
    (hr₀q₀ : r₀ < q₀)
    (hq₀s₀ : q₀ < s₀)
    (hs₀s₁ : s₀ < s₁)
    (hs₁q₁ : s₁ < q₁)
    (hq₁r₁ : q₁ < r₁)
    (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (hO₀open : IsOpen O₀)
    (hO₀ne : O₀.Nonempty)
    (hO₀compact : IsCompact (closure O₀))
    (hO₀Ω : closure O₀ ⊆ Ω)
    (hOopen : IsOpen O)
    (hOne : O.Nonempty)
    (hOcompact : IsCompact (closure O))
    (hOO₀ : closure O ⊆ O₀)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        c z.1 z.2 ≤ 0) :
    ∃ Citer : ℝ, 0 ≤ Citer ∧
      ∀ (F : ℝ → PDE.Vec d → ℝ)
        (hFSmooth : IsSmoothOnNeighborhood
          (fun z : TimeVelocity d => F z.1 z.2)
          (scalarParabolicClosedCylinder r₀ r₁ Ω))
        (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
        (u : ReverseTimeL2V hΩ (r₁ - r₀))
        (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
        (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
          (sub_pos.mpr h₀₁) u g)
        (hu : IsReverseTimeVariationalEnergySolution
          r₀ r₁ h₀₁ hΩ hΩbounded
          a b c F hFSmooth initial u g hdu),
        ∃ (w : TimeVelocity d → ℝ)
          (J : ParabolicW12Function d
            (Set.Ioo q₀ q₁ ×ˢ O₀) (2 : ℝ≥0∞))
          (coreLeft coreRight : ℝ)
          (Ocore : Set (PDE.Vec d))
          (B : ParabolicDerivativeIndex d (2 * d + 6) → ℝ)
          (Emax : ParabolicWeakDerivativeFamily d (2 * d + 6)
            (Set.Ioo q₀ q₁ ×ˢ O₀)
            (fun z : TimeVelocity d => F z.1 z.2))
          (Dcore : ParabolicWeakDerivativeFamily d (2 * d + 8)
            (Set.Ioo coreLeft coreRight ×ˢ Ocore) J.toFun),
          MemLp w (2 : ℝ≥0∞)
            (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) ∧
          (∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
            (fun y => w (r, y)) =ᵐ[PDE.volumeOn Ω]
              fun y => valueCLM hΩ (u (r₁ - r)) y) ∧
          J.toFun =ᵐ[
            timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀)] w ∧
          (∀ᵐ z ∂timeVelocityVolumeOn (Set.Ioo q₀ q₁ ×ˢ O₀),
            J.timeDeriv z +
                  (∑ i : Fin d, ∑ j : Fin d,
                    a z.1 z.2 i j * J.velocityHessian z j i) +
                (∑ j : Fin d,
                  b z.1 z.2 j * J.velocityGrad z j) +
              c z.1 z.2 * J.toFun z = F z.1 z.2) ∧
          q₀ < coreLeft ∧ coreLeft < s₀ ∧
          s₁ < coreRight ∧ coreRight < q₁ ∧
          IsOpen Ocore ∧ Ocore.Nonempty ∧
          IsCompact (closure Ocore) ∧
          closure O ⊆ Ocore ∧ closure Ocore ⊆ O₀ ∧
          (∀ beta, 0 ≤ B beta) ∧
          (∀ beta z,
            z ∈ closure (Set.Ioo q₀ q₁ ×ˢ O₀) →
            |TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
              (fun x : TimeVelocity d => F x.1 x.2) z| ≤ B beta) ∧
          (∀ beta, Emax.representative beta =
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
              (fun x : TimeVelocity d => F x.1 x.2)) ∧
          ParabolicWeakDerivativeFamily.squaredL2Norm Emax ≤
            volume.real (Set.Ioo q₀ q₁ ×ˢ O₀) *
              ∑ beta : ParabolicDerivativeIndex d (2 * d + 6),
                (B beta) ^ 2 ∧
          (∀ alpha : ParabolicDerivativeIndex d 2,
            Dcore.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ 2 * d + 8) alpha) =
              (J.toWeakDerivativeFamily
                (isOpen_Ioo.prod hO₀open)).representative alpha) ∧
          ParabolicWeakDerivativeFamily.squaredL2Norm Dcore ≤
            Citer *
              (ParabolicWeakDerivativeFamily.squaredL2Norm
                  (J.toWeakDerivativeFamily
                    (isOpen_Ioo.prod hO₀open)) +
                ParabolicWeakDerivativeFamily.squaredL2Norm Emax) := by
  obtain ⟨Citer, hCiter, hrun⟩ :=
    exists_higherOrderLocalL2WeakDerivativeFamily_of_valueRepresentative
      hd r₀ q₀ s₀ s₁ q₁ r₁ h₀₁ hr₀q₀ hq₀s₀ hs₀s₁ hs₁q₁ hq₁r₁
      hΩ hΩbounded hO₀open hO₀ne hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀
      lam Lam hlam hlamLam a b c haSmooth hbSmooth hcSmooth hLower hUpper hcNonpos
  refine ⟨Citer, hCiter, ?_⟩
  intro F hFSmooth initial u g hdu hu
  obtain ⟨w, hwmem, hwslice, _⟩ :=
    exists_originalTimeValueRepresentative_localL2StrongJets
      hd r₀ r₁ h₀₁ hΩ hΩbounded lam Lam hlam hlamLam a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos
      initial u g hdu hu
  obtain ⟨J, coreLeft, coreRight, Ocore, B, Emax, Dcore, hrest⟩ :=
    hrun F hFSmooth initial u g hdu hu w hwmem hwslice
  exact ⟨w, J, coreLeft, coreRight, Ocore, B, Emax, Dcore,
    hwmem, hwslice, hrest⟩


end HypoellipticAleksandrov.Parabolic.Dirichlet
