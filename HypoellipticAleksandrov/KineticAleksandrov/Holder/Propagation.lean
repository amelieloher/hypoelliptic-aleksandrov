module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationExplicit
import Mathlib.Tactic

/-! # Propagation along C-one-one skeletons with uniform source constants -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source propagation constant is uniform over coefficients, domains and skeletons. -/
theorem propagation (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (H kx kv T0 T1 : ℝ) (hH : 0 < H) (hkx : 0 < kx)
    (hkv : 0 < kv) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) :
  ∃ cprop : ℝ, 0 < cprop ∧ cprop ≤ 1 ∧
    ∀ (p C_A : ℝ), 1 ≤ p →
    ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
    ∀ O : Set (KineticPoint d), IsOpen O →
    ∀ (tminus : ℝ) (P : KineticPoint d), P ∈ O →
      T0 ≤ P.time-tminus → P.time-tminus ≤ T1 →
    ∀ x v : ℝ → PDE.Vec d,
      IsSkeleton x v H (-T0) (P.time-tminus) →
      x (P.time-tminus) = P.position → v (P.time-tminus) = P.velocity →
      corridor tminus (-T0) (P.time-tminus) kx kv x v ⊆ O →
    ∀ ell : ℝ, 0 ≤ ell →
    ∀ u : KineticPoint d → ℝ,
      (∀ Q ∈ O, 0 ≤ u Q) → IsAdmissibleSupersolution A O p C_A u →
      (∀ Q ∈ corridor tminus (-T0) (P.time-tminus) kx kv x v,
        Q.time ≤ tminus → ell ≤ u Q) → cprop*ell ≤ u P := by
  let L := barrierL d lam Lam H T1
  let hs := stepSize d lam Lam H T0 T1 kx kv
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hg := barrierGamma_bounds hL
  refine ⟨(barrierGamma L) ^ Nat.ceil (T1 / hs), pow_pos hg.1 _,
    pow_le_one₀ hg.1.le hg.2.le, ?_⟩
  intro p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v hsk hxP hvP htube
    ell hell u hnonneg hu hinitial
  exact propagation_explicit d hd lam Lam H T0 T1 kx kv hlam hLam hH hkx hkv hT0 hT1
    p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v hsk hxP hvP htube
    ell hell u hnonneg hu hinitial

end HypoellipticAleksandrov.KineticAleksandrov.Holder
