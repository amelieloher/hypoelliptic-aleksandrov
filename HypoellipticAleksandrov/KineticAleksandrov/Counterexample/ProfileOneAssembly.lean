module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeakExtension
import Mathlib.Tactic.Linarith

/-! # Scalar branch assembly into the shared profile interface -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped MatrixOrder

/-- Scalar multiples of the identity preserve the scalar order. -/
theorem scalar_identity_le {d : ℕ} (a b : ℝ) (hab : a ≤ b) :
    a • (1 : PDE.Mat d) ≤ b • (1 : PDE.Mat d) := by
  apply Matrix.le_iff.mpr
  simpa only [sub_smul] using
    (Matrix.PosSemidef.one (n := Fin d) (R := ℝ)).smul (sub_nonneg.mpr hab)

/-- The literal scalar coefficient is entrywise measurable. -/
theorem measurable_scalarProfileCoefficient (Lam : ℝ) (i k : Fin 1) :
    Measurable (fun q => scalarProfileCoefficient Lam q i k) := by
  have hm : Measurable (fun q : XV 1 => q.1 0 * q.2 0) :=
    ((measurable_pi_apply 0).comp measurable_fst).mul
      ((measurable_pi_apply 0).comp measurable_snd)
  have hs : MeasurableSet {q : XV 1 | q.1 0 * q.2 0 < 0} :=
    measurableSet_lt hm measurable_const
  exact (measurable_const.ite hs measurable_const).mul measurable_const

/-- The scalar coefficient has the source's uniform ellipticity bounds everywhere. -/
theorem scalarProfileCoefficient_order (Lam : ℝ) (hLam : 1 < Lam) (q : XV 1) :
    (1 : ℝ) • (1 : PDE.Mat 1) ≤ scalarProfileCoefficient Lam q ∧
      scalarProfileCoefficient Lam q ≤ Lam • (1 : PDE.Mat 1) := by
  unfold scalarProfileCoefficient
  split_ifs
  · exact ⟨scalar_identity_le 1 Lam hLam.le, le_refl _⟩
  · exact ⟨le_refl _, scalar_identity_le 1 Lam hLam.le⟩

/-- The scalar branch yields the whole-carrier profile with no additional analytic premises. -/
theorem counterProfile_one (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileOneStatement alpha) : CounterProfileStatement 1 alpha := by
  rcases h with ⟨Lam, c, C, H, gx, gv, hess, hLam, hc, hC, hH, hzero,
    hhom, hcomp, hmx, hmv, hmh, hjets, heq, hgrad, hb, hjhom, hweak, hsmooth⟩
  have hx (i : Fin 1) : LocallyIntegrable (fun q => gx q i) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => gx q i)
      ((measurable_pi_apply i).comp hmx) (alpha - 3) (by linarith) (by linarith)
    · intro r hr q
      simpa only [Pi.smul_apply, smul_eq_mul] using congrArg (fun w => w i) (hjhom r hr q).1
    · intro K hK hz
      obtain ⟨M, hM⟩ := hb K hK hz
      exact ⟨M, fun q hq => (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (gx q) i).trans (hM q hq).1)⟩
  have hv (i : Fin 1) : LocallyIntegrable (fun q => gv q i) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => gv q i)
      ((measurable_pi_apply i).comp hmv) (alpha - 1) (by linarith) (by linarith)
    · intro r hr q
      simpa only [Pi.smul_apply, smul_eq_mul] using
        congrArg (fun w => w i) (hjhom r hr q).2.1
    · intro K hK hz
      obtain ⟨M, hM⟩ := hb K hK hz
      exact ⟨M, fun q hq => (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (gv q) i).trans (hM q hq).2.1)⟩
  have hh (i k : Fin 1) : LocallyIntegrable (fun q => hess q i k) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega) (fun q => hess q i k)
      (hmh i k) (alpha - 2) (by linarith) (by linarith)
    · intro r hr q
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        congrArg (fun w => w i k) (hjhom r hr q).2.2
    · intro K hK hz
      obtain ⟨M, hM⟩ := hb K hK hz
      exact ⟨M, fun q hq => (hM q hq).2.2 i k⟩
  refine ⟨1, Lam, c, C, scalarProfileCoefficient Lam, H, gx, gv, hess,
    zero_lt_one, hLam.le, hc, hC, measurable_scalarProfileCoefficient Lam,
    scalarProfileCoefficient_order Lam hLam, hH, hzero, hhom, hcomp,
    hmx, hmv, hmh, hjets, heq, hgrad, hb, hx, hv, hh,
    profile_weak_identities_extend 1 (by omega) H gx gv hess hH hx hv hh hweak,
    (fun hd => by omega), ?_⟩
  filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
  have hq0 : q.1 0 ≠ 0 := by
    intro hz
    apply hq.1
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi, Pi.zero_apply] using hz
  exact hsmooth.contDiffAt
    ((isOpen_ne.preimage ((continuous_apply 0).comp continuous_fst)).mem_nhds hq0)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
