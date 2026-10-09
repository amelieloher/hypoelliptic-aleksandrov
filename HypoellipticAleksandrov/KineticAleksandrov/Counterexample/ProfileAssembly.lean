module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileOneAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoWeak

/-! # Assembly of the two exact profile branches -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The higher-dimensional branch yields the shared whole-carrier weak profile. -/
theorem counterProfile_ge_two (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileGeTwoStatement d alpha) : CounterProfileStatement d alpha := by
  rcases h with ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
    hhom, hcomp, hs, heq, hgrad⟩
  have hd1 : 1 ≤ d := by omega
  have hH := continuous_profile_of_comparison H alpha c C ha hc.le hzero hcomp hs
  obtain ⟨hx, hv, hh⟩ := profile_classical_jets_locallyIntegrable d hd1 H alpha ha ha1 hhom hs
  have heqae : ∀ᵐ q ∂volume, matrixContraction (A q) (dvv H q) = PDE.vecDot q.2 (dx H q) := by
    filter_upwards [coordinates_ne_zero_ae d hd1] with q hq
    exact heq q (fun hz => hq.1 (congrArg Prod.fst hz))
  refine ⟨lam, Lam, c, C, A, H, dx H, dv H, dvv H,
    hlam, hLam, hc, hC, hmA, hA, hH, hzero, hhom, hcomp,
    measurable_dx H, measurable_dv H, measurable_dvv H,
    Filter.Eventually.of_forall (fun _ => ⟨rfl, rfl, rfl⟩), heqae, hgrad,
    profile_jets_compact_bound H hs, hx, hv, hh,
    profile_weak_identities_extend d hd1 H (dx H) (dv H) (dvv H) hH hx hv hh
      (profile_classical_punctured_weak d hd1 H alpha ha ha1 hH hhom hs), (fun _ => hs), ?_⟩
  filter_upwards [coordinates_ne_zero_ae d hd1] with q hq
  have hq0 : q ≠ 0 := fun hz => hq.1 (congrArg Prod.fst hz)
  exact (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq0))).of_le (by simp)

/-- The exact scalar and higher-dimensional branch surfaces give the shared profile. -/
theorem counterProfile_of_branches (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hone : d = 1 → CounterProfileOneStatement alpha)
    (hge : 2 ≤ d → CounterProfileGeTwoStatement d alpha) : CounterProfileStatement d alpha := by
  by_cases hd1 : d = 1
  · subst d
    exact counterProfile_one alpha ha ha1 (hone rfl)
  · have hd2 : 2 ≤ d := by omega
    exact counterProfile_ge_two d hd2 alpha ha ha1 (hge hd2)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
