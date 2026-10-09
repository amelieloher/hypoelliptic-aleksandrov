module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Profile

/-! # The proved higher-dimensional profile supplies the shared branch interface -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The internally constructed profile satisfies the exact higher-dimensional branch statement. -/
theorem counterProfileGeTwo_holds (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) : CounterProfileGeTwoStatement d alpha := by
  obtain ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
    hsmooth, hhom, hcomp, heq, hgrad⟩ := profile_ge_two d hd alpha ha ha1
  exact ⟨lam, Lam, c, C, A, H, hlam, hLam, hc, hC, hmA, hA, hzero,
    hhom, hcomp, hsmooth, heq, hgrad⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
