module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDominationAllTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionClipped
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement

/-! # Core occupation exhausted and dominated by the canonical enlarged visits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The core domination statement, including initial poles at the named lower time. -/
theorem coreDominationStatement_holds : CoreDominationStatement := by
  classical
  intro hH hLE lam Lam hlam hLam A c J s T P hP _hbar _hJ hs
  have := enlargedVisitStarts_finite_of_outer_pole hH hLE hlam hLam A c J s T P
    ⟨hs, hP⟩
  have hT : s < T := hs.trans_lt hP.1
  have hi := enlargedOuterGreen_core_identity_of_finite_count hH hLE hlam hLam A c J s T
    hT P ⟨hs, hP⟩
  have hd := enlargedOuterGreen_core_domination_of_finite_count hH hLE hlam hLam A c J s T
    hT P ⟨hs, hP⟩
  have he : enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      stripGreen hH hLE hlam hLam A J T ⟨P, WithTop.coe_lt_coe.mpr hP.1, hP.2⟩ := by
    change (if hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion T then _ else 0) = _
    rw [dite_eq_left (show P ∈ enlargedVisitPoleSet J.toFiniteUnion T from
      ⟨hP.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2⟩)]
    rfl
  rw [he] at hi hd
  exact ⟨hi, hd⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
