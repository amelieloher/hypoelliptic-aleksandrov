module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoWeak

/-! # Selected profile jets commute with normalized convolution -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory

/-- The standard smooth approximation of the selected unflattened profile. -/
noncomputable def mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) : XV d → ℝ :=
  spatialMollify (standardMollifierSequence n) (profileFunction h)

/-- Each selected profile approximation is smooth. -/
theorem contDiff_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedProfile h n) :=
  spatialMollify_contDiff _ _ (selectedProfile_spec h).2.2.2.2.2.2.1.locallyIntegrable

/-- The position derivative of the profile approximation is convolution of the selected jet. -/
theorem dx_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) (q : XV d) (i : Fin d) :
    dx (mollifiedProfile h n) q i =
      spatialMollify (standardMollifierSequence n) (fun z => profilePositionJet h z i) q := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hw := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply mollify_weak_directional_jet _ _ _ hH.locallyIntegrable (Pi.single i 1, 0)
  intro test ht hc
  exact (hw test (ht.of_le (by simp)) hc).1 i

/-- The velocity derivative of the approximation is convolution of the selected weak jet. -/
theorem dv_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) (q : XV d) (i : Fin d) :
    dv (mollifiedProfile h n) q i =
      spatialMollify (standardMollifierSequence n) (fun z => profileVelocityJet h z i) q := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hw := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply mollify_weak_directional_jet _ _ _ hH.locallyIntegrable (0, Pi.single i 1)
  intro test ht hc
  exact (hw test (ht.of_le (by simp)) hc).2.1 i

/-- The velocity Hessian of the approximation is convolution of the selected weak Hessian. -/
theorem dvv_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) (q : XV d) (i k : Fin d) :
    dvv (mollifiedProfile h n) q i k =
      spatialMollify (standardMollifierSequence n) (fun z => profileHessian h z i k) q := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply mollify_weak_second_jet _ _ (fun z => profileVelocityJet h z k) _
    hH.locallyIntegrable (hv k) (0, Pi.single k 1) (0, Pi.single i 1)
  · intro test ht hc
    exact (hw test (ht.of_le (by simp)) hc).2.1 k
  · intro test ht hc
    change (∫ z, profileFunction h z * dvv test z k i) = _
    calc
      _ = (∫ z, profileFunction h z * dvv test z i k) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => congrArg (fun a => profileFunction h z * a)
          (dvv_test_swap test (ht.of_le (by simp)) z k i))
      _ = _ := (hw test (ht.of_le (by simp)) hc).2.2 i k

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
