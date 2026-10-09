module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyHeight
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySupport
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height

/-! # Actual smooth functions from the fixed-domain zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory

/-- The actual smooth function, obtained by spatial smoothing after zero extension. -/
def smoothedZeroExtendedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) : ℝ :=
  spatialMollify phi (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨P.time, y.1, y.2⟩) (P.position, P.velocity)

/-- Smoothness is joint in the native product chart. -/
theorem smoothedZeroExtendedProfile_contDiff {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha)
    (r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × XV d =>
      smoothedZeroExtendedProfile h r mu R phi ((KineticPoint.equivProd d).symm z)) :=
  spatial_zeroExtendedProfile_contDiff_of_profile ha h r mu R hr hmu hR hvel phi

/-- Each constructed smooth function is globally nonnegative. -/
theorem smoothedZeroExtendedProfile_nonneg {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) :
    0 ≤ smoothedZeroExtendedProfile h r mu R phi P :=
  spatialMollify_nonneg phi _
    (fun y => zeroExtendedProfile_nonneg _ alpha r mu R ⟨P.time, y.1, y.2⟩) _

/-- All nonpositive times remain identically zero after spatial smoothing. -/
theorem smoothedZeroExtendedProfile_eq_zero_of_time {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) (ht : P.time ≤ 0) :
    smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  unfold smoothedZeroExtendedProfile spatialMollify
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change phi.normed volume y * zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨P.time, P.position - y.1, P.velocity - y.2⟩ = 0
  rw [zeroExtendedProfile_eq_zero_of_time _ alpha r mu R
    ⟨P.time, P.position - y.1, P.velocity - y.2⟩ ht, mul_zero]

/-- Spatial smoothing leaves a fixed outer collar whenever its radius is small enough. -/
theorem smoothedZeroExtendedProfile_eq_zero_outside_thickening {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d)
    (hq : (P.position, P.velocity) ∉
      Metric.thickening phi.rOut {q | profileFunction h q ≤ 1}) :
    smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  apply spatialMollify_eq_zero_outside_thickening phi _ _ _ _ hq
  exact (subset_tsupport _).trans
    (zeroExtendedProfile_tsupport_subset h r mu R P.time)

/-- The same strictly interior time retains height one quarter while the kernel respects
any positive prescribed collar width. No terminal-face point is used as the witness. -/
theorem exists_smoothedZeroExtendedProfile_height {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (hr : 0 < r)
    (hmu : 0 < mu) (hR : 0 < R) (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ t : ℝ, ∃ n : ℕ, 0 < t ∧ t < barrierTime mu ∧
      1 / 4 < smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n) ⟨t, 0, 0⟩ ∧
      (standardMollifierSequence (G := XV d) n).rOut < delta := by
  obtain ⟨_, _, _, _, _, _, _, h0, _⟩ := selectedProfile_spec h
  obtain ⟨t, ht, hT, hh⟩ := timeCutoff_interior_height (profileFunction h)
    alpha r mu R h0 hr hmu hsmall
  have hzero : profileFunction h (0, 0) < 1 := by
    change profileFunction h 0 < 1
    rw [h0]
    norm_num
  have he : zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩ =
      timeCutoffProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩ := by
    simp only [zeroExtendedProfile, ht, hzero, and_self, ite_true]
  obtain ⟨n, hn, hradius⟩ := exists_mollifier_preserving_height_and_collar
    (fun q : XV d => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩)
    (continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale hvel t)
    0 (by
      change 5 / 16 < zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩
      rw [he]
      exact hh) delta hdelta
  exact ⟨t, n, ht, hT, hn, hradius⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
