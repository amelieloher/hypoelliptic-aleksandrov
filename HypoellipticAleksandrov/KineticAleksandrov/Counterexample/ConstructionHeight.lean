module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionBoundary

/-! # An interior height witness survives all sufficiently late spatial mollifiers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter
open scoped Topology

/-- The same strictly interior point retains the required height for every late kernel. -/
theorem construction_smoothed_interior_height_eventually {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hS : 0 < S)
    (hTS : barrierTime mu < S ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) :
    ∃ P ∈ backwardCylinder (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) S,
      ∀ᶠ n in atTop, (1 / 4 : ℝ) ≤
        smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n) P := by
  obtain ⟨_, _, _, _, _, _, _, h0, _⟩ := selectedProfile_spec h
  obtain ⟨t, ht, hT, hh⟩ := timeCutoff_interior_height (profileFunction h)
    alpha r mu R h0 hr hmu hsmall
  have hq : profileFunction h (0, 0) < 1 := by
    change profileFunction h 0 < 1
    rw [h0]
    norm_num
  have he := zeroExtendedProfile_eq_raw_on_profile (profileFunction h) alpha r mu R
    hr hmu hR hvel (⟨t, 0, 0⟩ : KineticPoint d) hq
  have hh' : 5 / 16 < zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩ := by
    rw [he]
    exact hh
  have hm := mollify_preserves_height_eventually
    (fun q : XV d => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩)
    (continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale hvel t)
    0 hh'
  refine ⟨⟨t, 0, 0⟩, construction_origin_mem_cylinder _ S t hS hTS ht hT, ?_⟩
  filter_upwards [hm] with n hn
  exact hn.le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
