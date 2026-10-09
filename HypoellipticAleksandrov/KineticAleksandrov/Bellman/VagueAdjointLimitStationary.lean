module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactness
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Tactic

/-! # The stationary weak equation survives vague convergence -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The source transport and diffusion tests are continuous and compact on the carrier. -/
theorem bellman_stationary_test_properties (phi : (ℝ × ℝ) → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ {q | q ≠ (0, 0)}) :
    (Continuous (fun q : BellmanPuncturedPlane =>
      q.val.2 * fderiv ℝ phi q.val (1, 0)) ∧
      HasCompactSupport (fun q : BellmanPuncturedPlane =>
        q.val.2 * fderiv ℝ phi q.val (1, 0))) ∧
    (Continuous (fun q : BellmanPuncturedPlane =>
      fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1)) ∧
      HasCompactSupport (fun q : BellmanPuncturedPlane =>
        fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1))) := by
  have hl := bellman_contDiff_direction hphi (1, 0)
  have hv := bellman_contDiff_direction hphi (0, 1)
  have hr := bellman_contDiff_direction hv (0, 1)
  have hls : tsupport (fun q : ℝ × ℝ => q.2 * fderiv ℝ phi q (1, 0)) ⊆ tsupport phi :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (1, 0))
  have hrs : tsupport (fun q : ℝ × ℝ =>
      fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q (0, 1)) ⊆ tsupport phi :=
    (tsupport_fderiv_apply_subset ℝ (0, 1)).trans
      (tsupport_fderiv_apply_subset ℝ (0, 1))
  exact ⟨⟨(continuous_snd.mul hl.continuous).comp continuous_subtype_val,
      bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hls)
        (hls.trans hs)⟩,
    ⟨hr.continuous.comp continuous_subtype_val,
      bellman_test_compact_subtype (hc.of_isClosed_subset (isClosed_tsupport _) hrs)
        (hrs.trans hs)⟩⟩

/-- The actual stationary identity passes to the common vague limit. -/
theorem bellman_vague_limit_stationary (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (hstat : ∀ n, IsBellmanStationaryAdjointPair (mu n) (eta n))
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf) :
    IsBellmanStationaryAdjointPair muInf etaInf := by
  intro phi hphi hc hs
  obtain ⟨⟨hl, hlc⟩, ⟨hr, hrc⟩⟩ := bellman_stationary_test_properties phi hphi hc hs
  have ht := (hmv _ hl hlc).add (hev _ hr hrc)
  have he : (fun n =>
      (∫ q, q.val.2 * fderiv ℝ phi q.val (1, 0) ∂mu n) +
      (∫ q, fderiv ℝ (fun z => fderiv ℝ phi z (0, 1)) q.val (0, 1) ∂eta n)) =
      fun _ : ℕ => (0 : ℝ) := funext (fun n => hstat n phi hphi hc hs)
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end HypoellipticAleksandrov.KineticAleksandrov
