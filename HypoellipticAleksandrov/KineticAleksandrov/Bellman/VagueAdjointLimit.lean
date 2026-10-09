module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitDegree
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitStationary
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimitScaling
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Tactic

/-! # Normalized vague limits retain the complete homogeneous adjoint-pair condition -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A fixed compact normalization survives the limit and prevents a zero adjoint pair. -/
theorem bellman_vague_limit_pair (R betaInf : ℝ) (_hR : 1 ≤ R)
    (beta : ℕ → ℝ) (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (muInf etaInf : Measure BellmanPuncturedPlane)
    (hbeta : Tendsto beta atTop (𝓝 betaInf))
    (hp : ∀ n, IsBellmanAdjointPair 1 R (beta n) (mu n) (eta n))
    (hmInf : IsBellmanRadon muInf) (heInf : IsBellmanRadon etaInf)
    (hmv : IsBellmanVagueLimit mu muInf) (hev : IsBellmanVagueLimit eta etaInf)
    (chi : (ℝ × ℝ) → ℝ) (hchi : Continuous chi) (hc : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | q ≠ (0, 0)})
    (hone : ∀ n, ∫ q, chi q.val ∂mu n = 1) :
    IsBellmanAdjointPair 1 R betaInf muInf etaInf ∧
      (∫ q, chi q.val ∂muInf) = 1 := by
  have ht := hmv (fun q => chi q.val) (hchi.comp continuous_subtype_val)
    (bellman_test_compact_subtype hc hs)
  have hn : (∫ q, chi q.val ∂muInf) = 1 := by
    have he : (fun n => ∫ q, chi q.val ∂mu n) = fun _ : ℕ => (1 : ℝ) := funext hone
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hnonzero : muInf ≠ 0 := by
    intro hz
    rw [hz, integral_zero_measure] at hn
    norm_num at hn
  have hlo : muInf ≤ etaInf := bellman_vague_limit_le mu eta muInf etaInf
    (fun n => (hp n).2.1.1) hmInf heInf hmv hev
    (fun n => by simpa only [ENNReal.ofReal_one, one_smul] using (hp n).2.2.2.1)
  have hhi : etaInf ≤ ENNReal.ofReal R • muInf := bellman_vague_limit_le eta
    (fun n => ENNReal.ofReal R • mu n) etaInf (ENNReal.ofReal R • muInf)
    (fun n => ((hp n).1.smul _ ENNReal.ofReal_ne_top).1)
    heInf (hmInf.smul _ ENNReal.ofReal_ne_top) hev (hmv.smul _) (fun n => (hp n).2.2.2.2.1)
  have hstat := bellman_vague_limit_stationary mu eta muInf etaInf
    (fun n => (hp n).2.2.2.2.2.1) hmv hev
  have hdm := bellman_vague_limit_degree beta betaInf mu muInf hbeta
    (fun n => (hp n).2.2.2.2.2.2.1) hmInf hmv
  have hde := bellman_vague_limit_degree beta betaInf eta etaInf hbeta
    (fun n => (hp n).2.2.2.2.2.2.2) heInf hev
  exact ⟨⟨hmInf, heInf, Or.inl hnonzero, by
    simpa only [ENNReal.ofReal_one, one_smul] using hlo, hhi, hstat, hdm, hde⟩, hn⟩

end HypoellipticAleksandrov.KineticAleksandrov
