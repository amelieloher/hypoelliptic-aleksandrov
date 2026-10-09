module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalization
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactnessExhaustion
import Mathlib.Tactic

/-! # Simultaneous vague subsequences for globally infinite homogeneous Radon pairs -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ENNReal NNReal
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Vague convergence tests every continuous function of compact support on the actual carrier. -/
def IsBellmanVagueLimit (mu : ℕ → Measure BellmanPuncturedPlane)
    (nu : Measure BellmanPuncturedPlane) : Prop :=
  ∀ f : BellmanPuncturedPlane → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun n => ∫ q, f q ∂mu n) atTop (𝓝 (∫ q, f q ∂nu))

/-- Uniform bounds on each compact give one common Radon subsequence for two measure lanes. -/
theorem bellman_radon_pair_subsequence (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (hm : ∀ n, IsBellmanRadon (mu n)) (he : ∀ n, IsBellmanRadon (eta n))
    (hb : ∀ K : Set BellmanPuncturedPlane, IsCompact K → ∃ C : ℝ≥0,
      ∀ n, mu n K ≤ C ∧ eta n K ≤ C) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ muinf etainf : Measure BellmanPuncturedPlane,
      IsBellmanRadon muinf ∧ IsBellmanRadon etainf ∧
      IsBellmanVagueLimit (fun n => mu (k n)) muinf ∧
      IsBellmanVagueLimit (fun n => eta (k n)) etainf := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  let m (b : Bool) (n : ℕ) : Measure BellmanPuncturedPlane := if b then eta n else mu n
  let (b : Bool) (n : ℕ) : IsFiniteMeasureOnCompacts (m b n) := by
    cases b
    · exact (hm n).1
    · exact (he n).1
  have hbound (b : Bool) (K : Set BellmanPuncturedPlane) (hK : IsCompact K) :
      ∃ C : ℝ≥0, ∀ n, m b n K ≤ C := by
    obtain ⟨C, hC⟩ := hb K hK
    refine ⟨C, ?_⟩
    intro n
    cases b
    · exact (hC n).1
    · exact (hC n).2
  obtain ⟨k, hk, ht⟩ := bellman_radon_family_subsequence m hbound
  obtain ⟨muinf, hmf, hmr, hmt⟩ := ht false
  obtain ⟨etainf, hef, her, het⟩ := ht true
  refine ⟨k, hk, muinf, etainf, ⟨hmf, hmr⟩, ⟨hef, her⟩, ?_, ?_⟩
  · intro f hf hfc
    exact hmt (⟨⟨f, hf⟩, hfc⟩ : C_c(BellmanPuncturedPlane, ℝ))
  · intro f hf hfc
    exact het (⟨⟨f, hf⟩, hfc⟩ : C_c(BellmanPuncturedPlane, ℝ))

/-- Bounded-degree homogeneous pairs have annular normalization and a simultaneous Radon limit. -/
theorem homogeneous_pairs_subsequence (R : ℝ) (hR : 1 ≤ R)
    (beta : ℕ → ℝ) (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (hp : ∀ n, IsBellmanAdjointPair 1 R (beta n) (mu n) (eta n))
    (hb : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b) :
    ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) ∧
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        (∀ n, ∫ q, chi q.val ∂(ENNReal.ofReal (c n) • mu n) = 1) ∧
        ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ muinf etainf : Measure BellmanPuncturedPlane,
          IsBellmanRadon muinf ∧ IsBellmanRadon etainf ∧
          IsBellmanVagueLimit (fun n => ENNReal.ofReal (c (k n)) • mu (k n)) muinf ∧
          IsBellmanVagueLimit (fun n => ENNReal.ofReal (c (k n)) • eta (k n)) etainf := by
  obtain ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, hbound⟩ :=
    bellman_pairs_annular_normalization R hR beta mu eta hp hb
  obtain ⟨k, hk, muinf, etainf, hmf, hef, hmt, het⟩ :=
    bellman_radon_pair_subsequence (fun n => ENNReal.ofReal (c n) • mu n)
      (fun n => ENNReal.ofReal (c n) • eta n)
      (fun n => (hp n).1.smul _ ENNReal.ofReal_ne_top)
      (fun n => (hp n).2.1.smul _ ENNReal.ofReal_ne_top) hbound
  exact ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, k, hk,
    muinf, etainf, hmf, hef, hmt, het⟩

end HypoellipticAleksandrov.KineticAleksandrov
