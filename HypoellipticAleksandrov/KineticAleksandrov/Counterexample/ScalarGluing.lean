module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Piecewise
import Mathlib.Tactic

/-!
# Gluing twice differentiable scalar functions

Ordinary calculus lemmas for joining two real functions at zero with matching jets.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter
open scoped Topology ContDiff

/-- Join the positive-side function to the negative-side function at zero. -/
def scalarJoin (f g : ℝ → ℝ) (s : ℝ) : ℝ := if 0 < s then f s else g s

/-- The glued derivative at zero follows from the two one-sided derivatives. -/
theorem scalarJoin_hasDerivAt_zero (f g : ℝ → ℝ) (D : ℝ)
    (hf : HasDerivAt f D 0) (hg : HasDerivAt g D 0) (hfg : f 0 = g 0) :
    HasDerivAt (scalarJoin f g) D 0 := by
  have hr : HasDerivWithinAt (scalarJoin f g) D (Ici 0) 0 :=
    hf.hasDerivWithinAt.congr (by
      intro s hs
      rcases eq_or_lt_of_le hs with hs | hs
      · simp only [← hs, scalarJoin, lt_self_iff_false, ↓reduceIte, hfg]
      · simp only [scalarJoin, hs, ↓reduceIte])
      (by simp only [scalarJoin, lt_self_iff_false, ↓reduceIte, hfg])
  have hl : HasDerivWithinAt (scalarJoin f g) D (Iic 0) 0 :=
    hg.hasDerivWithinAt.congr (by
      intro s hs
      simp only [scalarJoin, not_lt.mpr hs, ↓reduceIte])
      (by simp only [scalarJoin, lt_self_iff_false, ↓reduceIte])
  have hu : Ici (0 : ℝ) ∪ Iic 0 = univ := by
    ext s
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 s
  exact (hr.union hl).hasDerivAt (by rw [hu]; exact univ_mem)

/-- Away from zero, differentiation commutes with the branch selection. -/
theorem scalarJoin_deriv_of_ne_zero (f g : ℝ → ℝ) (s : ℝ) (hs : s ≠ 0) :
    deriv (scalarJoin f g) s = scalarJoin (deriv f) (deriv g) s := by
  rcases lt_or_gt_of_ne hs with hs | hs
  · have he : scalarJoin f g =ᶠ[𝓝 s] g := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      simp only [scalarJoin, not_lt.mpr ht.le, ↓reduceIte]
    rw [he.deriv_eq]
    simp only [scalarJoin, not_lt.mpr hs.le, ↓reduceIte]
  · have he : scalarJoin f g =ᶠ[𝓝 s] f := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      simp only [scalarJoin, show 0 < t from ht, ↓reduceIte]
    rw [he.deriv_eq]
    simp only [scalarJoin, hs, ↓reduceIte]

/-- Matching first jets gives the global piecewise derivative identity. -/
theorem scalarJoin_deriv (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f 0 = g 0) (hdfg : deriv f 0 = deriv g 0) :
    deriv (scalarJoin f g) = scalarJoin (deriv f) (deriv g) := by
  funext s
  by_cases hs : s = 0
  · subst s
    have hd := scalarJoin_hasDerivAt_zero f g (deriv g 0)
      (by rw [← hdfg]; exact (hf 0).hasDerivAt) (hg 0).hasDerivAt hfg
    simpa only [scalarJoin, lt_self_iff_false, ↓reduceIte] using hd.deriv
  · exact scalarJoin_deriv_of_ne_zero f g s hs

/-- Matching first jets gives ordinary differentiability of the join. -/
theorem differentiable_scalarJoin (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f 0 = g 0) (hdfg : deriv f 0 = deriv g 0) :
    Differentiable ℝ (scalarJoin f g) := by
  intro s
  rcases lt_trichotomy s 0 with hs | hs | hs
  · apply (hg s).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hs] with t ht
    simp only [scalarJoin, not_lt.mpr ht.le, ↓reduceIte]
  · subst s
    exact (scalarJoin_hasDerivAt_zero f g (deriv g 0)
      (by rw [← hdfg]; exact (hf 0).hasDerivAt) (hg 0).hasDerivAt hfg).differentiableAt
  · apply (hf s).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp only [scalarJoin, show 0 < t from ht, ↓reduceIte]

/-- Matching values makes the join continuous. -/
theorem continuous_scalarJoin (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f 0 = g 0) : Continuous (scalarJoin f g) := by
  classical
  have hb : ∀ s ∈ frontier (Ioi (0 : ℝ)), f s = g s := by
    intro s hs
    rw [frontier_Ioi] at hs
    simpa only [mem_singleton_iff.mp hs] using hfg
  have he : (Ioi (0 : ℝ)).piecewise f g = scalarJoin f g := by
    funext s
    simp only [Set.piecewise, mem_Ioi, scalarJoin]
  rw [← he]
  exact Continuous.piecewise hb hf hg

/-- Matching values and two derivatives suffices for global C² regularity. -/
theorem contDiff_two_scalarJoin (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfg : f 0 = g 0) (hdfg : deriv f 0 = deriv g 0)
    (hddfg : deriv (deriv f) 0 = deriv (deriv g) 0) :
    ContDiff ℝ 2 (scalarJoin f g) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have he := scalarJoin_deriv f g hfd hgd hfg hdfg
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨differentiable_scalarJoin f g hfd hgd hfg hdfg, by norm_num, ?_⟩
  rw [he, contDiff_one_iff_deriv]
  have hfdd := hf.differentiable_deriv_two
  have hgdd := hg.differentiable_deriv_two
  refine ⟨differentiable_scalarJoin (deriv f) (deriv g) hfdd hgdd hdfg hddfg, ?_⟩
  rw [scalarJoin_deriv (deriv f) (deriv g) hfdd hgdd hdfg hddfg]
  have hfder : ContDiff ℝ 1 (deriv f) :=
    (show ContDiff ℝ (1 + 1) f from hf).deriv'
  have hgder : ContDiff ℝ 1 (deriv g) :=
    (show ContDiff ℝ (1 + 1) g from hg).deriv'
  exact continuous_scalarJoin _ _ (hfder.continuous_deriv (by norm_num))
    (hgder.continuous_deriv (by norm_num)) hddfg

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
