module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceHomogeneousSpace

/-! # Pointwise identification using homogeneous L2 convergence

A common continuous representative on an open domain is identified at a chosen point by
any genuine continuous homogeneous approximation converging in L2 and at that point.
The pointwise approximation may depend on the point; the representative does not.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution
open scoped Topology

/-- Homogeneous L2 limits have a continuous representative identified by every actual
homogeneous approximating sequence at every point where that sequence converges. -/
theorem exists_continuousRepresentative_identified_by_homogeneous_limits
    (hH : HormanderHypoellipticityStatement) {d : ℕ}
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (U K : Set (EvolutionVec d)) (hU : IsOpen U) (hK : IsCompact K)
    (hKi : K ⊆ closure (interior K)) (hKU : K ⊆ U)
    [IsFiniteMeasure (volume.restrict U)]
    (u : EvolutionVec d → ℝ) (hu : MemLp u 2 (volume.restrict U))
    (hw : IsWeakTransportedSolution B b U u (fun _ => 0)) :
    ∃ v : EvolutionVec d → ℝ, ContinuousOn v U ∧ u =ᵐ[volume.restrict U] v ∧
      ∀ (f : ℕ → EvolutionVec d → ℝ)
        (hf : ∀ n, MemLp (f n) 2 (volume.restrict U)),
        (∀ n, ContinuousOn (f n) U) →
        (∀ n, IsWeakTransportedSolution B b U (f n) (fun _ => 0)) →
        Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)) →
        ∀ z ∈ K, Tendsto (fun n => f n z) atTop (𝓝 (u z)) → u z = v z := by
  classical
  let H := boundedSourceHomogeneousL2Space B b hB hb U
  have hclosed := isClosed_boundedSourceHomogeneousL2Space B b hB hb U
  have hrep := boundedSourceHomogeneousL2Space_hasContinuousRepresentative hH B b hB hb
    lam Lam m hlam hm hell hcoerc U hU
  let x : H := ⟨hu.toLp u, mem_boundedSourceHomogeneousL2Space_of_isWeak B b hB hb U u hu hw⟩
  let v := continuousWeakRepresentative volume U H hrep x
  have hvc := continuousWeakRepresentative_continuous volume U H hrep x
  have hve := hu.coeFn_toLp.symm.trans
    (continuousWeakRepresentative_ae volume U H hrep x)
  refine ⟨v, hvc, hve, ?_⟩
  intro f hf hfc hfw hlim z hz hp
  let fn (n : ℕ) : H := ⟨(hf n).toLp (f n),
    mem_boundedSourceHomogeneousL2Space_of_isWeak B b hB hb U (f n) (hf n) (hfw n)⟩
  have hfn : Tendsto fn atTop (𝓝 x) := tendsto_subtype_rng.mpr hlim
  let L := compactRepresentativeMap volume U K hU hKU H hrep
  have hL := continuous_compactRepresentativeMap volume U K hU hKU hK hKi H hclosed hrep
  have hmaps := (hL.tendsto x).comp hfn
  have hpoint := (continuous_eval_const (⟨z, hz⟩ : K)).tendsto (L x) |>.comp hmaps
  have heq (n : ℕ) : L (fn n) ⟨z, hz⟩ = f n z :=
    compactRepresentativeMap_apply_eq volume U K hU hKU H hrep (fn n) (f n)
      (hfc n) (hf n).coeFn_toLp ⟨z, hz⟩
  have hvlim : Tendsto (fun n => f n z) atTop (𝓝 (v z)) := by
    exact hpoint.congr' (Eventually.of_forall heq)
  exact tendsto_nhds_unique hp hvlim

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
