module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeWeak

/-!
# Transferring weak equations and smooth representatives across the coordinate bridge

Let `e = evolutionHomeomorph n : EvolutionVec n ≃ₜ KineticPoint n`, `(σ, v, z) ↦ ⟨σ, v, z⟩`.  A
function `u : KineticPoint n → ℝ` on a set `Ω ⊆ KineticPoint n` is pulled back to the packed
space as `u ∘ e` on `e ⁻¹' Ω`.  Since `e` is measure preserving
(`measurePreserving_evolutionHomeomorph`), local integrability, the integrals of the weak
equation and "equal almost everywhere" transfer verbatim:

* `isDistributionalSolution_comp_iff`: `u ∘ e` is a distributional solution on `e ⁻¹' Ω` iff
  `u` is locally integrable on `Ω` (for the `KineticPoint` volume) and
  `∫_Ω u(z) · L^*ψ(e⁻¹ z) dz = ∫_Ω g(z) ψ(e⁻¹ z) dz` for the smooth compactly supported
  `ψ` on the packed space with support in `e ⁻¹' Ω`;
* `ae_eq_comp_iff` and `contDiffOn_comp_iff`: the conclusion of the Hörmander theorem on the
  packed space (a smooth representative a.e. equal to `u ∘ e`) is the same as a representative
  `f ∘ e.symm` of `u` with `f ∘ e` smooth.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open HypoellipticAleksandrov

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- The measurable embedding underlying the coordinate bridge. -/
theorem measurableEmbedding_evolutionHomeomorph :
    MeasurableEmbedding (evolutionHomeomorph n) :=
  (evolutionMeasurableEquiv n).measurableEmbedding

/-- Change of variables for set integrals along the coordinate bridge. -/
theorem setIntegral_comp_evolutionHomeomorph (F : KineticPoint n → ℝ) (Ω : Set (KineticPoint n)) :
    (∫ x in evolutionHomeomorph n ⁻¹' Ω, F (evolutionHomeomorph n x)) = ∫ z in Ω, F z :=
  measurePreserving_evolutionHomeomorph.setIntegral_preimage_emb
    measurableEmbedding_evolutionHomeomorph F Ω

/-- Local integrability transfers across the coordinate bridge (in both directions). -/
theorem locallyIntegrableOn_comp_evolutionHomeomorph_iff {f : KineticPoint n → ℝ}
    {Ω : Set (KineticPoint n)} :
    LocallyIntegrableOn (f ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' Ω) volume ↔
      LocallyIntegrableOn f Ω volume := by
  have hmp := measurePreserving_evolutionHomeomorph (n := n)
  have hem := measurableEmbedding_evolutionHomeomorph (n := n)
  have hI : ∀ t : Set (KineticPoint n), IntegrableOn (f ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' t) volume ↔ IntegrableOn f t volume := fun t =>
    hmp.integrableOn_comp_preimage hem
  have hmap : ∀ x : EvolutionVec n, Filter.map (evolutionHomeomorph n)
      (nhdsWithin x (evolutionHomeomorph n ⁻¹' Ω)) =
        nhdsWithin (evolutionHomeomorph n x) Ω := fun x =>
    (evolutionHomeomorph n).isOpenEmbedding.map_nhdsWithin_preimage_eq Ω x
  constructor
  · intro h z hz
    have hz' : (evolutionHomeomorph n).symm z ∈ evolutionHomeomorph n ⁻¹' Ω := by simpa using hz
    obtain ⟨t, ht, hti⟩ := h _ hz'
    have hpre : evolutionHomeomorph n ⁻¹' ((evolutionHomeomorph n).symm ⁻¹' t) = t := by
      ext x; simp
    refine ⟨(evolutionHomeomorph n).symm ⁻¹' t, ?_, (hI _).1 (by rwa [hpre])⟩
    have := hmap ((evolutionHomeomorph n).symm z)
    rw [Homeomorph.apply_symm_apply] at this
    rw [← this, Filter.mem_map, hpre]
    exact ht
  · intro h x hx
    obtain ⟨t, ht, hti⟩ := h (evolutionHomeomorph n x) hx
    refine ⟨evolutionHomeomorph n ⁻¹' t, ?_, (hI t).2 hti⟩
    rw [← Filter.mem_map, hmap]
    exact ht

/-- Almost-everywhere equality transfers across the coordinate bridge. -/
theorem ae_eq_comp_evolutionHomeomorph_iff {f g : KineticPoint n → ℝ}
    {Ω : Set (KineticPoint n)} :
    (f ∘ evolutionHomeomorph n) =ᵐ[volume.restrict (evolutionHomeomorph n ⁻¹' Ω)]
        (g ∘ evolutionHomeomorph n) ↔ f =ᵐ[volume.restrict Ω] g := by
  have hmp := (measurePreserving_evolutionHomeomorph (n := n)).restrict_preimage_emb
    measurableEmbedding_evolutionHomeomorph Ω
  rw [← hmp.map_eq, Filter.EventuallyEq, Filter.EventuallyEq,
    measurableEmbedding_evolutionHomeomorph.ae_map_iff]
  rfl

/-- Smoothness of `f ∘ e` on `e ⁻¹' Ω` is smoothness of `f` on `Ω` read through the continuous
linear equivalence `evolutionProdCLE n : EvolutionVec n ≃L[ℝ] ℝ × (ℝ^d × ℝ^d)`, i.e. in the
convention of `IsSmoothFullKineticCoefficient`. -/
theorem contDiffOn_comp_evolutionHomeomorph_iff {f : KineticPoint n → ℝ}
    {Ω : Set (KineticPoint n)} :
    ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' Ω) ↔
      ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => f ⟨q.1, q.2.1, q.2.2⟩)
        (KineticPoint.equivProd n '' Ω) := by
  have h1 : (f ∘ evolutionHomeomorph n) =
      (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => f ⟨q.1, q.2.1, q.2.2⟩) ∘ evolutionProdCLE n :=
    rfl
  have h2 : evolutionHomeomorph n ⁻¹' Ω =
      evolutionProdCLE n ⁻¹' (KineticPoint.equivProd n '' Ω) := by
    ext x
    simp only [mem_preimage, mem_image]
    constructor
    · intro hx; exact ⟨_, hx, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have : z = evolutionHomeomorph n x := (KineticPoint.equivProd n).injective hzx
      rw [← this]; exact hz
  rw [h1, h2]
  exact (evolutionProdCLE n).contDiffOn_comp_iff

/-- Pointwise smoothness of the packed pullback is smoothness of `u` in the product convention
(`IsSmoothFullKineticCoefficient` style) at the corresponding point of `ℝ × (ℝ^d × ℝ^d)`. -/
theorem contDiffAt_comp_evolutionHomeomorph_iff {k : WithTop ℕ∞} {f : KineticPoint n → ℝ}
    {x : EvolutionVec n} :
    ContDiffAt ℝ k (f ∘ evolutionHomeomorph n) x ↔
      ContDiffAt ℝ k (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => f ⟨q.1, q.2.1, q.2.2⟩)
        (KineticPoint.equivProd n (evolutionHomeomorph n x)) := by
  have h1 : (f ∘ evolutionHomeomorph n) =
      (fun q : ℝ × (PDE.Vec n × PDE.Vec n) => f ⟨q.1, q.2.1, q.2.2⟩) ∘ evolutionProdCLE n :=
    rfl
  have := (evolutionProdCLE n).contDiffAt_comp_iff (𝕜 := ℝ) (n := k)
    (f := fun q : ℝ × (PDE.Vec n × PDE.Vec n) => f ⟨q.1, q.2.1, q.2.2⟩)
    (x := evolutionProdCLE n x)
  rw [ContinuousLinearEquiv.symm_apply_apply] at this
  rw [h1]
  exact this

/-! ### Weak equations -/

/-- **Weak equations transfer.**  `u ∘ e` is a distributional solution of `L v = g ∘ e` on
`e ⁻¹' Ω` (packed coordinates, test functions on `ℝ^{1+2d}`) iff `u` is locally integrable on
`Ω` for the `KineticPoint` volume and the weak identity holds with the integrals over `Ω` taken
for the `KineticPoint` volume. -/
theorem isDistributionalSolution_comp_iff
    (Ladj : (EvolutionVec n → ℝ) → EvolutionVec n → ℝ) (Ω : Set (KineticPoint n))
    (u g : KineticPoint n → ℝ) :
    IsDistributionalSolution Ladj (evolutionHomeomorph n ⁻¹' Ω) (u ∘ evolutionHomeomorph n)
        (g ∘ evolutionHomeomorph n) ↔
      LocallyIntegrableOn u Ω volume ∧
        ∀ ψ : EvolutionVec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ evolutionHomeomorph n ⁻¹' Ω →
          (∫ z in Ω, u z * Ladj ψ ((evolutionHomeomorph n).symm z)) =
            ∫ z in Ω, g z * ψ ((evolutionHomeomorph n).symm z) := by
  unfold IsDistributionalSolution
  rw [locallyIntegrableOn_comp_evolutionHomeomorph_iff]
  refine and_congr_right fun _ => forall_congr' fun ψ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  have h1 := setIntegral_comp_evolutionHomeomorph
    (fun z => u z * Ladj ψ ((evolutionHomeomorph n).symm z)) Ω
  have h2 := setIntegral_comp_evolutionHomeomorph
    (fun z => g z * ψ ((evolutionHomeomorph n).symm z)) Ω
  simp only [Homeomorph.symm_apply_apply] at h1 h2
  rw [Function.comp_def, Function.comp_def, h1, h2]

/-- The kinetic-side weak equation for `Lop`: `u` is locally integrable on `Ω ⊆ KineticPoint n` and
`∫_Ω u(z) · Lop^*ψ(e⁻¹ z) dz = ∫_Ω g(z) ψ(e⁻¹ z) dz` for every smooth `ψ` on `ℝ^{1+2d}`
with compact support inside `e ⁻¹' Ω`. -/
def IsKineticWeakTransportedSolution (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (Ω : Set (KineticPoint n)) (u g : KineticPoint n → ℝ) : Prop :=
  LocallyIntegrableOn u Ω volume ∧
    ∀ ψ : EvolutionVec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ evolutionHomeomorph n ⁻¹' Ω →
      (∫ z in Ω, u z * transportedAdjoint B b ψ ((evolutionHomeomorph n).symm z)) =
        ∫ z in Ω, g z * ψ ((evolutionHomeomorph n).symm z)

/-- The kinetic-side weak equation for `L_ε = Lop + ε Δ_z`. -/
def IsKineticWeakRegularizedSolution (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (ε : ℝ) (Ω : Set (KineticPoint n)) (u g : KineticPoint n → ℝ) :
    Prop :=
  LocallyIntegrableOn u Ω volume ∧
    ∀ ψ : EvolutionVec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ evolutionHomeomorph n ⁻¹' Ω →
      (∫ z in Ω, u z * regularizedAdjoint B b ε ψ ((evolutionHomeomorph n).symm z)) =
        ∫ z in Ω, g z * ψ ((evolutionHomeomorph n).symm z)

theorem isWeakTransportedSolution_comp_iff (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (Ω : Set (KineticPoint n)) (u g : KineticPoint n → ℝ) :
    IsWeakTransportedSolution B b (evolutionHomeomorph n ⁻¹' Ω) (u ∘ evolutionHomeomorph n)
        (g ∘ evolutionHomeomorph n) ↔ IsKineticWeakTransportedSolution B b Ω u g :=
  isDistributionalSolution_comp_iff (transportedAdjoint B b) Ω u g

theorem isWeakRegularizedSolution_comp_iff (B : FullKineticCoefficient n)
    (b : PDE.Vec n → PDE.Vec n) (ε : ℝ) (Ω : Set (KineticPoint n)) (u g : KineticPoint n → ℝ) :
    IsWeakRegularizedSolution B b ε (evolutionHomeomorph n ⁻¹' Ω) (u ∘ evolutionHomeomorph n)
        (g ∘ evolutionHomeomorph n) ↔ IsKineticWeakRegularizedSolution B b ε Ω u g :=
  isDistributionalSolution_comp_iff (regularizedAdjoint B b ε) Ω u g

/-- **Kinetic weak equation ⇒ Hörmander weak equation (`ε = 0`).**  A kinetic distributional
solution of `Lop u = g` on `Ω ⊆ KineticPoint n`, with `g ∘ e` smooth on `e ⁻¹' Ω`, gives the
carrier `HasWeakHormanderEquation` for `u ∘ e` on `e ⁻¹' Ω`. -/
theorem hasWeakHormanderEquation_comp_transportedFields {lam Lam : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) {Ω : Set (KineticPoint n)} {u g : KineticPoint n → ℝ}
    (hu : IsKineticWeakTransportedSolution B b Ω u g)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (g ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' Ω)) :
    HasWeakHormanderEquation (evolutionHomeomorph n ⁻¹' Ω) (transportedFields B b)
      (fun _ => 0) (g ∘ evolutionHomeomorph n) (u ∘ evolutionHomeomorph n) :=
  hasWeakHormanderEquation_transportedFields hlam hB hell hb
    ((isWeakTransportedSolution_comp_iff B b Ω u g).2 hu) hg

/-- **Kinetic weak equation ⇒ Hörmander weak equation (`ε ≥ 0`).**  As above for
`L_ε = Lop + ε Δ_z` and `regularizedFields B b ε`. -/
theorem hasWeakHormanderEquation_comp_regularizedFields {lam Lam ε : ℝ} (hε : 0 ≤ ε)
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) {Ω : Set (KineticPoint n)} {u g : KineticPoint n → ℝ}
    (hu : IsKineticWeakRegularizedSolution B b ε Ω u g)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (g ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' Ω)) :
    HasWeakHormanderEquation (evolutionHomeomorph n ⁻¹' Ω) (regularizedFields B b ε)
      (fun _ => 0) (g ∘ evolutionHomeomorph n) (u ∘ evolutionHomeomorph n) :=
  hasWeakHormanderEquation_regularizedFields hε hlam hB hell hb
    ((isWeakRegularizedSolution_comp_iff B b ε Ω u g).2 hu) hg

/-- **Conclusion transfer.**  A smooth representative of `u ∘ e` on `e ⁻¹' Ω` (the conclusion of
the Hörmander theorem on the packed space) yields a representative `f ∘ e.symm` of `u` on `Ω`
that is smooth in packed coordinates and equals `u` almost everywhere on `Ω`. -/
theorem exists_kinetic_representative {Ω : Set (KineticPoint n)} {u : KineticPoint n → ℝ}
    (h : ∃ f : EvolutionVec n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (evolutionHomeomorph n ⁻¹' Ω) ∧
      (u ∘ evolutionHomeomorph n) =ᵐ[volume.restrict (evolutionHomeomorph n ⁻¹' Ω)] f) :
    ∃ f : KineticPoint n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' Ω) ∧
        u =ᵐ[volume.restrict Ω] f := by
  obtain ⟨f, hf, hae⟩ := h
  refine ⟨f ∘ (evolutionHomeomorph n).symm, ?_, ?_⟩
  · simpa [Function.comp_def] using hf
  · rw [← ae_eq_comp_evolutionHomeomorph_iff]
    simpa [Function.comp_def] using hae

end HypoellipticAleksandrov.KineticAleksandrov.Evolution
