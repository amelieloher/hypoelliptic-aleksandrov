module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Cylinders
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Classical terminal solutions under an affine change of variables

For compatible moving domains, `u` is a classical terminal solution of the original problem
with terminal datum `F` if and only if `u ∘ Φ` is one for the rescaled data with the
terminal datum `F ∘ Φ_τ`.  Every clause of `IsClassicalTerminalSolution` (boundedness,
continuity, smoothness, the equation, terminal values, lateral values) is transported by
the chain rule `Scaling.Calculus` and the cylinder identities of `Scaling.Cylinders`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory Set
open HypoellipticAleksandrov

namespace KineticAffineScaling

variable {d : ℕ} (Φ : KineticAffineScaling d)

/-! ### Transport of quantifiers and regularity -/

theorem forall_mem_iff {S S' : Set (KineticPoint d)} (hS : ∀ p, p ∈ S' ↔ Φ.point p ∈ S)
    {f : KineticPoint d → Prop} : (∀ p ∈ S', f (Φ.point p)) ↔ ∀ p ∈ S, f p := by
  constructor
  · intro h p hp
    have hmem : Φ.pointInv p ∈ S' := (hS _).2 (by rwa [Φ.point_pointInv])
    simpa only [Φ.point_pointInv] using h _ hmem
  · intro h p hp
    exact h _ ((hS p).1 hp)

theorem continuousOn_iff {S S' : Set (KineticPoint d)} (hS : ∀ p, p ∈ S' ↔ Φ.point p ∈ S)
    {u : KineticPoint d → ℝ} :
    ContinuousOn (fun p => u (Φ.point p)) S' ↔ ContinuousOn u S := by
  constructor
  · intro h
    have hmaps : Set.MapsTo Φ.pointInv S S' := fun p hp =>
      (hS _).2 (by rwa [Φ.point_pointInv])
    have := h.comp Φ.continuous_pointInv.continuousOn hmaps
    refine this.congr ?_
    intro p _
    simp only [Function.comp_apply, Φ.point_pointInv]
  · intro h
    exact h.comp Φ.continuous_point.continuousOn (fun p hp => (hS p).1 hp)

theorem contDiffOn_raw_iff {S S' : Set (ℝ × (PDE.Vec d × PDE.Vec d))}
    (hS : ∀ q, q ∈ S' ↔ Φ.raw q ∈ S) {g : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => g (Φ.raw q)) S' ↔ ContDiffOn ℝ (⊤ : ℕ∞) g S := by
  constructor
  · intro h
    have hmaps : Set.MapsTo Φ.rawInv S S' := fun q hq =>
      (hS _).2 (by rwa [Φ.raw_rawInv])
    have := h.comp Φ.contDiff_rawInv.contDiffOn hmaps
    refine this.congr ?_
    intro q _
    simp only [Function.comp_apply, Φ.raw_rawInv]
  · intro h
    exact h.comp Φ.contDiff_raw.contDiffOn (fun q hq => (hS q).1 hq)

/-- Second-order smoothness of the raw lift at a point, before and after the change of
variables. -/
theorem contDiffAt_raw_iff {g : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    {q : ℝ × (PDE.Vec d × PDE.Vec d)} :
    ContDiffAt ℝ 2 (fun q => g (Φ.raw q)) q ↔ ContDiffAt ℝ 2 g (Φ.raw q) := by
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_cast
  constructor
  · intro h
    have hg : ContDiffAt ℝ 2 (fun q => g (Φ.raw q)) (Φ.rawInv (Φ.raw q)) := by
      rw [Φ.rawInv_raw]
      exact h
    have := ContDiffAt.comp (Φ.raw q) hg (Φ.contDiff_rawInv.contDiffAt.of_le hle)
    have e : g = (fun q => g (Φ.raw q)) ∘ Φ.rawInv := by
      funext x
      simp only [Function.comp_apply, Φ.raw_rawInv]
    rwa [← e] at this
  · intro h
    exact h.comp q (Φ.contDiff_raw.contDiffAt.of_le hle)

variable {Ω Ω' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}

/-- **Classical solutions are transported by the change of variables.**  If the moving
domains correspond, `Ω` is open, `γ` is continuous, and the terminal data correspond
(`F' = F ∘ Φ_τ`), then `u ∘ Φ` is a classical terminal solution for the rescaled data
(`B̂`, `b̂`, `Ω'`, `γ'`, `τ`, `F'`) exactly when `u` is one for `(B, b, Ω, γ, σ₀ + a τ, F)`. -/
theorem isClassicalTerminalSolution_comp_point_iff
    (h : Φ.MapsDomain Ω γ Ω' γ') (hΩ : IsOpen Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (τ : ℝ)
    (F F' : BoundedBorel (EvolutionAmbientState d))
    (hF : ∀ x, F' x = F (Φ.ambientEquiv τ x)) (u : KineticPoint d → ℝ) :
    IsClassicalTerminalSolution Ω' γ' (Φ.coefficient B) (Φ.drift b) τ F'
        (fun p => u (Φ.point p)) ↔
      IsClassicalTerminalSolution Ω γ B b (Φ.time τ) F u := by
  have hopen := isOpen_evolutionPastInteriorRaw hΩ hγ (Φ.time τ)
  -- the individual clause transports
  have c1 : (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ evolutionPastClosedCylinder Ω' γ' τ,
        |u (Φ.point p)| ≤ C) ↔
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ evolutionPastClosedCylinder Ω γ (Φ.time τ), |u p| ≤ C) := by
    refine exists_congr fun C => and_congr_right fun _ => ?_
    exact Φ.forall_mem_iff (f := fun q => |u q| ≤ C) (h.mem_closedCylinder_iff τ)
  have c2 : ContinuousOn (fun p => u (Φ.point p)) (evolutionPastClosedCylinder Ω' γ' τ) ↔
      ContinuousOn u (evolutionPastClosedCylinder Ω γ (Φ.time τ)) :=
    Φ.continuousOn_iff (h.mem_closedCylinder_iff τ)
  have c3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => rawLift (fun p => u (Φ.point p)) q)
        (evolutionPastInteriorRaw Ω' γ' τ) ↔
      ContDiffOn ℝ (⊤ : ℕ∞) (rawLift u) (evolutionPastInteriorRaw Ω γ (Φ.time τ)) :=
    Φ.contDiffOn_raw_iff (g := rawLift u) (h.mem_interiorRaw_iff τ)
  have hnhds : ∀ p : KineticPoint d, p ∈ evolutionPastOpenCylinder Ω' γ' τ →
      evolutionPastInteriorRaw Ω γ (Φ.time τ) ∈
        nhds (rawPoint (Φ.point p)) := by
    intro p hp
    refine hopen.mem_nhds ?_
    have := (h.mem_openCylinder_iff τ p).1 hp
    exact this
  have c4 : ContDiffOn ℝ (⊤ : ℕ∞) (rawLift u) (evolutionPastInteriorRaw Ω γ (Φ.time τ)) →
      ((∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
        transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p = 0)
        ↔ ∀ p ∈ evolutionPastOpenCylinder Ω γ (Φ.time τ),
          transportedForwardOperator B b u p = 0) := by
    intro hsm
    have hop : ∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
        transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p =
          Φ.a * transportedForwardOperator B b u (Φ.point p) := by
      intro p hp
      refine transportedForwardOperator_comp_point Φ B b ?_
      exact (hsm.contDiffAt (hnhds p hp)).of_le (by norm_cast)
    have key : (∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
        transportedForwardOperator (Φ.coefficient B) (Φ.drift b) (fun p => u (Φ.point p)) p = 0)
        ↔ ∀ p ∈ evolutionPastOpenCylinder Ω' γ' τ,
          transportedForwardOperator B b u (Φ.point p) = 0 := by
      refine forall_congr' fun p => forall_congr' fun hp => ?_
      rw [hop p hp]
      exact mul_eq_zero.trans (or_iff_right Φ.a_pos.ne')
    rw [key]
    exact Φ.forall_mem_iff (f := fun q => transportedForwardOperator B b u q = 0)
      (h.mem_openCylinder_iff τ)
  have c5 : (∀ p ∈ evolutionTerminalClosure Ω' γ' τ, u (Φ.point p) = F' (p.position, p.velocity))
      ↔ ∀ p ∈ evolutionTerminalClosure Ω γ (Φ.time τ), u p = F (p.position, p.velocity) := by
    have hFp : ∀ p ∈ evolutionTerminalClosure Ω' γ' τ,
        F' (p.position, p.velocity) = F ((Φ.point p).position, (Φ.point p).velocity) := by
      intro p hp
      rw [hF]
      have hpt : p.time = τ := hp.1
      simp only [ambientEquiv_apply, point_position, point_velocity, hpt]
    rw [forall_congr' fun p => forall_congr' fun hp => by rw [hFp p hp]]
    exact Φ.forall_mem_iff
      (f := fun q => u q = F (q.position, q.velocity)) (h.mem_terminalClosure_iff τ)
  have c6 : (∀ p ∈ evolutionLateralFrontier Ω' γ' τ, u (Φ.point p) = 0) ↔
      ∀ p ∈ evolutionLateralFrontier Ω γ (Φ.time τ), u p = 0 :=
    Φ.forall_mem_iff (f := fun q => u q = 0) (h.mem_lateralFrontier_iff τ)
  unfold IsClassicalTerminalSolution
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hsm := c3.1 h3
    exact ⟨c1.1 h1, c2.1 h2, hsm, (c4 hsm).1 h4, c5.1 h5, c6.1 h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨c1.2 h1, c2.2 h2, c3.2 h3, (c4 h3).2 h4, c5.2 h5, c6.2 h6⟩

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling
