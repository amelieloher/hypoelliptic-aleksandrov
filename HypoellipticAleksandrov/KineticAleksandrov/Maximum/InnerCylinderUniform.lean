module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderRetraction

/-! # Uniform convergence of the affine inner maps on fixed compact closures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter

/-- Exact epsilon formulation of uniform convergence on the original closure. -/
theorem innerRetraction_uniformly_to_identity {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2), δ < η →
        ∀ P ∈ closure (forwardCylinder Z₀ R hR),
          dist (innerRetraction Z₀ R hR δ hδ0 hδlt P) P < ε := by
  let f : ℝ → KineticPoint d → KineticPoint d := fun δ P =>
    let ρ := Real.sqrt (1 - 2 * δ / R ^ 2)
    let s := Z₀.time + δ + ρ ^ 2 * (P.time - Z₀.time)
    ⟨s, Z₀.position + (s - Z₀.time) • Z₀.velocity + ρ ^ 3 • relativePosition Z₀ P,
      Z₀.velocity + ρ • relativeVelocity Z₀ P⟩
  have hc : Continuous (Function.uncurry f) := by
    have ht : Continuous (fun q : ℝ × KineticPoint d => q.2.time) :=
      continuous_time.comp continuous_snd
    have hx : Continuous (fun q : ℝ × KineticPoint d => q.2.position) :=
      continuous_position.comp continuous_snd
    have hv : Continuous (fun q : ℝ × KineticPoint d => q.2.velocity) :=
      continuous_velocity.comp continuous_snd
    have hρ : Continuous (fun q : ℝ × KineticPoint d =>
        Real.sqrt (1 - 2 * q.1 / R^2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub
        ((continuous_const.mul continuous_fst).div_const _))
    have hs : Continuous (fun q : ℝ × KineticPoint d => Z₀.time + q.1 +
        (Real.sqrt (1 - 2 * q.1 / R^2))^2 * (q.2.time - Z₀.time)) :=
      (continuous_const.add continuous_fst).add
      ((hρ.pow 2).mul (ht.sub continuous_const))
    exact KineticPoint.continuous_mk hs
      ((continuous_const.add ((hs.sub continuous_const).smul continuous_const)).add
        ((hρ.pow 3).smul ((hx.sub continuous_const).sub
          ((ht.sub continuous_const).smul continuous_const))))
      (continuous_const.add (hρ.smul (hv.sub continuous_const)))
  have h0 : ∀ P, f 0 P = P := by
    intro P
    ext i <;> simp [f, relativePosition, relativeVelocity] <;> ring
  intro ε hε
  obtain ⟨v,hv,he⟩ := (isCompact_closure_forwardCylinder Z₀ R hR).mem_uniformity_of_prod
    (s := univ) (q := (0 : ℝ)) hc.continuousOn (mem_univ 0)
    (Metric.dist_mem_uniformity hε)
  have hv' : v ∈ nhds (0 : ℝ) := by simpa only [nhdsWithin_univ] using hv
  obtain ⟨η,hη,hηv⟩ := Metric.mem_nhds_iff.mp hv'
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη P hP
  have hdv := hηv (show δ ∈ Metric.ball 0 η by simpa [Real.dist_eq,abs_of_pos hδ0])
  have he' := he δ hdv P hP
  change dist (f δ P) (f 0 P) < ε at he'
  rw [h0] at he'
  exact he'

end HypoellipticAleksandrov.KineticAleksandrov
