module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleStrict
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleTilt
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Moving-domain comparison away from the initial time

An affine terminal perturbation reduces the weak operator inequality to strict
maximum exclusion. No derivative at the initial or terminal time is assumed.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- Moving-domain comparison at every strictly later time. -/
theorem nonpos_at_later_time_maximumClosedTube {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a b : ℝ}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ}
    (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω))
    (hγ : ContinuousOn γ (Icc a b))
    (hu : ContinuousOn u (maximumClosedTube Ω γ a b))
    (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b))
    (hreg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : ∀ p ∈ maximumOpenTube Ω γ a b,
      (B p.time p.position p.velocity).PosSemidef)
    (hsub : ∀ p ∈ maximumOpenTube Ω γ a b, 0 ≤ transportedForwardOperator B drift u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ a b, p.time = b → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ a b,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0)
    {q : KineticPoint d} (hq : q ∈ maximumClosedTube Ω γ a b) (ht : a < q.time) :
    u q ≤ 0 := by
  by_cases hqb : q.time = b
  · exact hterminal q hq hqb
  have hqt : q.time < b := lt_of_le_of_ne hq.1.2 hqb
  by_contra hnot
  have hpos : 0 < u q := lt_of_not_ge hnot
  let ε : ℝ := u q / (2 * (b - q.time))
  have hε : 0 < ε := div_pos hpos (mul_pos (by norm_num) (sub_pos.mpr hqt))
  let w := maximumTerminalTilt u ε b
  have hwle : ∀ p ∈ maximumClosedTube Ω γ a b, w p ≤ u p := by
    intro p hp
    exact sub_le_self _ (mul_nonneg hε.le (sub_nonneg.mpr hp.1.2))
  have hwCont : ContinuousOn w (maximumClosedTube Ω γ a b) :=
    hu.sub (continuousOn_const.mul (continuousOn_const.sub continuous_time.continuousOn))
  have hwControl : IsTransportIndependentOn w (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn w (maximumClosedTube Ω γ a b) := by
    rcases hcontrol with hi | hn
    · left
      intro p hp z
      dsimp [w, maximumTerminalTilt]
      rw [hi p hp z]
    · right
      intro M
      obtain ⟨R, hR, hb⟩ := hn M
      exact ⟨R, hR, fun p hp hz => (hwle p hp).trans (hb p hp hz)⟩
  have hwReg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => w ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => w ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => w ⟨p.time, p.position, z⟩) p.velocity := by
    intro p hp
    obtain ⟨ht, hv, hz⟩ := hreg p hp
    dsimp only [w, maximumTerminalTilt]
    refine ⟨?_, hv.sub contDiffAt_const, hz.sub_const (ε * (b - p.time))⟩
    exact ht.sub ((differentiableAt_const ε).mul
      ((differentiableAt_const b).sub differentiableAt_id))
  have hwStrict : ∀ p ∈ maximumOpenTube Ω γ a b,
      0 < transportedForwardOperator B drift w p := by
    intro p hp
    rw [transportedForwardOperator_maximumTerminalTilt B drift (hreg p hp).1]
    exact add_pos_of_nonneg_of_pos (hsub p hp) hε
  have hresult := nonpos_on_inset_maximumClosedTube_of_strict hΩ hcΩ
    (show a < (a + q.time) / 2 by linarith) hγ hwCont hwControl hwReg hB hwStrict
    (fun p hp heq => (hwle p hp).trans (hterminal p hp heq))
    (fun p hp hf => (hwle p hp).trans (hlateral p hp hf))
    q ⟨⟨by linarith, hq.1.2⟩, hq.2⟩
  have heq : ε * (b - q.time) = u q / 2 := by
    dsimp [ε]
    field_simp
  change u q - ε * (b - q.time) ≤ 0 at hresult
  rw [heq] at hresult
  linarith


/-- Moving-domain comparison on the entire closed time slab, including its initial slice. -/
theorem nonpos_on_maximumClosedTube {d : ℕ}
    {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} {a b : ℝ}
    {B : FullKineticCoefficient d} {drift : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ}
    (hab : a < b) (hΩ : IsOpen Ω) (hcΩ : IsCompact (closure Ω))
    (hγ : ContinuousOn γ (Icc a b))
    (hu : ContinuousOn u (maximumClosedTube Ω γ a b))
    (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b))
    (hreg : ∀ p ∈ maximumOpenTube Ω γ a b,
      DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time ∧
      ContDiffAt ℝ 2 (fun v => u ⟨p.time, v, p.velocity⟩) p.position ∧
      DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : ∀ p ∈ maximumOpenTube Ω γ a b,
      (B p.time p.position p.velocity).PosSemidef)
    (hsub : ∀ p ∈ maximumOpenTube Ω γ a b, 0 ≤ transportedForwardOperator B drift u p)
    (hterminal : ∀ p ∈ maximumClosedTube Ω γ a b, p.time = b → u p ≤ 0)
    (hlateral : ∀ p ∈ maximumClosedTube Ω γ a b,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p ≤ 0)
 :
    ∀ q ∈ maximumClosedTube Ω γ a b, u q ≤ 0 := by
  intro q hq
  have hlater : ∀ {p : KineticPoint d}, p ∈ maximumClosedTube Ω γ a b →
      a < p.time → u p ≤ 0 :=
    fun {_} => nonpos_at_later_time_maximumClosedTube hΩ hcΩ hγ hu hcontrol
      hreg hB hsub hterminal hlateral
  by_cases hqa : q.time = a
  · let f : ℝ → KineticPoint d :=
      fun t => ⟨t, q.position - γ a + γ t, q.velocity⟩
    have hf : ContinuousOn f (Icc a b) := by
      change ContinuousOn ((KineticPoint.homeomorphProd d).symm ∘
        (fun t => (t, (q.position - γ a + γ t, q.velocity)))) _
      exact (KineticPoint.homeomorphProd d).symm.continuous.comp_continuousOn
        (continuousOn_id.prodMk ((continuousOn_const.add hγ).prodMk continuousOn_const))
    have hfmem : ∀ t ∈ Icc a b, f t ∈ maximumClosedTube Ω γ a b := by
      intro t ht
      refine ⟨ht, ?_⟩
      rw [mem_closure_movingDomain_iff]
      have hv := (mem_closure_movingDomain_iff Ω γ q.time q.position).mp hq.2
      simpa only [f, add_sub_cancel_right, hqa] using hv
    have hfc : ContinuousWithinAt (u ∘ f) (Icc a b) a :=
      (hu.comp hf hfmem) a ⟨le_rfl, hab.le⟩
    have haClosure : a ∈ closure (Ioc a b) := by
      rw [closure_Ioc hab.ne]
      exact ⟨le_rfl, hab.le⟩
    have hbound : (u ∘ f) a ≤ (0 : ℝ) :=
      (hfc.mono Ioc_subset_Icc_self).closure_le haClosure continuousWithinAt_const
        (fun t ht => hlater (hfmem t ⟨ht.1.le, ht.2⟩) ht.1)
    have hfa : f a = q := by
      simp only [f, sub_add_cancel, ← hqa]
    simpa only [Function.comp_apply, hfa] using hbound
  · exact hlater hq (lt_of_le_of_ne hq.1.1 (Ne.symm hqa))

end HypoellipticAleksandrov.KineticAleksandrov.Decay
