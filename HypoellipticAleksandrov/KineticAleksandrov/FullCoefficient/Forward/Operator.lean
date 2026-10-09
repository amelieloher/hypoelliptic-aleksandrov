module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Joint
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# The transported forward operator in joint coordinates

The operator `transportedForwardOperator B b` of the terminal solution theory acts on functions
of a kinetic point `⟨σ, v, z⟩`.  On functions that are smooth on an open set it is the joint
expression `∂_σ G + B : D_v² G + b(v) · ∇_z G` (`forwardRepr`), and consequently additive.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Topology

variable {d : ℕ}

/-- The forward operator `∂_σ G + B : D_v² G + b(v) · ∇_z G` of a joint function of
`(σ, (v, z))`. -/
def forwardRepr (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (G : ℝ × EvolutionAmbientState d → ℝ) (q : ℝ × EvolutionAmbientState d) : ℝ :=
  jointTimePartial G q +
    ∑ i, ∑ j, B q.1 q.2.1 q.2.2 i j * jointVelocityPartial i (jointVelocityPartial j G) q +
      ∑ i, b q.2.1 i * jointPositionPartial i G q

/-- The raw-coordinate version of a function of a kinetic point. -/
def rawOf (u : KineticPoint d → ℝ) (q : ℝ × EvolutionAmbientState d) : ℝ :=
  u ⟨q.1, q.2.1, q.2.2⟩

/-- Local smoothness of a joint function passes to its velocity partials. -/
theorem contDiffAt_jointVelocityPartial {G : ℝ × EvolutionAmbientState d → ℝ}
    {q : ℝ × EvolutionAmbientState d} (hG : ContDiffAt ℝ (⊤ : ℕ∞) G q) (i : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (jointVelocityPartial i G) q :=
  (hG.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiffAt_const

/-- On an open set of smoothness, the kinetic operator is the joint forward expression. -/
theorem transportedForwardOperator_eq_forwardRepr (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (u : KineticPoint d → ℝ)
    {O : Set (ℝ × EvolutionAmbientState d)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (rawOf u) O) (q : ℝ × EvolutionAmbientState d) (hq : q ∈ O) :
    transportedForwardOperator B b u ⟨q.1, q.2.1, q.2.2⟩ = forwardRepr B b (rawOf u) q := by
  obtain ⟨t, a, z⟩ := q
  have hAt : ∀ q' ∈ O, ContDiffAt ℝ (⊤ : ℕ∞) (rawOf u) q' :=
    fun q' h => hu.contDiffAt (hO.mem_nhds h)
  have hD : ∀ q' ∈ O, DifferentiableAt ℝ (rawOf u) q' :=
    fun q' h => (hAt q' h).differentiableAt (by simp)
  have h1 : kineticTimeDerivative u ⟨t, a, z⟩ = jointTimePartial (rawOf u) (t, (a, z)) :=
    deriv_slice_time (rawOf u) t (a, z) (hD _ hq)
  have h2 : kineticVelocityGradient u ⟨t, a, z⟩ =
      fun i => jointPositionPartial i (rawOf u) (t, (a, z)) := by
    funext i
    simp only [kineticVelocityGradient, PDE.classicalGradient_apply]
    exact fderiv_slice_position (rawOf u) t a z (hD _ hq) _
  have h3 : ∀ i j, diffusedHessian u ⟨t, a, z⟩ i j =
      jointVelocityPartial i (jointVelocityPartial j (rawOf u)) (t, (a, z)) := by
    intro i j
    have hnhds : {y' : PDE.Vec d | (t, (y', z)) ∈ O} ∈ 𝓝 a :=
      (hO.preimage (by fun_prop : Continuous fun y' : PDE.Vec d => (t, (y', z)))).mem_nhds hq
    have hev : (fun y' : PDE.Vec d => kineticPositionGradient u ⟨t, y', z⟩) =ᶠ[𝓝 a]
        fun y' => fun j => jointVelocityPartial j (rawOf u) (t, (y', z)) := by
      filter_upwards [hnhds] with y' hy'
      funext j
      simp only [kineticPositionGradient, PDE.classicalGradient_apply]
      exact fderiv_slice_velocity (rawOf u) t y' z (hD _ hy') _
    have hdj : ∀ j, DifferentiableAt ℝ
        (fun y' : PDE.Vec d => jointVelocityPartial j (rawOf u) (t, (y', z))) a := by
      intro j
      have := (contDiffAt_jointVelocityPartial (hAt _ hq) j).differentiableAt (by simp)
      exact this.comp a (by fun_prop : DifferentiableAt ℝ
        (fun y' : PDE.Vec d => ((t, (y', z)) : ℝ × EvolutionAmbientState d)) a)
    unfold diffusedHessian
    rw [hev.fderiv_eq]
    have hdiff : DifferentiableAt ℝ
        (fun y' : PDE.Vec d => fun j => jointVelocityPartial j (rawOf u) (t, (y', z))) a :=
      differentiableAt_pi.2 hdj
    rw [show (fderiv ℝ (fun y' : PDE.Vec d => fun j => jointVelocityPartial j (rawOf u)
        (t, (y', z))) a (PDE.basisVec i)) j = fderiv ℝ (fun y' : PDE.Vec d =>
        jointVelocityPartial j (rawOf u) (t, (y', z))) a (PDE.basisVec i) from by
      rw [fderiv_apply hdiff j]; rfl]
    exact fderiv_slice_velocity (jointVelocityPartial j (rawOf u)) t a z
      ((contDiffAt_jointVelocityPartial (hAt _ hq) j).differentiableAt (by simp)) _
  rw [transportedForwardOperator_apply, h1, h2]
  unfold forwardRepr matrixContraction PDE.vecDot
  simp only [fullKineticCoefficientAt_apply, h3]

/-- The joint forward expression is additive on an open set of smoothness. -/
theorem forwardRepr_sub (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    {f g : ℝ × EvolutionAmbientState d → ℝ} {O : Set (ℝ × EvolutionAmbientState d)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g O)
    (q : ℝ × EvolutionAmbientState d) (hq : q ∈ O) :
    forwardRepr B b (fun q => f q - g q) q = forwardRepr B b f q - forwardRepr B b g q := by
  have hfa : ∀ q' ∈ O, ContDiffAt ℝ (⊤ : ℕ∞) f q' := fun q' h => hf.contDiffAt (hO.mem_nhds h)
  have hga : ∀ q' ∈ O, ContDiffAt ℝ (⊤ : ℕ∞) g q' := fun q' h => hg.contDiffAt (hO.mem_nhds h)
  have hfd : ∀ q' ∈ O, DifferentiableAt ℝ f q' := fun q' h => (hfa q' h).differentiableAt (by simp)
  have hgd : ∀ q' ∈ O, DifferentiableAt ℝ g q' := fun q' h => (hga q' h).differentiableAt (by simp)
  have hv : ∀ j, ∀ q' ∈ O, jointVelocityPartial j (fun q => f q - g q) q' =
      jointVelocityPartial j f q' - jointVelocityPartial j g q' := by
    intro j q' h
    unfold jointVelocityPartial
    rw [fderiv_fun_sub (hfd _ h) (hgd _ h)]
    rfl
  have hvv : ∀ i j, jointVelocityPartial i (jointVelocityPartial j (fun q => f q - g q)) q =
      jointVelocityPartial i (jointVelocityPartial j f) q -
        jointVelocityPartial i (jointVelocityPartial j g) q := by
    intro i j
    have hev : jointVelocityPartial j (fun q => f q - g q) =ᶠ[𝓝 q]
        fun q' => jointVelocityPartial j f q' - jointVelocityPartial j g q' := by
      filter_upwards [hO.mem_nhds hq] with q' h using hv j q' h
    unfold jointVelocityPartial at hev ⊢
    rw [hev.fderiv_eq]
    have h1 := (contDiffAt_jointVelocityPartial (hfa q hq) j).differentiableAt (by simp)
    have h2 := (contDiffAt_jointVelocityPartial (hga q hq) j).differentiableAt (by simp)
    unfold jointVelocityPartial at h1 h2
    rw [fderiv_fun_sub h1 h2]
    rfl
  have ht : jointTimePartial (fun q => f q - g q) q =
      jointTimePartial f q - jointTimePartial g q := by
    unfold jointTimePartial
    rw [fderiv_fun_sub (hfd _ hq) (hgd _ hq)]
    rfl
  have hz : ∀ i, jointPositionPartial i (fun q => f q - g q) q =
      jointPositionPartial i f q - jointPositionPartial i g q := by
    intro i
    unfold jointPositionPartial
    rw [fderiv_fun_sub (hfd _ hq) (hgd _ hq)]
    rfl
  unfold forwardRepr
  simp only [ht, hvv, hz, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The transported forward operator is additive on functions smooth on an open set. -/
theorem transportedForwardOperator_sub (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (u w : KineticPoint d → ℝ)
    {O : Set (ℝ × EvolutionAmbientState d)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (rawOf u) O) (hw : ContDiffOn ℝ (⊤ : ℕ∞) (rawOf w) O)
    (q : ℝ × EvolutionAmbientState d) (hq : q ∈ O) :
    transportedForwardOperator B b (fun p => u p - w p) ⟨q.1, q.2.1, q.2.2⟩ =
      transportedForwardOperator B b u ⟨q.1, q.2.1, q.2.2⟩ -
        transportedForwardOperator B b w ⟨q.1, q.2.1, q.2.2⟩ := by
  rw [transportedForwardOperator_eq_forwardRepr B b u hO hu q hq,
    transportedForwardOperator_eq_forwardRepr B b w hO hw q hq,
    transportedForwardOperator_eq_forwardRepr B b (fun p => u p - w p) hO (hu.sub hw) q hq]
  exact forwardRepr_sub B b hO hu hw q hq

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
