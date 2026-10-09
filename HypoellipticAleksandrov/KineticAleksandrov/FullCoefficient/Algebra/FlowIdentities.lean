module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.GammaCauchySchwarz
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.FlowCore
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Flow identities, pointwise function versions

The flow identities. Fix `lam > 0` and a flow parameter
`h₀`. For `r, j : ℝ → EvolutionAmbientState d → ℝ` with `r h₀`, `j h₀` of class `C²`, `r h₀ > 0`,
and `∂_h r = M^h : D² r`, `∂_h j = M^h : D² j` at the point `(h₀, y)`:

* `power_identity` is the power identity;
* `coef_inequality` is the coefficient identity for one entry `β = j / r`.

The right-hand sides use `flowGamma lam h₀ F F y = Mform lam h₀ ∇_zF ∇_vF`
(`flowGamma_self`), i.e. the `M^h`-norm of the gradient.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- Derivative of the first derivative of `x ↦ x^q` at a positive point. -/
theorem hasDerivAt_rpow_deriv {x : ℝ} (hx : 0 < x) (q : ℝ) :
    HasDerivAt (fun x : ℝ => q * x ^ (q - 1)) (q * (q - 1) * x ^ (q - 2)) x := by
  have h := (Real.hasDerivAt_rpow_const (p := q - 1) (Or.inl hx.ne')).const_mul q
  convert h using 1
  rw [show q - 1 - 1 = q - 2 by ring]
  ring

/-- The power identity: `-(∂_h - M:D²) r^q = q(q-1) r^{q-2} |Dr|²_M`, pointwise. -/
theorem power_identity (lam h₀ q : ℝ) (r : ℝ → EvolutionAmbientState d → ℝ)
    (hr2 : ContDiff ℝ 2 (r h₀)) (hpos : ∀ y', 0 < r h₀ y') (y : EvolutionAmbientState d)
    (ht : HasDerivAt (fun h => r h y) (flowL lam h₀ (r h₀) y) h₀) :
    -(deriv (fun h => r h y ^ q) h₀ - flowL lam h₀ (fun y' => r h₀ y' ^ q) y)
      = q * (q - 1) * r h₀ y ^ (q - 2) * flowGamma lam h₀ (r h₀) (r h₀) y := by
  have hφ : ∀ y', HasDerivAt (fun x : ℝ => x ^ q) (q * r h₀ y' ^ (q - 1)) (r h₀ y') :=
    fun y' => Real.hasDerivAt_rpow_const (Or.inl (hpos y').ne')
  have hL : flowL lam h₀ (fun y' => r h₀ y' ^ q) y
      = q * r h₀ y ^ (q - 1) * flowL lam h₀ (r h₀) y
        + q * (q - 1) * r h₀ y ^ (q - 2) * flowGamma lam h₀ (r h₀) (r h₀) y :=
    flowL_comp (φ := fun x : ℝ => x ^ q) (φ' := fun x : ℝ => q * x ^ (q - 1))
      (φ'' := fun x : ℝ => q * (q - 1) * x ^ (q - 2)) hr2 hφ y
      (hasDerivAt_rpow_deriv (hpos y) q) lam h₀
  have hT := ht.rpow_const (p := q) (Or.inl (hpos y).ne')
  rw [hT.deriv, hL]
  ring

/-- The coefficient identity, one entry: with `β = j / r`,
`r^q |Dβ|²_M ≤ -(∂_h - M:D²)(r^q β²)`, pointwise, for `1 < q ≤ 4/3`. -/
theorem coef_inequality {lam : ℝ} (hlam : 0 < lam) (h₀ q : ℝ) (hq1 : 1 < q) (hq2 : q ≤ 4 / 3)
    (r j : ℝ → EvolutionAmbientState d → ℝ)
    (hr2 : ContDiff ℝ 2 (r h₀)) (hj2 : ContDiff ℝ 2 (j h₀)) (hpos : ∀ y', 0 < r h₀ y')
    (y : EvolutionAmbientState d)
    (htr : HasDerivAt (fun h => r h y) (flowL lam h₀ (r h₀) y) h₀)
    (htj : HasDerivAt (fun h => j h y) (flowL lam h₀ (j h₀) y) h₀) :
    r h₀ y ^ q * flowGamma lam h₀ (fun y' => j h₀ y' / r h₀ y')
        (fun y' => j h₀ y' / r h₀ y') y
      ≤ -(deriv (fun h => r h y ^ q * (j h y / r h y) ^ 2) h₀
          - flowL lam h₀ (fun y' => r h₀ y' ^ q * (j h₀ y' / r h₀ y') ^ 2) y) := by
  set B : EvolutionAmbientState d → ℝ := fun y' => j h₀ y' / r h₀ y' with hBdef
  have hne : ∀ y', r h₀ y' ≠ 0 := fun y' => (hpos y').ne'
  have hB : ContDiff ℝ 2 B := hj2.div hr2 hne
  have hP : ContDiff ℝ 2 (fun y' => r h₀ y' ^ q) := hr2.rpow_const_of_ne hne
  have hBB : ContDiff ℝ 2 (fun y' => B y' * B y') := hB.mul hB
  have hjfun : (fun y' => r h₀ y' * B y') = j h₀ := by
    funext y'; simp only [hBdef]; exact mul_div_cancel₀ _ (hne y')
  have hJ : j h₀ y = r h₀ y * B y := by
    have := congrFun hjfun y; exact this.symm
  have jrel : flowL lam h₀ (j h₀) y
      = r h₀ y * flowL lam h₀ B y + B y * flowL lam h₀ (r h₀) y
        + 2 * flowGamma lam h₀ (r h₀) B y := by
    have := flowL_mul hr2 hB lam h₀ y
    rw [hjfun] at this
    exact this
  have hφ : ∀ y', HasDerivAt (fun x : ℝ => x ^ q) (q * r h₀ y' ^ (q - 1)) (r h₀ y') :=
    fun y' => Real.hasDerivAt_rpow_const (Or.inl (hne y'))
  have hLP : flowL lam h₀ (fun y' => r h₀ y' ^ q) y
      = q * r h₀ y ^ (q - 1) * flowL lam h₀ (r h₀) y
        + q * (q - 1) * r h₀ y ^ (q - 2) * flowGamma lam h₀ (r h₀) (r h₀) y :=
    flowL_comp (φ := fun x : ℝ => x ^ q) (φ' := fun x : ℝ => q * x ^ (q - 1))
      (φ'' := fun x : ℝ => q * (q - 1) * x ^ (q - 2)) hr2 hφ y
      (hasDerivAt_rpow_deriv (hpos y) q) lam h₀
  have hLBB : flowL lam h₀ (fun y' => B y' * B y') y
      = B y * flowL lam h₀ B y + B y * flowL lam h₀ B y + 2 * flowGamma lam h₀ B B y :=
    flowL_mul hB hB lam h₀ y
  have hGPB : flowGamma lam h₀ (fun y' => r h₀ y' ^ q) B y
      = q * r h₀ y ^ (q - 1) * flowGamma lam h₀ (r h₀) B y :=
    flowGamma_comp_left (φ := fun x : ℝ => x ^ q) (φ' := fun x : ℝ => q * x ^ (q - 1))
      hr2 hφ lam h₀ y
  have hGPBB : flowGamma lam h₀ (fun y' => r h₀ y' ^ q) (fun y' => B y' * B y') y
      = B y * flowGamma lam h₀ (fun y' => r h₀ y' ^ q) B y
        + B y * flowGamma lam h₀ (fun y' => r h₀ y' ^ q) B y :=
    flowGamma_mul_right hB hB lam h₀ y
  have hfun : (fun y' => r h₀ y' ^ q * (j h₀ y' / r h₀ y') ^ 2)
      = fun y' => (r h₀ y' ^ q) * (B y' * B y') := by
    funext y'; simp only [hBdef]; ring
  have hLfull : flowL lam h₀ (fun y' => r h₀ y' ^ q * (j h₀ y' / r h₀ y') ^ 2) y
      = r h₀ y ^ q * flowL lam h₀ (fun y' => B y' * B y') y
        + B y * B y * flowL lam h₀ (fun y' => r h₀ y' ^ q) y
        + 2 * flowGamma lam h₀ (fun y' => r h₀ y' ^ q) (fun y' => B y' * B y') y := by
    rw [hfun]; exact flowL_mul hP hBB lam h₀ y
  have hBt : HasDerivAt (fun h => j h y / r h y)
      ((flowL lam h₀ (j h₀) y * r h₀ y - j h₀ y * flowL lam h₀ (r h₀) y) / r h₀ y ^ 2) h₀ :=
    htj.div htr (hne y)
  have hT := (htr.rpow_const (p := q) (Or.inl (hne y))).mul (hBt.pow 2)
  have hTd : deriv (fun h => r h y ^ q * (j h y / r h y) ^ 2) h₀ = _ := hT.deriv
  obtain ⟨hs1, hs2⟩ := rpow_split (hpos y) q
  have hRne := hne y
  have hBy : j h₀ y / r h₀ y = B y := rfl
  have hcore := coef_core (β := B y) (Γrr := flowGamma lam h₀ (r h₀) (r h₀) y)
    (Γrb := flowGamma lam h₀ (r h₀) B y) (Γbb := flowGamma lam h₀ B B y) hq1 hq2 (hpos y)
    (flowGamma_self_nonneg hlam _ _) (flowGamma_self_nonneg hlam _ _)
    (flowGamma_sq_le hlam _ _ _)
  rw [hTd, hLfull, hLBB, hLP, hGPBB, hGPB, jrel]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  rw [hJ]
  simp only [hs1, hs2] at hcore ⊢
  field_simp
  linarith [hcore]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
