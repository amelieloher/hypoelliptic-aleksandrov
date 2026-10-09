module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz

/-!
# Germ-local time--velocity multi-index calculus

This module proves the pointwise product and successor-coordinate rules from
finite `ContDiffAt` hypotheses. Its auxiliary directional and block evaluators
are private proof devices; the public derivative remains `coordinateIteratedFDeriv`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d : ℕ}

private def localRepDirs (v : E) : ℕ → (E → ℝ) → E → ℝ
  | 0, f => f
  | n + 1, f => fun z => fderiv ℝ (localRepDirs v n f) z v

private theorem localRepDirs_contDiffAt (v : E) (n m : ℕ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (m + n) f z) : ContDiffAt ℝ m (localRepDirs v n f) z := by
  induction n generalizing m f with
  | zero => simpa [localRepDirs] using hf
  | succ n ih =>
      rw [localRepDirs]
      have h : ContDiffAt ℝ (m + 1) (localRepDirs v n f) z := by
        apply ih
        simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
      exact (h.fderiv_right (by norm_num)).clm_apply contDiffAt_const

private theorem localRepDirs_mul_range (v : E) (n : ℕ) (f g : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ n f z) (hg : ContDiffAt ℝ n g z) :
    localRepDirs v n (fun x => f x * g x) z =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) *
        (localRepDirs v k f z * localRepDirs v (n - k) g z) := by
  classical
  induction n generalizing f g z with
  | zero => simp [localRepDirs]
  | succ n ih =>
      rw [localRepDirs]
      have hfun : localRepDirs v n (fun x => f x * g x) =ᶠ[nhds z] fun x =>
          ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) *
            (localRepDirs v k f x * localRepDirs v (n - k) g x) := by
        filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with x hfx hgx
        exact ih f g x (hfx.of_le (by simp)) (hgx.of_le (by simp))
      change (fderiv ℝ (localRepDirs v n (fun x => f x * g x)) z) v = _
      rw [hfun.fderiv_eq]
      have hdf : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (localRepDirs v k f) z := by
        intro k hk
        exact (localRepDirs_contDiffAt v k 1 f z (hf.of_le (by
          exact_mod_cast (show 1 + k ≤ n + 1 by
            have := Finset.mem_range.mp hk
            omega)))).differentiableAt (by norm_num)
      have hdg : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (localRepDirs v (n - k) g) z := by
        intro k hk
        exact (localRepDirs_contDiffAt v (n-k) 1 g z (hg.of_le (by
          exact_mod_cast (show 1 + (n-k) ≤ n + 1 by omega)))).differentiableAt (by norm_num)
      change (fderiv ℝ (fun x => ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) *
          (localRepDirs v k f x * localRepDirs v (n - k) g x)) z) v = _
      rw [fderiv_fun_sum]
      · simp only [ContinuousLinearMap.sum_apply]
        have hterm : ∀ k ∈ Finset.range (n + 1),
            (fderiv ℝ (fun x => (Nat.choose n k : ℝ) *
              (localRepDirs v k f x * localRepDirs v (n-k) g x)) z) v =
              (Nat.choose n k : ℝ) *
                (localRepDirs v k f z * localRepDirs v (n-k+1) g z +
                 localRepDirs v (k+1) f z * localRepDirs v (n-k) g z) := by
          intro k hk
          change (fderiv ℝ (fun x => (Nat.choose n k : ℝ) *
            ((localRepDirs v k f * localRepDirs v (n-k) g) x)) z) v = _
          rw [fderiv_const_mul ((hdf k hk).mul (hdg k hk)) (Nat.choose n k : ℝ)]
          change ((Nat.choose n k : ℝ) •
            fderiv ℝ (fun y => localRepDirs v k f y * localRepDirs v (n-k) g y) z) v = _
          rw [fderiv_fun_mul (hdf k hk) (hdg k hk)]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul, localRepDirs]
          ring
        rw [Finset.sum_congr rfl hterm]
        rw [Finset.sum_choose_succ_mul
          (f := fun i j => localRepDirs v i f z * localRepDirs v j g z) n]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have heq : n - k + 1 = n + 1 - k := by omega
        rw [heq]
        ring
      · intro k hk
        have hf1 := localRepDirs_contDiffAt v k 1 f z (hf.of_le (by
          exact_mod_cast (show 1 + k ≤ n + 1 by
            have := Finset.mem_range.mp hk
            omega)))
        have hg1 := localRepDirs_contDiffAt v (n-k) 1 g z (hg.of_le (by
          exact_mod_cast (show 1 + (n-k) ≤ n + 1 by omega)))
        exact (contDiffAt_const.mul (hf1.mul hg1)).differentiableAt (by norm_num)

private theorem localRepDirs_mul_binomial (v : E) (n : ℕ) (f g : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ n f z) (hg : ContDiffAt ℝ n g z) :
    localRepDirs v n (fun x => f x * g x) z =
      ∑ k : Fin (n + 1), (Nat.choose n k : ℝ) *
        localRepDirs v k f z * localRepDirs v (n - k) g z := by
  rw [localRepDirs_mul_range v n f g z hf hg]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem localRepDirs_smul (v : E) (n : ℕ) (a : ℝ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ n f z) :
    localRepDirs v n (fun x => a * f x) z = a * localRepDirs v n f z := by
  induction n generalizing f z with
  | zero => rfl
  | succ n ih =>
      rw [localRepDirs]
      have hfun : localRepDirs v n (fun x => a * f x) =ᶠ[nhds z]
          fun x => a * localRepDirs v n f x := by
        filter_upwards [hf.eventually (by simp)] with x hfx
        exact ih f x (hfx.of_le (by simp))
      change (fderiv ℝ (localRepDirs v n (fun x => a * f x)) z) v = _
      rw [hfun.fderiv_eq]
      have hd := (localRepDirs_contDiffAt v n 1 f z
        (by simpa [add_comm] using hf)).differentiableAt (by norm_num)
      simpa only [localRepDirs, Pi.smul_def, smul_eq_mul, ContinuousLinearMap.smul_apply] using
        congrArg (fun L : E →L[ℝ] ℝ => L v) (fderiv_const_smul hd a)

private theorem localRepDirs_eq_iteratedFDeriv (v : E) (n : ℕ)
    (G : E → ℝ) (z : E) (hG : ContDiffAt ℝ n G z) :
    localRepDirs v n G z = iteratedFDeriv ℝ n G z (fun _ => v) := by
  induction n generalizing G z with
  | zero => simp [localRepDirs]
  | succ n ih =>
      rw [localRepDirs, iteratedFDeriv_succ_apply_left]
      have heq : localRepDirs v n G =ᶠ[nhds z]
          fun y => iteratedFDeriv ℝ n G y (fun _ => v) := by
        filter_upwards [hG.eventually (by simp)] with y hy
        exact ih G y (hy.of_le (show (n : WithTop ℕ∞) ≤ n + 1 by simp))
      change (fderiv ℝ (localRepDirs v n G) z) v = _
      rw [heq.fderiv_eq]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n G) z :=
        hG.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
      rw [fderiv_continuousMultilinear_apply_const_apply hd]
      rfl

private theorem localRepDirs_congr (v : E) (n : ℕ) {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ n f z) (hg : ContDiffAt ℝ n g z) (hfg : f =ᶠ[nhds z] g) :
    localRepDirs v n f z = localRepDirs v n g z := by
  rw [localRepDirs_eq_iteratedFDeriv v n f z hf,
    localRepDirs_eq_iteratedFDeriv v n g z hg]
  exact congrArg (fun L => L (fun _ => v))
    (hfg.iteratedFDeriv ℝ n).self_of_nhds

private theorem localRepDirs_sum {A : Type*} [Fintype A] (v : E) (n : ℕ)
    (F : A → E → ℝ) (z : E) (hF : ∀ a, ContDiffAt ℝ n (F a) z) :
    localRepDirs v n (fun x => ∑ a, F a x) z = ∑ a, localRepDirs v n (F a) z := by
  classical
  rw [localRepDirs_eq_iteratedFDeriv v n _ z (ContDiffAt.sum fun a _ => hF a)]
  have hsum : iteratedFDeriv ℝ n (fun x => ∑ a, F a x) z =
      ∑ a, iteratedFDeriv ℝ n (F a) z := by
    simpa [iteratedFDerivWithin_univ, Finset.sum_fn] using
      (iteratedFDerivWithin_sum_apply (s := Set.univ) uniqueDiffOn_univ
        (Set.mem_univ z) (u := Finset.univ) (fun a _ => (hF a).contDiffWithinAt))
  rw [hsum]
  simp only [ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [localRepDirs_eq_iteratedFDeriv v n (F a) z (hF a)]

private def LocalBlockSplit {C : Type*} (beta : C → ℕ) : List C → Type
  | [] => PUnit
  | c :: cs => Fin (beta c + 1) × LocalBlockSplit beta cs

private instance {C : Type*} (beta : C → ℕ) (cs : List C) :
    Fintype (LocalBlockSplit beta cs) := by
  induction cs with
  | nil => simp [LocalBlockSplit]; infer_instance
  | cons c cs ih => simp [LocalBlockSplit]; infer_instance

private def localBlockOrder {C : Type*} (beta : C → ℕ) (cs : List C) : ℕ :=
  (cs.map beta).sum

private def localBlockDirs {C : Type*} (basis : C → E) (beta : C → ℕ) :
    List C → (E → ℝ) → E → ℝ
  | [], f => f
  | c :: cs, f => localRepDirs (basis c) (beta c) (localBlockDirs basis beta cs f)

private def localBlockLeft {C : Type*} (basis : C → E) (beta : C → ℕ) :
    (cs : List C) → LocalBlockSplit beta cs → (E → ℝ) → E → ℝ
  | [], _, f => f
  | c :: cs, (k,a), f => localRepDirs (basis c) k (localBlockLeft basis beta cs a f)

private def localBlockRight {C : Type*} (basis : C → E) (beta : C → ℕ) :
    (cs : List C) → LocalBlockSplit beta cs → (E → ℝ) → E → ℝ
  | [], _, f => f
  | c :: cs, (k,a), f => localRepDirs (basis c) (beta c-k)
      (localBlockRight basis beta cs a f)

private def localBlockCoeff {C : Type*} (beta : C → ℕ) :
    (cs : List C) → LocalBlockSplit beta cs → ℕ
  | [], _ => 1
  | c :: cs, (k,a) => Nat.choose (beta c) k * localBlockCoeff beta cs a

private theorem sum_localBlockSplit_cons {C : Type*} (beta : C → ℕ) (c : C)
    (cs : List C) (F : LocalBlockSplit beta (c :: cs) → ℝ) :
    (∑ a, F a) = ∑ k : Fin (beta c + 1), ∑ a : LocalBlockSplit beta cs, F (k,a) := by
  exact Fintype.sum_prod_type F

private theorem localBlockDirs_contDiffAt {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (m : ℕ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (m + localBlockOrder beta cs) f z) :
    ContDiffAt ℝ m (localBlockDirs basis beta cs f) z := by
  induction cs generalizing m f with
  | nil => simpa [localBlockDirs, localBlockOrder] using hf
  | cons c cs ih =>
      rw [localBlockDirs]
      apply localRepDirs_contDiffAt
      apply ih
      simpa [localBlockOrder, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf

private theorem localBlockLeft_contDiffAt {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (a : LocalBlockSplit beta cs) (m : ℕ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (m + localBlockOrder beta cs) f z) :
    ContDiffAt ℝ m (localBlockLeft basis beta cs a f) z := by
  induction cs generalizing m f with
  | nil => simpa [localBlockLeft, localBlockOrder] using hf
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockLeft]
      apply localRepDirs_contDiffAt
      apply ih
      apply hf.of_le
      exact_mod_cast (show m + k + localBlockOrder beta cs ≤
        m + localBlockOrder beta (c::cs) by simp [localBlockOrder]; omega)

private theorem localBlockRight_contDiffAt {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (a : LocalBlockSplit beta cs) (m : ℕ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (m + localBlockOrder beta cs) f z) :
    ContDiffAt ℝ m (localBlockRight basis beta cs a f) z := by
  induction cs generalizing m f with
  | nil => simpa [localBlockRight, localBlockOrder] using hf
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockRight]
      apply localRepDirs_contDiffAt
      apply ih
      apply hf.of_le
      exact_mod_cast (show m + (beta c-k) + localBlockOrder beta cs ≤
        m + localBlockOrder beta (c::cs) by simp [localBlockOrder]; omega)

private theorem localBlockDirs_mul {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (f g : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (localBlockOrder beta cs) f z)
    (hg : ContDiffAt ℝ (localBlockOrder beta cs) g z) :
    localBlockDirs basis beta cs (fun x => f x * g x) z =
      ∑ a : LocalBlockSplit beta cs, (localBlockCoeff beta cs a : ℝ) *
        localBlockLeft basis beta cs a f z * localBlockRight basis beta cs a g z := by
  classical
  induction cs generalizing f g z with
  | nil => simp [localBlockDirs, LocalBlockSplit, localBlockCoeff,
      localBlockLeft, localBlockRight]
  | cons c cs ih =>
      rw [localBlockDirs]
      have hfun : localBlockDirs basis beta cs (fun x => f x * g x) =ᶠ[nhds z]
          fun x => ∑ a : LocalBlockSplit beta cs, (localBlockCoeff beta cs a : ℝ) *
            (localBlockLeft basis beta cs a f x * localBlockRight basis beta cs a g x) := by
        filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with x hfx hgx
        simpa [mul_assoc] using ih f g x
          (hfx.of_le (by simp [localBlockOrder])) (hgx.of_le (by simp [localBlockOrder]))
      have hsource : ContDiffAt ℝ (beta c)
          (localBlockDirs basis beta cs (fun x => f x * g x)) z :=
        localBlockDirs_contDiffAt basis beta cs (beta c) _ z
          (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hf.mul hg)
      have htarget : ContDiffAt ℝ (beta c) (fun x =>
          ∑ a : LocalBlockSplit beta cs, (localBlockCoeff beta cs a : ℝ) *
            (localBlockLeft basis beta cs a f x * localBlockRight basis beta cs a g x)) z :=
        ContDiffAt.sum fun a _ => contDiffAt_const.mul
          ((localBlockLeft_contDiffAt basis beta cs a (beta c) f z
            (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hf)).mul
           (localBlockRight_contDiffAt basis beta cs a (beta c) g z
            (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hg)))
      rw [localRepDirs_congr (basis c) (beta c) hsource htarget hfun]
      rw [localRepDirs_sum]
      · rw [Finset.sum_congr rfl (fun a _ =>
          localRepDirs_smul (basis c) (beta c) (localBlockCoeff beta cs a : ℝ)
            (fun x => localBlockLeft basis beta cs a f x *
              localBlockRight basis beta cs a g x) z
            ((localBlockLeft_contDiffAt basis beta cs a (beta c) f z
              (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hf)).mul
             (localBlockRight_contDiffAt basis beta cs a (beta c) g z
              (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hg))))]
        rw [Finset.sum_congr rfl (fun a _ => congrArg
          (fun q => (localBlockCoeff beta cs a : ℝ) * q)
          (localRepDirs_mul_binomial (basis c) (beta c)
            (localBlockLeft basis beta cs a f)
            (localBlockRight basis beta cs a g) z
            (localBlockLeft_contDiffAt basis beta cs a (beta c) f z
              (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hf))
            (localBlockRight_contDiffAt basis beta cs a (beta c) g z
              (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hg))))]
        rw [sum_localBlockSplit_cons, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        change (localBlockCoeff beta cs k : ℝ) *
          (∑ j : Fin (beta c + 1), (Nat.choose (beta c) j : ℝ) *
            localRepDirs (basis c) j (localBlockLeft basis beta cs k f) z *
            localRepDirs (basis c) (beta c-j) (localBlockRight basis beta cs k g) z) = _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [localBlockCoeff, localBlockLeft, localBlockRight, Nat.cast_mul]
        ring
      · intro a
        exact contDiffAt_const.mul
          ((localBlockLeft_contDiffAt basis beta cs a (beta c) f z
            (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hf)).mul
           (localBlockRight_contDiffAt basis beta cs a (beta c) g z
            (by simpa [localBlockOrder, add_comm, add_left_comm, add_assoc] using hg)))

private def localSplitToFun {C : Type*} (beta : C → ℕ) :
    (cs : List C) → LocalBlockSplit beta cs → (i : Fin cs.length) → Fin (beta (cs.get i) + 1)
  | [], _, i => Fin.elim0 i
  | _ :: cs, (k,a), i => Fin.cases k (localSplitToFun beta cs a) i

private theorem localSplitToFun_cons_zero {C : Type*} (beta : C → ℕ)
    (c : C) (cs : List C) (k : Fin (beta c + 1)) (a : LocalBlockSplit beta cs) :
    localSplitToFun beta (c :: cs) (k, a) 0 = k := by
  rfl

private theorem localSplitToFun_cons_succ {C : Type*} (beta : C → ℕ)
    (c : C) (cs : List C) (k : Fin (beta c + 1)) (a : LocalBlockSplit beta cs)
    (i : Fin cs.length) :
    localSplitToFun beta (c :: cs) (k, a) i.succ = localSplitToFun beta cs a i := by
  rfl

private def funToLocalSplit {C : Type*} (beta : C → ℕ) :
    (cs : List C) → ((i : Fin cs.length) → Fin (beta (cs.get i) + 1)) → LocalBlockSplit beta cs
  | [], _ => PUnit.unit
  | _ :: cs, f => (f ⟨0, by simp⟩, funToLocalSplit beta cs fun i => f i.succ)

private theorem funToLocalSplit_toFun {C : Type*} (beta : C → ℕ)
    (cs : List C) (a : LocalBlockSplit beta cs) :
    funToLocalSplit beta cs (localSplitToFun beta cs a) = a := by
  induction cs with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      simp only [funToLocalSplit, localSplitToFun]
      exact congrArg (fun x => (k,x)) (ih a)

private theorem localSplitToFun_toLocalSplit {C : Type*} (beta : C → ℕ)
    (cs : List C) (f : (i : Fin cs.length) → Fin (beta (cs.get i) + 1)) :
    localSplitToFun beta cs (funToLocalSplit beta cs f) = f := by
  induction cs with
  | nil => funext i; exact Fin.elim0 i
  | cons c cs ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [funToLocalSplit, localSplitToFun, Fin.cases]
        rfl
      · change localSplitToFun beta cs
          (funToLocalSplit beta cs (fun i => f i.succ)) j = f j.succ
        rw [ih]

private def localSplitEquivPi {C : Type*} (beta : C → ℕ) (cs : List C) :
    LocalBlockSplit beta cs ≃ ((i : Fin cs.length) → Fin (beta (cs.get i) + 1)) where
  toFun := localSplitToFun beta cs
  invFun := funToLocalSplit beta cs
  left_inv := funToLocalSplit_toFun beta cs
  right_inv := localSplitToFun_toLocalSplit beta cs

private def localCoordinateEquiv (d : ℕ) :
    Fin (Finset.univ.toList : List (TimeVelocityCoord d)).length ≃ TimeVelocityCoord d :=
  List.Nodup.getEquivOfForallMemList _
    (Finset.nodup_toList (Finset.univ : Finset (TimeVelocityCoord d))) (by simp)

private def localBlockSplitEquivSplit (beta : TimeVelocityMultiIndex d) :
    LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)) ≃ Split beta :=
  (localSplitEquivPi beta _).trans
    (Equiv.piCongrLeft (fun c => Fin (beta c + 1)) (localCoordinateEquiv d))

private theorem sum_localBlockSplit_eq_sum_split (beta : TimeVelocityMultiIndex d)
    (F : Split beta → ℝ) :
    ∑ a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)),
        F (localBlockSplitEquivSplit beta a) = ∑ gamma : Split beta, F gamma := by
  exact Equiv.sum_comp (localBlockSplitEquivSplit beta) F

private theorem localBlockCoeff_eq_prod {C : Type*} [Fintype C]
    (beta : C → ℕ) (cs : List C) (a : LocalBlockSplit beta cs) :
    localBlockCoeff beta cs a = ∏ i : Fin cs.length,
      Nat.choose (beta (cs.get i)) (localSplitToFun beta cs a i) := by
  induction cs with
  | nil => cases a; simp [localBlockCoeff]
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockCoeff]
      change Nat.choose (beta c) k * localBlockCoeff beta cs a =
        ∏ i : Fin (cs.length + 1), Nat.choose (beta ((c :: cs).get i))
          (localSplitToFun beta (c :: cs) (k,a) i)
      rw [Fin.prod_univ_succ]
      simp only [localSplitToFun_cons_zero, localSplitToFun_cons_succ,
        List.get_cons_zero]
      rw [ih]
      congr 1

private theorem localBlockCoeff_eq_choose (beta : TimeVelocityMultiIndex d)
    (a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d))) :
    localBlockCoeff beta _ a = beta.choose (localBlockSplitEquivSplit beta a).left := by
  classical
  rw [localBlockCoeff_eq_prod]
  unfold choose Split.left localBlockSplitEquivSplit
  rw [← (localCoordinateEquiv d).prod_comp]
  apply Finset.prod_congr rfl
  intro i hi
  change Nat.choose (beta ((localCoordinateEquiv d) i)) (localSplitToFun beta _ a i) =
    Nat.choose (beta ((localCoordinateEquiv d) i))
      ((Equiv.piCongrLeft (fun c => Fin (beta c + 1)) (localCoordinateEquiv d))
        (localSplitToFun beta _ a) ((localCoordinateEquiv d) i))
  let f : (j : Fin (Finset.univ.toList : List (TimeVelocityCoord d)).length) →
      Fin (beta ((localCoordinateEquiv d) j) + 1) := localSplitToFun beta _ a
  have h := Equiv.piCongrLeft_apply_apply (fun c => Fin (beta c + 1))
    (localCoordinateEquiv d) f i
  exact congrArg (fun x : Fin (beta ((localCoordinateEquiv d) i) + 1) =>
    Nat.choose (beta ((localCoordinateEquiv d) i)) x.val) h.symm

private def localBlockLeftList (beta : TimeVelocityMultiIndex d) :
    (cs : List (TimeVelocityCoord d)) → LocalBlockSplit beta cs → List (TimeVelocity d)
  | [], _ => []
  | c :: cs, (k,a) => List.replicate k (timeVelocityBasis c) ++ localBlockLeftList beta cs a

private def localBlockRightList (beta : TimeVelocityMultiIndex d) :
    (cs : List (TimeVelocityCoord d)) → LocalBlockSplit beta cs → List (TimeVelocity d)
  | [], _ => []
  | c :: cs, (k,a) => List.replicate (beta c-k) (timeVelocityBasis c) ++
      localBlockRightList beta cs a

private def localDirs : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: vs, f => fun z => fderiv ℝ (localDirs vs f) z v

private theorem localRepDirs_eq_localDirs (v : E) (n : ℕ) (f : E → ℝ) :
    localRepDirs v n f = localDirs (List.replicate n v) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, localDirs, localRepDirs]
      exact congrArg (fun h : E → ℝ => fun z => fderiv ℝ h z v) ih

private theorem localDirs_append (xs ys : List E) (f : E → ℝ) :
    localDirs (xs ++ ys) f = localDirs xs (localDirs ys f) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, localDirs]; rw [ih]

private theorem localBlockLeft_eq_dirs (beta : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : LocalBlockSplit beta cs) (f : TimeVelocity d → ℝ) :
    localBlockLeft timeVelocityBasis beta cs a f = localDirs (localBlockLeftList beta cs a) f := by
  induction cs generalizing f with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockLeft, localBlockLeftList, localDirs_append, ← localRepDirs_eq_localDirs]
      exact congrArg (localRepDirs (timeVelocityBasis c) k) (ih a f)

private theorem localBlockRight_eq_dirs (beta : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : LocalBlockSplit beta cs) (f : TimeVelocity d → ℝ) :
    localBlockRight timeVelocityBasis beta cs a f =
      localDirs (localBlockRightList beta cs a) f := by
  induction cs generalizing f with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockRight, localBlockRightList, localDirs_append, ← localRepDirs_eq_localDirs]
      exact congrArg (localRepDirs (timeVelocityBasis c) (beta c-k)) (ih a f)

private theorem localLeftList_eq_flatMap (beta gamma : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : LocalBlockSplit beta cs)
    (h : ∀ i, gamma (cs.get i) = localSplitToFun beta cs a i) :
    localBlockLeftList beta cs a =
      cs.flatMap fun c => List.replicate (gamma c) (timeVelocityBasis c) := by
  induction cs with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockLeftList, List.flatMap_cons]
      have hzero := h (⟨0, by simp⟩ : Fin (c :: cs).length)
      have htail : ∀ i, gamma (cs.get i) = localSplitToFun beta cs a i := by
        intro i; simpa [localSplitToFun_cons_zero, localSplitToFun_cons_succ] using h i.succ
      rw [ih a htail]
      congr 1
      simpa [localSplitToFun_cons_zero, localSplitToFun_cons_succ] using hzero.symm

private theorem localRightList_eq_flatMap (beta gamma : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : LocalBlockSplit beta cs)
    (h : ∀ i, gamma (cs.get i) = localSplitToFun beta cs a i) :
    localBlockRightList beta cs a =
      cs.flatMap fun c => List.replicate (beta c-gamma c) (timeVelocityBasis c) := by
  induction cs with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [localBlockRightList, List.flatMap_cons]
      have hzero := h (⟨0, by simp⟩ : Fin (c :: cs).length)
      have htail : ∀ i, gamma (cs.get i) = localSplitToFun beta cs a i := by
        intro i; simpa [localSplitToFun_cons_zero, localSplitToFun_cons_succ] using h i.succ
      rw [ih a htail]
      congr 1
      simpa [localSplitToFun_cons_zero, localSplitToFun_cons_succ] using
        congrArg (fun n : ℕ => beta c-n) hzero.symm

private theorem localSplit_pointwise (beta : TimeVelocityMultiIndex d)
    (a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)))
    (i : Fin (Finset.univ.toList : List (TimeVelocityCoord d)).length) :
    localBlockSplitEquivSplit beta a ((Finset.univ.toList).get i) =
      localSplitToFun beta _ a i := by
  change ((Equiv.piCongrLeft (fun c => Fin (beta c + 1)) (localCoordinateEquiv d))
    (localSplitToFun beta _ a)) ((localCoordinateEquiv d) i) = _
  let f : (j : Fin (Finset.univ.toList : List (TimeVelocityCoord d)).length) →
      Fin (beta ((localCoordinateEquiv d) j) + 1) := localSplitToFun beta _ a
  exact Equiv.piCongrLeft_apply_apply (fun c => Fin (beta c + 1))
    (localCoordinateEquiv d) f i

private theorem localLeftList_eq_coordinateList (beta : TimeVelocityMultiIndex d)
    (a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d))) :
    localBlockLeftList beta _ a =
      (coordinateList (localBlockSplitEquivSplit beta a).left).map timeVelocityBasis := by
  rw [localLeftList_eq_flatMap beta (localBlockSplitEquivSplit beta a).left _ a
    (fun i => congrArg Fin.val (localSplit_pointwise beta a i))]
  unfold coordinateList
  rw [List.map_flatMap]
  simp [Split.left]

private theorem localRightList_eq_coordinateList (beta : TimeVelocityMultiIndex d)
    (a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d))) :
    localBlockRightList beta _ a =
      (coordinateList (localBlockSplitEquivSplit beta a).right).map timeVelocityBasis := by
  rw [localRightList_eq_flatMap beta (localBlockSplitEquivSplit beta a).left _ a
    (fun i => congrArg Fin.val (localSplit_pointwise beta a i))]
  unfold coordinateList
  rw [List.map_flatMap]
  simp [Split.right]

private theorem localDirs_ofFn_eq_iteratedFDeriv (n : ℕ) (v : Fin n → E)
    (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ n f z) :
    localDirs (List.ofFn v) f z = iteratedFDeriv ℝ n f z v := by
  induction n generalizing f z with
  | zero => simp [localDirs]
  | succ n ih =>
      rw [List.ofFn_succ, localDirs, iteratedFDeriv_succ_apply_left]
      have hfun : localDirs (List.ofFn fun i => v i.succ) f =ᶠ[nhds z] fun y =>
          iteratedFDeriv ℝ n f y fun i => v i.succ := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih (fun i => v i.succ) f y (hy.of_le
          (show (n : WithTop ℕ∞) ≤ n + 1 by simp))
      change (fderiv ℝ (localDirs (List.ofFn fun i => v i.succ) f) z) (v 0) = _
      rw [hfun.fderiv_eq]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) z :=
        hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
      rw [fderiv_continuousMultilinear_apply_const_apply hd]
      rfl

private theorem localOrder_mono {alpha beta : TimeVelocityMultiIndex d} (h : alpha ≤ beta) :
    alpha.order ≤ beta.order := by
  have hv : ∑ i, alpha (velocityCoord i) ≤ ∑ i, beta (velocityCoord i) :=
    Finset.sum_le_sum fun i _ => h (velocityCoord i)
  have ht := h (timeCoord d)
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order] at *
  omega

private theorem localBlockLeft_eq_coordinate (beta : TimeVelocityMultiIndex d)
    (a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)))
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) (hf : ContDiffAt ℝ beta.order f z) :
    localBlockLeft timeVelocityBasis beta _ a f z =
      coordinateIteratedFDeriv (localBlockSplitEquivSplit beta a).left f z := by
  rw [localBlockLeft_eq_dirs, localLeftList_eq_coordinateList]
  have hlist : (coordinateList (localBlockSplitEquivSplit beta a).left).map timeVelocityBasis =
      List.ofFn (fun i => timeVelocityBasis
        ((coordinateList (localBlockSplitEquivSplit beta a).left).get i)) := by
    symm
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map timeVelocityBasis)
      (List.ofFn_get (coordinateList (localBlockSplitEquivSplit beta a).left))
  rw [hlist]
  unfold coordinateIteratedFDeriv
  apply localDirs_ofFn_eq_iteratedFDeriv
  apply hf.of_le
  rw [length_coordinateList]
  exact_mod_cast localOrder_mono fun c => Nat.le_of_lt_succ
    ((localBlockSplitEquivSplit beta a) c).isLt

private theorem localBlockRight_eq_coordinate (beta : TimeVelocityMultiIndex d)
    (a : LocalBlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)))
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) (hf : ContDiffAt ℝ beta.order f z) :
    localBlockRight timeVelocityBasis beta _ a f z =
      coordinateIteratedFDeriv (localBlockSplitEquivSplit beta a).right f z := by
  rw [localBlockRight_eq_dirs, localRightList_eq_coordinateList]
  have hlist : (coordinateList (localBlockSplitEquivSplit beta a).right).map timeVelocityBasis =
      List.ofFn (fun i => timeVelocityBasis
        ((coordinateList (localBlockSplitEquivSplit beta a).right).get i)) := by
    symm
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map timeVelocityBasis)
      (List.ofFn_get (coordinateList (localBlockSplitEquivSplit beta a).right))
  rw [hlist]
  unfold coordinateIteratedFDeriv
  apply localDirs_ofFn_eq_iteratedFDeriv
  apply hf.of_le
  rw [length_coordinateList]
  exact_mod_cast localOrder_mono fun c => Nat.sub_le _ _

private theorem localBlockDirs_eq_dirs_flatMap {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (f : E → ℝ) :
    localBlockDirs basis beta cs f =
      localDirs (cs.flatMap fun c => List.replicate (beta c) (basis c)) f := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
      rw [localBlockDirs, List.flatMap_cons, localDirs_append, ← localRepDirs_eq_localDirs]
      exact congrArg (localRepDirs (basis c) (beta c)) (ih f)

private theorem localBlockOrder_univ (beta : TimeVelocityMultiIndex d) :
    localBlockOrder beta (Finset.univ.toList : List (TimeVelocityCoord d)) = beta.order := by
  simp [localBlockOrder, TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order, timeCoord, velocityCoord]

private theorem localBlockDirs_univ_eq_coordinate (beta : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) (hf : ContDiffAt ℝ beta.order f z) :
    localBlockDirs timeVelocityBasis beta
        (Finset.univ.toList : List (TimeVelocityCoord d)) f z =
      coordinateIteratedFDeriv beta f z := by
  rw [localBlockDirs_eq_dirs_flatMap]
  have hlist : ((Finset.univ.toList : List (TimeVelocityCoord d)).flatMap fun c =>
        List.replicate (beta c) (timeVelocityBasis c)) =
      List.ofFn (fun i => timeVelocityBasis (beta.coordinateList.get i)) := by
    calc
      _ = beta.coordinateList.map timeVelocityBasis := by
        unfold coordinateList
        rw [List.map_flatMap]
        simp
      _ = _ := by
        symm
        simpa only [List.map_ofFn, Function.comp_def] using
          congrArg (List.map timeVelocityBasis) (List.ofFn_get beta.coordinateList)
  rw [hlist]
  unfold coordinateIteratedFDeriv
  apply localDirs_ofFn_eq_iteratedFDeriv
  simpa using hf

/-- Exact pointwise multi-index Leibniz formula under finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_mul_at
    (beta : TimeVelocityMultiIndex d)
    (f g : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ beta.order f z)
    (hg : ContDiffAt ℝ beta.order g z) :
    coordinateIteratedFDeriv beta (fun x ↦ f x * g x) z =
      ∑ gamma : Split beta,
        (beta.choose gamma.left : ℝ) *
          coordinateIteratedFDeriv gamma.left f z *
          coordinateIteratedFDeriv gamma.right g z := by
  classical
  let cs : List (TimeVelocityCoord d) := Finset.univ.toList
  calc
    coordinateIteratedFDeriv beta (fun x => f x * g x) z =
        localBlockDirs timeVelocityBasis beta cs (fun x => f x * g x) z := by
      exact (localBlockDirs_univ_eq_coordinate beta _ z (hf.mul hg)).symm
    _ = ∑ a : LocalBlockSplit beta cs, (localBlockCoeff beta cs a : ℝ) *
          localBlockLeft timeVelocityBasis beta cs a f z *
          localBlockRight timeVelocityBasis beta cs a g z := by
      apply localBlockDirs_mul
      · simpa [cs, localBlockOrder_univ] using hf
      · simpa [cs, localBlockOrder_univ] using hg
    _ = ∑ a : LocalBlockSplit beta cs,
          (beta.choose (localBlockSplitEquivSplit beta a).left : ℝ) *
            coordinateIteratedFDeriv (localBlockSplitEquivSplit beta a).left f z *
            coordinateIteratedFDeriv (localBlockSplitEquivSplit beta a).right g z := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [localBlockCoeff_eq_choose, localBlockLeft_eq_coordinate beta a f z hf,
        localBlockRight_eq_coordinate beta a g z hg]
    _ = _ := by
      exact sum_localBlockSplit_eq_sum_split beta (fun gamma =>
        (beta.choose gamma.left : ℝ) * coordinateIteratedFDeriv gamma.left f z *
          coordinateIteratedFDeriv gamma.right g z)

private theorem localDirs_contDiffAt (l : List E) (m : ℕ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (m + l.length) f z) : ContDiffAt ℝ m (localDirs l f) z := by
  induction l generalizing m f with
  | nil => simpa [localDirs] using hf
  | cons v l ih =>
      rw [localDirs]
      have h : ContDiffAt ℝ (m + 1) (localDirs l f) z := by
        apply ih
        convert hf using 1
        norm_num
        exact_mod_cast (show (m + 1) + l.length = m + (l.length + 1) by omega)
      exact (h.fderiv_right (by norm_num)).clm_apply contDiffAt_const

private theorem localDirectional_comm (a b : E) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fun y => fderiv ℝ f y a) z b =
      fderiv ℝ (fun y => fderiv ℝ f y b) z a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const b)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.isSymmSndFDerivAt (by simp)).eq b a

private theorem localDirs_perm {l₁ l₂ : List E} (hperm : l₁.Perm l₂)
    (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ l₁.length f z) :
    localDirs l₁ f z = localDirs l₂ f z := by
  induction hperm generalizing f z with
  | nil => rfl
  | @cons a l₁ l₂ hperm ih =>
      simp only [localDirs]
      have heq : localDirs l₁ f =ᶠ[nhds z] localDirs l₂ f := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih f y (hy.of_le (by simp))
      exact congrArg (fun L : E →L[ℝ] ℝ => L a) heq.fderiv_eq
  | @swap a b l =>
      simp only [localDirs]
      apply localDirectional_comm
      apply localDirs_contDiffAt l 2 f z
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
  | @trans l₁ l₂ l₃ h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact (ih₁₂ f z hf).trans (ih₂₃ f z (h₁₂.length_eq ▸ hf))

private theorem coordinateList_add_single_perm_local
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d) :
    (beta + Pi.single c 1).coordinateList.Perm (c :: beta.coordinateList) := by
  classical
  letI : BEq (TimeVelocityCoord d) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (TimeVelocityCoord d) := ⟨by intro a b; simp⟩
  rw [List.perm_iff_count]
  intro a
  have count_flat (q : TimeVelocityMultiIndex d) : ∀ l : List (TimeVelocityCoord d),
      l.Nodup → List.count a (l.flatMap fun b => List.replicate (q b) b) =
        if a ∈ l then q a else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
        have hbl := (List.nodup_cons.mp hl).1
        have hln := (List.nodup_cons.mp hl).2
        by_cases hab : a = b
        · subst b
          simp [hbl, ih hln]
        · simp [ih hln]
          rw [List.count_replicate]
          split <;> simp_all
  unfold coordinateList
  rw [count_flat _ _ (Finset.nodup_toList (Finset.univ : Finset (TimeVelocityCoord d)))]
  simp only [List.count_cons]
  rw [count_flat _ _ (Finset.nodup_toList (Finset.univ : Finset (TimeVelocityCoord d)))]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.add_apply]
  change beta a + (Pi.single c 1 : TimeVelocityMultiIndex d) a =
    beta a + (if c == a then 1 else 0)
  congr 1
  by_cases h : c = a
  · subst a
    simp only [Pi.single_eq_same, beq_self_eq_true, if_true]
  · rw [Pi.single_apply, if_neg (fun hac => h hac.symm)]
    have hb : (c == a) = false := Bool.eq_false_iff.mpr fun heq => h (beq_iff_eq.mp heq)
    rw [hb]
    rfl

/-- Adding one coordinate differentiates the associated coordinate derivative
at a point under the exact finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_add_single_at
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ (beta.order + 1) f z) :
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
      fderiv ℝ (coordinateIteratedFDeriv beta f) z
        (timeVelocityBasis c) := by
  let vecList (alpha : TimeVelocityMultiIndex d) : List (TimeVelocity d) :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (y : TimeVelocity d)
      (ha : ContDiffAt ℝ alpha.order f y) :
      coordinateIteratedFDeriv alpha f y = localDirs (vecList alpha) f y := by
    unfold coordinateIteratedFDeriv
    have hlist : vecList alpha = List.ofFn (fun i =>
        timeVelocityBasis (alpha.coordinateList.get i)) := by
      symm
      simpa [vecList, Function.comp_def] using congrArg (List.map timeVelocityBasis)
        (List.ofFn_get alpha.coordinateList)
    rw [hlist, localDirs_ofFn_eq_iteratedFDeriv]
    simpa using ha
  have hperm : (vecList (beta + Pi.single c 1)).Perm
      (timeVelocityBasis c :: vecList beta) := by
    simpa [vecList] using (coordinateList_add_single_perm_local beta c).map timeVelocityBasis
  calc
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
        localDirs (vecList (beta + Pi.single c 1)) f z :=
      eval_dirs _ _ (by simpa using hf)
    _ = localDirs (timeVelocityBasis c :: vecList beta) f z := by
      apply localDirs_perm hperm f z
      simpa [vecList] using hf
    _ = fderiv ℝ (coordinateIteratedFDeriv beta f) z (timeVelocityBasis c) := by
      simp only [localDirs]
      have hfun : localDirs (vecList beta) f =ᶠ[nhds z]
          coordinateIteratedFDeriv beta f := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact (eval_dirs beta y (hy.of_le (by simp))).symm
      exact congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L (timeVelocityBasis c))
        hfun.fderiv_eq

/-- A coordinate derivative composed before a coordinate multi-index agrees
with addition of that coordinate, under exact finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_comp_single_at
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ (beta.order + 1) f z) :
    coordinateIteratedFDeriv beta
        (coordinateIteratedFDeriv (Pi.single c 1) f) z =
      coordinateIteratedFDeriv (beta + Pi.single c 1) f z := by
  let vecList (alpha : TimeVelocityMultiIndex d) : List (TimeVelocity d) :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (g : TimeVelocity d → ℝ)
      (y : TimeVelocity d) (hg : ContDiffAt ℝ alpha.order g y) :
      coordinateIteratedFDeriv alpha g y = localDirs (vecList alpha) g y := by
    unfold coordinateIteratedFDeriv
    have hlist : vecList alpha = List.ofFn (fun i =>
        timeVelocityBasis (alpha.coordinateList.get i)) := by
      symm
      simpa [vecList, Function.comp_def] using congrArg (List.map timeVelocityBasis)
        (List.ofFn_get alpha.coordinateList)
    rw [hlist, localDirs_ofFn_eq_iteratedFDeriv]
    simpa using hg
  have hsingle : coordinateIteratedFDeriv (Pi.single c 1) f =ᶠ[nhds z]
      localDirs (vecList (Pi.single c 1)) f := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact eval_dirs (Pi.single c 1) f y (by
      apply hy.of_le
      simp only [order_single, Nat.cast_one]
      exact le_add_self)
  have houter : ContDiffAt ℝ beta.order
      (localDirs (vecList (Pi.single c 1)) f) z := by
    apply localDirs_contDiffAt
    simpa [vecList, add_comm] using hf
  have hsinglePerm : (vecList (Pi.single c 1)).Perm [timeVelocityBasis c] := by
    have h := (coordinateList_add_single_perm_local
      (0 : TimeVelocityMultiIndex d) c).map timeVelocityBasis
    simpa [vecList] using h
  have hperm : (vecList beta ++ vecList (Pi.single c 1)).Perm
      (vecList (beta + Pi.single c 1)) := by
    have h := (coordinateList_add_single_perm_local beta c).map timeVelocityBasis
    exact (hsinglePerm.append_left (vecList beta)).trans
      (List.perm_append_comm.trans (by simpa [vecList] using h.symm))
  calc
    coordinateIteratedFDeriv beta
        (coordinateIteratedFDeriv (Pi.single c 1) f) z =
        coordinateIteratedFDeriv beta
          (localDirs (vecList (Pi.single c 1)) f) z := by
      exact coordinateIteratedFDeriv_congr_of_eventuallyEq beta hsingle
    _ = localDirs (vecList beta)
        (localDirs (vecList (Pi.single c 1)) f) z :=
      eval_dirs beta _ z houter
    _ = localDirs (vecList beta ++ vecList (Pi.single c 1)) f z := by
      rw [localDirs_append]
    _ = localDirs (vecList (beta + Pi.single c 1)) f z := by
      apply localDirs_perm hperm f z
      simpa [vecList] using hf
    _ = coordinateIteratedFDeriv (beta + Pi.single c 1) f z := by
      symm
      apply eval_dirs
      simpa using hf

end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
