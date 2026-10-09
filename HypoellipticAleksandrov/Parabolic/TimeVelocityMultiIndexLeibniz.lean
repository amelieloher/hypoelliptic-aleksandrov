module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Time--velocity multi-index derivatives

This file evaluates finite iterated Fréchet derivatives in the time--velocity
coordinate directions and proves their exact coordinatewise Leibniz formula.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

open scoped BigOperators

variable {d : ℕ}

private theorem sum_sub_of_le {I : Type*} [Fintype I]
    (f g : I → ℕ) (h : ∀ i, g i ≤ f i) :
    ∑ i, (f i - g i) = (∑ i, f i) - ∑ i, g i := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [ih]
      · have hi' := h i
        have hs : ∑ j ∈ s, g j ≤ ∑ j ∈ s, f j :=
          Finset.sum_le_sum fun j _ => h j
        omega

private def directionalFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) (f : E → F) : E → F :=
  fun x => fderiv ℝ f x v

private def directionalFDerivs {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : List E → (E → F) → E → F
  | [], f => f
  | v :: l, f => directionalFDerivs l (directionalFDeriv v f)

private theorem contDiff_directionalFDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (v : E) (f : E → F) (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (directionalFDeriv v f) := by
  exact (hf.fderiv_right (le_refl _)).clm_apply contDiff_const

private theorem directionalFDeriv_comm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : E) (f : E → F) (hf : ContDiff ℝ 2 f) :
    directionalFDeriv b (directionalFDeriv a f) =
      directionalFDeriv a (directionalFDeriv b f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change fderiv ℝ (fun y => fderiv ℝ f y a) x b =
    fderiv ℝ (fun y => fderiv ℝ f y b) x a
  rw [fderiv_clm_apply hd (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const b)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq b a

private theorem directionalFDerivs_congr {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List E) {f g : E → F} (h : f = g) :
    directionalFDerivs l f = directionalFDerivs l g := by
  subst g
  rfl

private theorem directionalFDerivs_append {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l₁ l₂ : List E) (f : E → F) :
    directionalFDerivs (l₁ ++ l₂) f =
      directionalFDerivs l₂ (directionalFDerivs l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons v l ih =>
      simp only [List.cons_append, directionalFDerivs]
      exact ih (directionalFDeriv v f)

private theorem directionalFDerivs_eq_of_perm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l₁ l₂ : List E} (hperm : l₁.Perm l₂) (f : E → F)
    (hf : ContDiff ℝ l₁.length f) :
    directionalFDerivs l₁ f = directionalFDerivs l₂ f := by
  induction hperm generalizing f with
  | nil => rfl
  | @cons a l₁ l₂ hperm ih =>
      simp only [directionalFDerivs]
      apply ih
      simpa using contDiff_directionalFDeriv a f hf
  | @swap a b l =>
      simp only [directionalFDerivs]
      apply directionalFDerivs_congr
      apply directionalFDeriv_comm
      apply hf.of_le
      simp only [List.length_cons]
      norm_cast
      omega
  | @trans l₁ l₂ l₃ h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact (ih₁₂ f hf).trans (ih₂₃ f (h₁₂.length_eq ▸ hf))

private theorem directionalFDerivs_reverse_ofFn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (v : Fin n → E) (f : E → F) (z : E) (hf : ContDiff ℝ n f) :
    directionalFDerivs (List.ofFn v).reverse f z = iteratedFDeriv ℝ n f z v := by
  induction n generalizing f with
  | zero => simp [directionalFDerivs]
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat]
      simp only [directionalFDerivs]
      rw [ih]
      · change iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (v (Fin.last n))) z
            (fun i => v i.castSucc) = _
        calc
          _ = iteratedFDeriv ℝ n (fderiv ℝ f) z (fun i => v i.castSucc)
                (v (Fin.last n)) :=
            iteratedFDeriv_clm_apply_const_apply
              (hc := hf.fderiv_right (by simp)) (hi := le_rfl)
          _ = _ := (iteratedFDeriv_succ_apply_right v).symm
      · exact contDiff_directionalFDeriv (v (Fin.last n)) f hf

/-- The coordinate multiset of a multi-index, represented by the fixed `Finset.univ.toList`
coordinate order and repeated according to multiplicity. -/
def coordinateList (beta : TimeVelocityMultiIndex d) : List (TimeVelocityCoord d) :=
  (Finset.univ.toList).flatMap fun c => List.replicate (beta c) c

/-- The coordinatewise multinomial coefficient. -/
def choose (beta gamma : TimeVelocityMultiIndex d) : ℕ :=
  ∏ c, Nat.choose (beta c) (gamma c)

/-- A coordinatewise split of `beta`, recording the multiplicity sent to the left factor. -/
abbrev Split (beta : TimeVelocityMultiIndex d) :=
  (c : TimeVelocityCoord d) → Fin (beta c + 1)

/-- The left multi-index of a split. -/
def Split.left {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    TimeVelocityMultiIndex d := fun c => gamma c

/-- The complementary right multi-index of a split. -/
def Split.right {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    TimeVelocityMultiIndex d := beta - gamma.left

/-- The classical coordinate derivative associated to `beta`, implemented by evaluating the
actual iterated Fréchet derivative on its fixed coordinate list. -/
def coordinateIteratedFDeriv (beta : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  iteratedFDeriv ℝ beta.coordinateList.length f z fun i =>
    timeVelocityBasis (beta.coordinateList.get i)

/-- The zero multi-index has no coordinate directions. -/
@[simp] theorem coordinateList_zero (d : ℕ) :
    coordinateList (0 : TimeVelocityMultiIndex d) = [] := by
  simp [coordinateList]

/-- The coordinate list has length equal to the total differential order. -/
@[simp] theorem length_coordinateList (beta : TimeVelocityMultiIndex d) :
    beta.coordinateList.length = beta.order := by
  simp [coordinateList, TimeVelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

/-- Choosing zero derivatives in every coordinate has coefficient one. -/
@[simp] theorem choose_zero_right (beta : TimeVelocityMultiIndex d) :
    beta.choose 0 = 1 := by
  simp [choose]

/-- Choosing every derivative in every coordinate has coefficient one. -/
@[simp] theorem choose_self (beta : TimeVelocityMultiIndex d) :
    beta.choose beta = 1 := by
  simp [choose]

/-- The left side of a split is bounded coordinatewise by the original index. -/
theorem Split.left_le {beta : TimeVelocityMultiIndex d}
    (gamma : Split beta) :
    gamma.left ≤ beta := by
  intro c
  exact Nat.le_of_lt_succ (gamma c).isLt

/-- The two sides of a split add back to the original multi-index. -/
@[simp] theorem Split.left_add_right
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left + gamma.right = beta := by
  funext c
  exact Nat.add_sub_of_le (gamma.left_le c)

/-- Total differential order is additive. -/
@[simp] theorem order_add (beta gamma : TimeVelocityMultiIndex d) :
    (beta + gamma).order = beta.order + gamma.order := by
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
    Finset.sum_add_distrib]
  omega

/-- Parabolic weight is additive. -/
@[simp] theorem parabolicWeight_add (beta gamma : TimeVelocityMultiIndex d) :
    (beta + gamma).parabolicWeight = beta.parabolicWeight + gamma.parabolicWeight := by
  simp [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, Finset.sum_add_distrib]
  omega

/-- Total order commutes with coordinatewise subtraction under a pointwise bound. -/
theorem order_sub_of_le
    {beta gamma : TimeVelocityMultiIndex d} (h : gamma ≤ beta) :
    (beta - gamma).order = beta.order - gamma.order := by
  have hsum : ∑ i, gamma (velocityCoord i) ≤ ∑ i, beta (velocityCoord i) :=
    Finset.sum_le_sum fun i _ => h (velocityCoord i)
  have hsub :
      ∑ i, (beta (velocityCoord i) - gamma (velocityCoord i)) =
        (∑ i, beta (velocityCoord i)) - ∑ i, gamma (velocityCoord i) := by
    exact sum_sub_of_le _ _ fun i => h (velocityCoord i)
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order]
  rw [hsub]
  have ht : gamma (timeCoord d) ≤ beta (timeCoord d) := h (timeCoord d)
  omega

/-- Parabolic weight commutes with coordinatewise subtraction under a pointwise bound. -/
theorem parabolicWeight_sub_of_le
    {beta gamma : TimeVelocityMultiIndex d} (h : gamma ≤ beta) :
    (beta - gamma).parabolicWeight =
      beta.parabolicWeight - gamma.parabolicWeight := by
  have hsum : ∑ i, gamma (velocityCoord i) ≤ ∑ i, beta (velocityCoord i) :=
    Finset.sum_le_sum fun i _ => h (velocityCoord i)
  have hsub :
      ∑ i, (beta (velocityCoord i) - gamma (velocityCoord i)) =
        (∑ i, beta (velocityCoord i)) - ∑ i, gamma (velocityCoord i) := by
    exact sum_sub_of_le _ _ fun i => h (velocityCoord i)
  simp [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order]
  rw [hsub]
  have ht : gamma (timeCoord d) ≤ beta (timeCoord d) := h (timeCoord d)
  omega

/-- A single coordinate derivative has total order one. -/
@[simp] theorem order_single (c : TimeVelocityCoord d) :
    TimeVelocityMultiIndex.order (Pi.single c 1 : TimeVelocityMultiIndex d) = 1 := by
  cases c with
  | inl u => cases u; simp [TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order, timeCoord, velocityCoord]
  | inr i =>
      change 0 + ∑ x,
        (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr x) = 1
      rw [zero_add, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

/-- A single time derivative has parabolic weight two. -/
@[simp] theorem parabolicWeight_single_time :
    TimeVelocityMultiIndex.parabolicWeight
      (Pi.single (timeCoord d) 1 : TimeVelocityMultiIndex d) = 2 := by
  simp [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

/-- A single velocity derivative has parabolic weight one. -/
@[simp] theorem parabolicWeight_single_velocity (i : Fin d) :
    TimeVelocityMultiIndex.parabolicWeight
      (Pi.single (velocityCoord i) 1 : TimeVelocityMultiIndex d) = 1 := by
  change 2 * 0 + ∑ x,
    (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr x) = 1
  simp only [Nat.mul_zero, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The coordinate derivative of order zero is evaluation of the function. -/
@[simp] theorem coordinateIteratedFDeriv_zero
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    coordinateIteratedFDeriv 0 f z = f z := by
  unfold coordinateIteratedFDeriv
  rw [coordinateList_zero]
  exact iteratedFDeriv_zero_apply _

private theorem coordinateList_add_single_perm
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
    have hb : (c == a) = false := by
      exact Bool.eq_false_iff.mpr fun heq => h (beq_iff_eq.mp heq)
    rw [hb]
    rfl

/-- Adding one coordinate to a multi-index differentiates the associated
classical coordinate derivative in that direction. -/
theorem coordinateIteratedFDeriv_add_single
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiff ℝ (beta.order + 1) f) :
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
      fderiv ℝ (coordinateIteratedFDeriv beta f) z (timeVelocityBasis c) := by
  let vecList (alpha : TimeVelocityMultiIndex d) : List (TimeVelocity d) :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (y : TimeVelocity d)
      (ha : ContDiff ℝ alpha.order f) :
      coordinateIteratedFDeriv alpha f y =
        directionalFDerivs (vecList alpha).reverse f y := by
    unfold coordinateIteratedFDeriv
    rw [← directionalFDerivs_reverse_ofFn alpha.coordinateList.length
      (fun i => timeVelocityBasis (alpha.coordinateList.get i)) f y
      (by simpa using ha)]
    congr 2
    have hget : List.ofFn (fun i => alpha.coordinateList.get i) =
        alpha.coordinateList := List.ofFn_get _
    simpa only [vecList, List.map_ofFn, Function.comp_def] using! congrArg (List.map
      timeVelocityBasis) hget
  have hperm : ((vecList (beta + Pi.single c 1)).reverse).Perm
      ((vecList beta).reverse ++ [timeVelocityBasis c]) := by
    have hm := (coordinateList_add_single_perm beta c).map timeVelocityBasis
    exact (List.reverse_perm (l := vecList (beta + Pi.single c 1))).trans
      (hm.trans (by
        simpa [vecList, List.map_ofFn, Function.comp_def] using!
          (List.reverse_perm (l := timeVelocityBasis c :: vecList beta)).symm))
  calc
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
        directionalFDerivs (vecList (beta + Pi.single c 1)).reverse f z :=
      eval_dirs _ _ (by simpa using hf)
    _ = directionalFDerivs ((vecList beta).reverse ++ [timeVelocityBasis c]) f z := by
      exact congrFun (directionalFDerivs_eq_of_perm hperm f
        (by simpa [vecList, List.map_ofFn, Function.comp_def] using! hf)) z
    _ = directionalFDeriv (timeVelocityBasis c)
          (directionalFDerivs (vecList beta).reverse f) z := by
      rw [directionalFDerivs_append]
      rfl
    _ = fderiv ℝ (coordinateIteratedFDeriv beta f) z
          (timeVelocityBasis c) := by
      unfold directionalFDeriv
      exact congrArg (fun q => fderiv ℝ q z (timeVelocityBasis c))
        (funext fun y => (eval_dirs beta y (hf.of_le (by simp))).symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def repDirs (v : E) : ℕ → (E → ℝ) → E → ℝ
  | 0, f => f
  | n + 1, f => fun z => fderiv ℝ (repDirs v n f) z v

private theorem repDirs_contDiff (v : E) (n m : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ (m + n) f) : ContDiff ℝ m (repDirs v n f) := by
  induction n generalizing m f with
  | zero => simpa [repDirs] using hf
  | succ n ih =>
      rw [repDirs]
      have h : ContDiff ℝ (m + 1) (repDirs v n f) := by
        apply ih
        simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
      exact (h.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem repDirs_add (v : E) (n : ℕ) (f g : E → ℝ) (z : E)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    repDirs v n (fun x => f x + g x) z = repDirs v n f z + repDirs v n g z := by
  induction n generalizing f g z with
  | zero => rfl
  | succ n ih =>
      rw [repDirs]
      have hfun : repDirs v n (fun x => f x + g x) =
          fun x => repDirs v n f x + repDirs v n g x := by
        funext x
        exact ih f g x (hf.of_le (by simp)) (hg.of_le (by simp))
      rw [hfun]
      simp only [repDirs]
      rw [fderiv_fun_add]
      · rfl
      · exact (repDirs_contDiff v n 1 f (by simpa [add_comm] using! hf)).differentiable (by
        norm_num) |>.differentiableAt
      · exact (repDirs_contDiff v n 1 g (by simpa [add_comm] using! hg)).differentiable (by
        norm_num) |>.differentiableAt

private theorem repDirs_smul (v : E) (n : ℕ) (a : ℝ) (f : E → ℝ) (z : E)
    (hf : ContDiff ℝ n f) :
    repDirs v n (fun x => a * f x) z = a * repDirs v n f z := by
  induction n generalizing f z with
  | zero => rfl
  | succ n ih =>
      rw [repDirs]
      have hfun : repDirs v n (fun x => a * f x) = fun x => a * repDirs v n f x := by
        funext x
        exact ih f x (hf.of_le (by simp))
      rw [hfun]
      have hd : DifferentiableAt ℝ (repDirs v n f) z :=
        (repDirs_contDiff v n 1 f (by simpa [add_comm] using! hf)).differentiable (by norm_num)
          |>.differentiableAt
      simpa only [repDirs, smul_eq_mul, ContinuousLinearMap.smul_apply, Pi.smul_def] using
        congrArg (fun L : E →L[ℝ] ℝ => L v)
          (fderiv_const_smul hd a)

private theorem repDirs_sum {A : Type*} [Fintype A] (v : E) (n : ℕ)
    (F : A → E → ℝ) (z : E) (hF : ∀ a, ContDiff ℝ n (F a)) :
    repDirs v n (fun x => ∑ a, F a x) z = ∑ a, repDirs v n (F a) z := by
  classical
  have hzero : ∀ m z, repDirs v m (fun _ : E => 0) z = 0 := by
    intro m
    induction m with
    | zero => simp [repDirs]
    | succ m ih =>
        intro x
        rw [repDirs]
        have hz : repDirs v m (fun _ : E => 0) = fun _ => 0 := funext ih
        rw [hz]
        simp
  induction (Finset.univ : Finset A) using Finset.induction_on with
  | empty => simpa using hzero n z
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [repDirs_add v n _ _ z]
      · rw [ih]
      · exact hF a
      · exact ContDiff.sum fun b _ => hF b

private theorem repDirs_mul_range (v : E) (n : ℕ) (f g : E → ℝ) (z : E)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    repDirs v n (fun x => f x * g x) z =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) *
        (repDirs v k f z * repDirs v (n - k) g z) := by
  classical
  induction n generalizing f g z with
  | zero => simp [repDirs]
  | succ n ih =>
      rw [repDirs]
      have hfun : repDirs v n (fun x => f x * g x) = fun x =>
          ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) *
            (repDirs v k f x * repDirs v (n - k) g x) := by
        funext x
        exact ih f g x (hf.of_le (by simp)) (hg.of_le (by simp))
      rw [hfun]
      have hdf : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (repDirs v k f) z := by
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        exact (repDirs_contDiff v k 1 f (hf.of_le (by
          exact_mod_cast (show 1 + k ≤ n + 1 by omega)))).differentiable (by norm_num)
          |>.differentiableAt
      have hdg : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (repDirs v (n - k) g) z := by
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        exact (repDirs_contDiff v (n-k) 1 g (hg.of_le (by
          exact_mod_cast (show 1 + (n-k) ≤ n + 1 by omega)))).differentiable (by norm_num)
          |>.differentiableAt
      change (fderiv ℝ (fun x => ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) *
          (repDirs v k f x * repDirs v (n - k) g x)) z) v = _
      rw [fderiv_fun_sum]
      · simp only [ContinuousLinearMap.sum_apply]
        have hterm : ∀ k ∈ Finset.range (n + 1),
            (fderiv ℝ (fun x => (Nat.choose n k : ℝ) *
              (repDirs v k f x * repDirs v (n-k) g x)) z) v =
              (Nat.choose n k : ℝ) *
                (repDirs v k f z * repDirs v (n-k+1) g z +
                 repDirs v (k+1) f z * repDirs v (n-k) g z) := by
          intro k hk
          change (fderiv ℝ (fun x => (Nat.choose n k : ℝ) *
            ((repDirs v k f * repDirs v (n-k) g) x)) z) v = _
          rw [fderiv_const_mul ((hdf k hk).mul (hdg k hk))
            (Nat.choose n k : ℝ)]
          change ((Nat.choose n k : ℝ) •
            fderiv ℝ (fun y => repDirs v k f y * repDirs v (n-k) g y) z) v = _
          rw [fderiv_fun_mul (hdf k hk) (hdg k hk)]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul, repDirs]
          ring
        rw [Finset.sum_congr rfl hterm]
        rw [Finset.sum_choose_succ_mul
          (f := fun i j => repDirs v i f z * repDirs v j g z) n]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have heq : n - k + 1 = n + 1 - k := by omega
        rw [heq]
        ring
      · intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hf1 : ContDiff ℝ 1 (repDirs v k f) :=
          repDirs_contDiff v k 1 f (hf.of_le (by
            exact_mod_cast (show 1 + k ≤ n + 1 by omega)))
        have hg1 : ContDiff ℝ 1 (repDirs v (n-k) g) :=
          repDirs_contDiff v (n-k) 1 g (hg.of_le (by
            exact_mod_cast (show 1 + (n-k) ≤ n + 1 by omega)))
        exact (contDiff_const.mul (hf1.mul hg1)).differentiable (by norm_num) |>.differentiableAt

private theorem repDirs_mul_binomial (v : E) (n : ℕ) (f g : E → ℝ) (z : E)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    repDirs v n (fun x => f x * g x) z =
      ∑ k : Fin (n + 1), (Nat.choose n k : ℝ) *
        repDirs v k f z * repDirs v (n - k) g z := by
  rw [repDirs_mul_range v n f g z hf hg]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def dirs : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: vs, f => fun z => fderiv ℝ (dirs vs f) z v

private theorem repDirs_eq_dirs_replicate (v : E) (n : ℕ) (f : E → ℝ) :
    repDirs v n f = dirs (List.replicate n v) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, dirs, repDirs]
      exact congrArg (fun h : E → ℝ => fun z => fderiv ℝ h z v) ih

private theorem repDirs_contDiff_local (v : E) (n m : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ (m + n) f) : ContDiff ℝ m (repDirs v n f) := by
  induction n generalizing m f with
  | zero => simpa [repDirs] using hf
  | succ n ih =>
      rw [repDirs]
      have h : ContDiff ℝ (m + 1) (repDirs v n f) := by
        apply ih
        simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
      exact (h.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- Apply coordinate blocks in the order induced by a coordinate list. -/
private def blockDirs {C : Type*} (basis : C → E) (beta : C → ℕ) :
    List C → (E → ℝ) → E → ℝ
  | [], f => f
  | c :: cs, f => repDirs (basis c) (beta c) (blockDirs basis beta cs f)

private def blockOrder {C : Type*} (beta : C → ℕ) (cs : List C) : ℕ :=
  (cs.map beta).sum

private theorem blockDirs_contDiff {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (m : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ (m + blockOrder beta cs) f) :
    ContDiff ℝ m (blockDirs basis beta cs f) := by
  induction cs generalizing m f with
  | nil => simpa [blockDirs, blockOrder] using hf
  | cons c cs ih =>
      rw [blockDirs]
      apply repDirs_contDiff_local
      apply ih
      simpa [blockOrder, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf

private theorem dirs_append (xs ys : List E) (f : E → ℝ) :
    dirs (xs ++ ys) f = dirs xs (dirs ys f) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, dirs]
      rw [ih]

private theorem blockDirs_eq_dirs_flatMap {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (f : E → ℝ) :
    blockDirs basis beta cs f =
      dirs (cs.flatMap fun c => List.replicate (beta c) (basis c)) f := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
      rw [blockDirs, List.flatMap_cons, dirs_append]
      rw [← repDirs_eq_dirs_replicate]
      exact congrArg (repDirs (basis c) (beta c)) (ih f)

/-- Dependent choices of derivative counts, one for each coordinate block. -/
private def BlockSplit {C : Type*} (beta : C → ℕ) : List C → Type
  | [] => PUnit
  | c :: cs => Fin (beta c + 1) × BlockSplit beta cs

private instance {C : Type*} (beta : C → ℕ) (cs : List C) : Fintype (BlockSplit beta cs) := by
  induction cs with
  | nil => simp [BlockSplit]; infer_instance
  | cons c cs ih => simp [BlockSplit]; infer_instance

private def blockSplitToFun {C : Type*} (beta : C → ℕ) :
    (cs : List C) → BlockSplit beta cs → (i : Fin cs.length) → Fin (beta (cs.get i) + 1)
  | [], _, i => Fin.elim0 i
  | _ :: cs, (k, a), i => Fin.cases k (blockSplitToFun beta cs a) i

private def funToBlockSplit {C : Type*} (beta : C → ℕ) :
    (cs : List C) → ((i : Fin cs.length) → Fin (beta (cs.get i) + 1)) → BlockSplit beta cs
  | [], _ => PUnit.unit
  | _ :: cs, f => (f ⟨0, by simp⟩, funToBlockSplit beta cs fun i => f i.succ)

private theorem funToBlockSplit_toFun {C : Type*} (beta : C → ℕ)
    (cs : List C) (a : BlockSplit beta cs) :
    funToBlockSplit beta cs (blockSplitToFun beta cs a) = a := by
  induction cs with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      simp only [funToBlockSplit, blockSplitToFun]
      exact congrArg (fun x => (k,x)) (ih a)

private theorem blockSplitToFun_toBlockSplit {C : Type*} (beta : C → ℕ)
    (cs : List C) (f : (i : Fin cs.length) → Fin (beta (cs.get i) + 1)) :
    blockSplitToFun beta cs (funToBlockSplit beta cs f) = f := by
  induction cs with
  | nil => funext i; exact Fin.elim0 i
  | cons c cs ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [funToBlockSplit, blockSplitToFun]
        rfl
      · change blockSplitToFun beta cs
          (funToBlockSplit beta cs (fun i => f i.succ)) j = f j.succ
        rw [ih]

private def blockSplitEquivPi {C : Type*} (beta : C → ℕ) (cs : List C) :
    BlockSplit beta cs ≃ ((i : Fin cs.length) → Fin (beta (cs.get i) + 1)) where
  toFun := blockSplitToFun beta cs
  invFun := funToBlockSplit beta cs
  left_inv := funToBlockSplit_toFun beta cs
  right_inv := blockSplitToFun_toBlockSplit beta cs

private theorem sum_blockSplit_cons {C : Type*} (beta : C → ℕ) (c : C) (cs : List C)
    (F : BlockSplit beta (c :: cs) → ℝ) :
    (∑ a, F a) = ∑ k : Fin (beta c + 1), ∑ a : BlockSplit beta cs, F (k,a) := by
  exact Fintype.sum_prod_type F

private def blockLeftDirs {C : Type*} (basis : C → E) (beta : C → ℕ) :
    (cs : List C) → BlockSplit beta cs → (E → ℝ) → E → ℝ
  | [], _, f => f
  | c :: cs, (k,a), f => repDirs (basis c) k (blockLeftDirs basis beta cs a f)

private def blockRightDirs {C : Type*} (basis : C → E) (beta : C → ℕ) :
    (cs : List C) → BlockSplit beta cs → (E → ℝ) → E → ℝ
  | [], _, f => f
  | c :: cs, (k,a), f => repDirs (basis c) (beta c - k)
      (blockRightDirs basis beta cs a f)

private def blockCoeff {C : Type*} (beta : C → ℕ) :
    (cs : List C) → BlockSplit beta cs → ℕ
  | [], _ => 1
  | c :: cs, (k,a) => Nat.choose (beta c) k * blockCoeff beta cs a

private theorem blockLeftDirs_contDiff {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (a : BlockSplit beta cs) (m : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ (m + blockOrder beta cs) f) :
    ContDiff ℝ m (blockLeftDirs basis beta cs a f) := by
  induction cs generalizing m f with
  | nil => simpa [blockLeftDirs, blockOrder] using hf
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [blockLeftDirs]
      apply repDirs_contDiff_local
      apply ih
      apply hf.of_le
      have hk : (k : ℕ) ≤ beta c := Nat.le_of_lt_succ k.isLt
      exact_mod_cast (show m + k + blockOrder beta cs ≤
        m + blockOrder beta (c::cs) by simp [blockOrder]; omega)

private theorem blockRightDirs_contDiff {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (a : BlockSplit beta cs) (m : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ (m + blockOrder beta cs) f) :
    ContDiff ℝ m (blockRightDirs basis beta cs a f) := by
  induction cs generalizing m f with
  | nil => simpa [blockRightDirs, blockOrder] using hf
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [blockRightDirs]
      apply repDirs_contDiff_local
      apply ih
      apply hf.of_le
      exact_mod_cast (show m + (beta c - k) + blockOrder beta cs ≤
        m + blockOrder beta (c::cs) by simp [blockOrder]; omega)

private theorem blockDirs_mul {C : Type*} (basis : C → E) (beta : C → ℕ)
    (cs : List C) (f g : E → ℝ) (z : E)
    (hf : ContDiff ℝ (blockOrder beta cs) f)
    (hg : ContDiff ℝ (blockOrder beta cs) g) :
    blockDirs basis beta cs (fun x => f x * g x) z =
      ∑ a : BlockSplit beta cs, (blockCoeff beta cs a : ℝ) *
        blockLeftDirs basis beta cs a f z * blockRightDirs basis beta cs a g z := by
  classical
  induction cs generalizing f g z with
  | nil => simp [blockDirs, BlockSplit, blockCoeff, blockLeftDirs, blockRightDirs]
  | cons c cs ih =>
      rw [blockDirs]
      have hfun : blockDirs basis beta cs (fun x => f x * g x) = fun x =>
          ∑ a : BlockSplit beta cs, (blockCoeff beta cs a : ℝ) *
            (blockLeftDirs basis beta cs a f x * blockRightDirs basis beta cs a g x) := by
        funext x
        simpa [mul_assoc] using ih f g x
          (hf.of_le (by simp [blockOrder])) (hg.of_le (by simp [blockOrder]))
      rw [hfun]
      rw [repDirs_sum]
      · have hl : ∀ a : BlockSplit beta cs,
            ContDiff ℝ (beta c) (blockLeftDirs basis beta cs a f) := fun a =>
          blockLeftDirs_contDiff basis beta cs a (beta c) f
            (by simpa [blockOrder, add_comm, add_left_comm, add_assoc] using hf)
        have hr : ∀ a : BlockSplit beta cs,
            ContDiff ℝ (beta c) (blockRightDirs basis beta cs a g) := fun a =>
          blockRightDirs_contDiff basis beta cs a (beta c) g
            (by simpa [blockOrder, add_comm, add_left_comm, add_assoc] using hg)
        rw [Finset.sum_congr rfl (fun a _ =>
          repDirs_smul (basis c) (beta c)
            (blockCoeff beta cs a : ℝ)
            (fun x => blockLeftDirs basis beta cs a f x *
              blockRightDirs basis beta cs a g x) z ((hl a).mul (hr a)))]
        rw [Finset.sum_congr rfl (fun a _ => congrArg
          (fun q => (blockCoeff beta cs a : ℝ) * q)
          (repDirs_mul_binomial (basis c) (beta c)
            (blockLeftDirs basis beta cs a f)
            (blockRightDirs basis beta cs a g) z (hl a) (hr a)))]
        rw [sum_blockSplit_cons]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        change (blockCoeff beta cs k : ℝ) *
          (∑ j : Fin (beta c + 1), (Nat.choose (beta c) j : ℝ) *
            repDirs (basis c) j (blockLeftDirs basis beta cs k f) z *
            repDirs (basis c) (beta c - j) (blockRightDirs basis beta cs k g) z) = _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [blockCoeff, blockLeftDirs, blockRightDirs]
        rw [Nat.cast_mul]
        ring
      · intro a
        exact contDiff_const.mul
          ((blockLeftDirs_contDiff basis beta cs a (beta c)
            f (by simpa [blockOrder, add_comm, add_left_comm, add_assoc] using hf)).mul
           (blockRightDirs_contDiff basis beta cs a (beta c)
            g (by simpa [blockOrder, add_comm, add_left_comm, add_assoc] using hg)))

private def coordinateEquiv (d : ℕ) :
    Fin (Finset.univ.toList : List (TimeVelocityCoord d)).length ≃
      TimeVelocityCoord d :=
  List.Nodup.getEquivOfForallMemList _
    (Finset.nodup_toList (Finset.univ : Finset (TimeVelocityCoord d))) (by simp)

private def blockSplitEquivSplit (beta : TimeVelocityMultiIndex d) :
    BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)) ≃ Split beta :=
  (blockSplitEquivPi beta _).trans
    (Equiv.piCongrLeft (fun c => Fin (beta c + 1)) (coordinateEquiv d))

private theorem sum_blockSplit_eq_sum_split (beta : TimeVelocityMultiIndex d)
    (F : Split beta → ℝ) :
    ∑ a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)),
        F (blockSplitEquivSplit beta a) = ∑ gamma : Split beta, F gamma := by
  exact Equiv.sum_comp (blockSplitEquivSplit beta) F

private theorem blockCoeff_eq_prod_fin {C : Type*} [Fintype C]
    (beta : C → ℕ) (cs : List C) (a : BlockSplit beta cs) :
    blockCoeff beta cs a =
      ∏ i : Fin cs.length,
        Nat.choose (beta (cs.get i)) (blockSplitToFun beta cs a i) := by
  induction cs with
  | nil => cases a; simp [blockCoeff]
  | cons c cs ih =>
      rcases a with ⟨k, a⟩
      rw [blockCoeff]
      change Nat.choose (beta c) k * blockCoeff beta cs a =
        ∏ i : Fin (cs.length + 1),
          Nat.choose (beta ((c :: cs).get i))
            (blockSplitToFun beta (c :: cs) (k, a) i)
      rw [Fin.prod_univ_succ]
      simp only [blockSplitToFun, Fin.cases_zero, Fin.cases_succ, List.get_eq_getElem]
      rw [ih]
      rfl

private theorem blockCoeff_eq_choose (beta : TimeVelocityMultiIndex d)
    (a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d))) :
    blockCoeff beta _ a = beta.choose (blockSplitEquivSplit beta a).left := by
  classical
  rw [blockCoeff_eq_prod_fin]
  unfold choose Split.left blockSplitEquivSplit
  rw [← (coordinateEquiv d).prod_comp]
  apply Finset.prod_congr rfl
  intro i hi
  change Nat.choose (beta ((coordinateEquiv d) i))
      (blockSplitToFun beta _ a i) =
    Nat.choose (beta ((coordinateEquiv d) i))
      ((Equiv.piCongrLeft (fun c => Fin (beta c + 1)) (coordinateEquiv d))
        (blockSplitToFun beta _ a) ((coordinateEquiv d) i))
  have he := Equiv.piCongrLeft_apply_apply (fun c => Fin (beta c + 1))
    (coordinateEquiv d) (blockSplitToFun beta _ a) i
  exact congrArg (fun k : Fin (beta ((coordinateEquiv d) i) + 1) =>
    Nat.choose (beta ((coordinateEquiv d) i)) k) he.symm

private theorem dirs_eq_iteratedFDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (l : List E) (f : E → ℝ) (z : E)
    (hf : ContDiff ℝ l.length f) :
    dirs l f z =
      iteratedFDeriv ℝ l.length f z fun i => l.get i := by
  induction l generalizing f z with
  | nil => simp [dirs]
  | cons v l ih =>
      rw [dirs]
      change fderiv ℝ (dirs l f) z v =
        iteratedFDeriv ℝ (l.length + 1) f z
          (fun i => (v :: l).get i)
      rw [iteratedFDeriv_succ_apply_left]
      change fderiv ℝ (dirs l f) z v =
        fderiv ℝ (iteratedFDeriv ℝ l.length f) z v
          (fun i => l.get i)
      have hfun : dirs l f = fun y =>
          iteratedFDeriv ℝ l.length f y fun i => l.get i := by
        funext y
        exact ih f y (hf.of_le (by simp))
      rw [hfun]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ l.length f) z :=
        hf.differentiable_iteratedFDeriv (by
          exact_mod_cast Nat.lt_succ_self l.length) z
      rw [fderiv_continuousMultilinear_apply_const_apply hd]

variable {d : ℕ}

private theorem count_flatMap_replicate_of_nodup {C : Type*} [DecidableEq C]
    (m : C → ℕ) (cs : List C) (hcs : cs.Nodup) (x : C) :
    (cs.flatMap fun c => List.replicate (m c) c).count x =
      if x ∈ cs then m x else 0 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      rw [List.nodup_cons] at hcs
      simp only [List.flatMap_cons, List.count_append, List.count_replicate]
      rw [ih hcs.2]
      by_cases hxc : x = c
      · subst c
        simp [hcs.1]
      · have hcx : c ≠ x := Ne.symm hxc
        simp [hxc, hcx]

private def blockLeftList (beta : TimeVelocityMultiIndex d) :
    (cs : List (TimeVelocityCoord d)) → BlockSplit beta cs → List (TimeVelocity d)
  | [], _ => []
  | c :: cs, (k,a) => List.replicate k (timeVelocityBasis c) ++ blockLeftList beta cs a

private def blockRightList (beta : TimeVelocityMultiIndex d) :
    (cs : List (TimeVelocityCoord d)) → BlockSplit beta cs → List (TimeVelocity d)
  | [], _ => []
  | c :: cs, (k,a) => List.replicate (beta c-k) (timeVelocityBasis c) ++
      blockRightList beta cs a

private theorem blockLeftDirs_eq_dirs (beta : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : BlockSplit beta cs)
    (f : TimeVelocity d → ℝ) :
    blockLeftDirs timeVelocityBasis beta cs a f = dirs (blockLeftList beta cs a) f := by
  induction cs generalizing f with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [blockLeftDirs, blockLeftList, dirs_append, ← repDirs_eq_dirs_replicate]
      exact congrArg (repDirs (timeVelocityBasis c) k) (ih a f)

private theorem blockRightDirs_eq_dirs (beta : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : BlockSplit beta cs)
    (f : TimeVelocity d → ℝ) :
    blockRightDirs timeVelocityBasis beta cs a f = dirs (blockRightList beta cs a) f := by
  induction cs generalizing f with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k,a⟩
      rw [blockRightDirs, blockRightList, dirs_append, ← repDirs_eq_dirs_replicate]
      exact congrArg (repDirs (timeVelocityBasis c) (beta c-k)) (ih a f)

variable {d : ℕ}

private theorem blockLeftList_eq_flatMap
    (beta gamma : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : BlockSplit beta cs)
    (h : ∀ i, gamma (cs.get i) = blockSplitToFun beta cs a i) :
    blockLeftList beta cs a =
      cs.flatMap fun c => List.replicate (gamma c) (timeVelocityBasis c) := by
  induction cs with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k, a⟩
      rw [blockLeftList, List.flatMap_cons]
      have hzero := h (⟨0, by simp⟩ : Fin (c :: cs).length)
      have htail : ∀ i, gamma (cs.get i) = blockSplitToFun beta cs a i := by
        intro i
        simpa [blockSplitToFun, Fin.cases_zero, Fin.cases_succ] using! h i.succ
      rw [ih a htail]
      congr 1
      simpa [blockSplitToFun, Fin.cases_zero, Fin.cases_succ] using! hzero.symm

private theorem blockRightList_eq_flatMap
    (beta gamma : TimeVelocityMultiIndex d)
    (cs : List (TimeVelocityCoord d)) (a : BlockSplit beta cs)
    (h : ∀ i, gamma (cs.get i) = blockSplitToFun beta cs a i) :
    blockRightList beta cs a =
      cs.flatMap fun c => List.replicate (beta c - gamma c) (timeVelocityBasis c) := by
  induction cs with
  | nil => cases a; rfl
  | cons c cs ih =>
      rcases a with ⟨k, a⟩
      rw [blockRightList, List.flatMap_cons]
      have hzero := h (⟨0, by simp⟩ : Fin (c :: cs).length)
      have htail : ∀ i, gamma (cs.get i) = blockSplitToFun beta cs a i := by
        intro i
        simpa [blockSplitToFun, Fin.cases_zero, Fin.cases_succ] using! h i.succ
      rw [ih a htail]
      congr 1
      change gamma c = (k : ℕ) at hzero
      rw [hzero]

private theorem split_pointwise (beta : TimeVelocityMultiIndex d)
    (a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)))
    (i : Fin (Finset.univ.toList : List (TimeVelocityCoord d)).length) :
    blockSplitEquivSplit beta a ((Finset.univ.toList).get i) =
      blockSplitToFun beta _ a i := by
  change ((Equiv.piCongrLeft (fun c => Fin (beta c + 1)) (coordinateEquiv d))
    (blockSplitToFun beta _ a)) ((coordinateEquiv d) i) = _
  simpa only [coordinateEquiv] using
    (Equiv.piCongrLeft_apply_apply (fun c => Fin (beta c + 1))
      (coordinateEquiv d) (blockSplitToFun beta _ a) i)

private theorem blockLeftList_eq_coordinateList (beta : TimeVelocityMultiIndex d)
    (a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d))) :
    blockLeftList beta _ a =
      (coordinateList (blockSplitEquivSplit beta a).left).map timeVelocityBasis := by
  rw [blockLeftList_eq_flatMap beta (blockSplitEquivSplit beta a).left _ a
    (fun i => congrArg Fin.val (split_pointwise beta a i))]
  unfold coordinateList
  rw [List.map_flatMap]
  simp [Split.left]

private theorem blockRightList_eq_coordinateList (beta : TimeVelocityMultiIndex d)
    (a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d))) :
    blockRightList beta _ a =
      (coordinateList (blockSplitEquivSplit beta a).right).map timeVelocityBasis := by
  rw [blockRightList_eq_flatMap beta (blockSplitEquivSplit beta a).left _ a
    (fun i => congrArg Fin.val (split_pointwise beta a i))]
  unfold coordinateList
  rw [List.map_flatMap]
  simp [Split.right]

private theorem length_coordinateList_local (beta : TimeVelocityMultiIndex d) :
    beta.coordinateList.length = beta.order := by
  simp [coordinateList, TimeVelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

private theorem order_mono_local {alpha beta : TimeVelocityMultiIndex d}
    (h : alpha ≤ beta) : alpha.order ≤ beta.order := by
  have hv : ∑ i, alpha (velocityCoord i) ≤ ∑ i, beta (velocityCoord i) :=
    Finset.sum_le_sum fun i _ => h (velocityCoord i)
  have ht := h (timeCoord d)
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order] at *
  omega

private theorem dirs_ofFn_eq_iteratedFDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (v : Fin n → E) (f : E → ℝ) (z : E)
    (hf : ContDiff ℝ n f) :
    dirs (List.ofFn v) f z =
      iteratedFDeriv ℝ n f z v := by
  induction n generalizing f z with
  | zero => simp [dirs]
  | succ n ih =>
      rw [List.ofFn_succ, dirs]
      rw [iteratedFDeriv_succ_apply_left]
      have hfun : dirs
          (List.ofFn fun i => v i.succ) f = fun y =>
            iteratedFDeriv ℝ n f y fun i => v i.succ := by
        funext y
        exact ih (fun i => v i.succ) f y (hf.of_le (by simp))
      rw [hfun]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) z :=
        hf.differentiable_iteratedFDeriv (by
          exact_mod_cast Nat.lt_succ_self n) z
      change fderiv ℝ (fun y =>
        iteratedFDeriv ℝ n f y (fun i => v i.succ)) z (v 0) = _
      rw [fderiv_continuousMultilinear_apply_const_apply hd]
      rfl

private theorem blockLeftDirs_eq_coordinateIteratedFDeriv
    (beta : TimeVelocityMultiIndex d)
    (a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)))
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiff ℝ beta.order f) :
    blockLeftDirs timeVelocityBasis beta _ a f z =
      coordinateIteratedFDeriv (blockSplitEquivSplit beta a).left f z := by
  rw [blockLeftDirs_eq_dirs, blockLeftList_eq_coordinateList]
  have hlist : (coordinateList (blockSplitEquivSplit beta a).left).map
      timeVelocityBasis = List.ofFn (fun i =>
        timeVelocityBasis ((coordinateList (blockSplitEquivSplit beta a).left).get i)) := by
    symm
    simpa using! congrArg (List.map timeVelocityBasis)
      (List.ofFn_get (coordinateList (blockSplitEquivSplit beta a).left))
  rw [hlist]
  unfold coordinateIteratedFDeriv
  apply dirs_ofFn_eq_iteratedFDeriv
  apply hf.of_le
  rw [length_coordinateList_local]
  exact_mod_cast order_mono_local fun c =>
    Nat.le_of_lt_succ ((blockSplitEquivSplit beta a) c).isLt

private theorem blockRightDirs_eq_coordinateIteratedFDeriv
    (beta : TimeVelocityMultiIndex d)
    (a : BlockSplit beta (Finset.univ.toList : List (TimeVelocityCoord d)))
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiff ℝ beta.order f) :
    blockRightDirs timeVelocityBasis beta _ a f z =
      coordinateIteratedFDeriv (blockSplitEquivSplit beta a).right f z := by
  rw [blockRightDirs_eq_dirs, blockRightList_eq_coordinateList]
  have hlist : (coordinateList (blockSplitEquivSplit beta a).right).map
      timeVelocityBasis = List.ofFn (fun i =>
        timeVelocityBasis ((coordinateList (blockSplitEquivSplit beta a).right).get i)) := by
    symm
    simpa using! congrArg (List.map timeVelocityBasis)
      (List.ofFn_get (coordinateList (blockSplitEquivSplit beta a).right))
  rw [hlist]
  unfold coordinateIteratedFDeriv
  apply dirs_ofFn_eq_iteratedFDeriv
  apply hf.of_le
  rw [length_coordinateList_local]
  exact_mod_cast order_mono_local fun c => Nat.sub_le _ _

private theorem blockOrder_univ (beta : TimeVelocityMultiIndex d) :
    blockOrder beta (Finset.univ.toList : List (TimeVelocityCoord d)) = beta.order := by
  simp [blockOrder, TimeVelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

private theorem map_flatMap_replicate {C E : Type*} (basis : C → E)
    (m : C → ℕ) (cs : List C) :
    (cs.flatMap fun c => List.replicate (m c) c).map basis =
      cs.flatMap fun c => List.replicate (m c) (basis c) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_replicate]
      rw [ih]

private theorem blockDirs_univ_eq_coordinateIteratedFDeriv
    (beta : TimeVelocityMultiIndex d) (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d) (hf : ContDiff ℝ beta.order f) :
    blockDirs timeVelocityBasis beta
        (Finset.univ.toList : List (TimeVelocityCoord d)) f z =
      coordinateIteratedFDeriv beta f z := by
  rw [blockDirs_eq_dirs_flatMap]
  have hlist :
      ((Finset.univ.toList : List (TimeVelocityCoord d)).flatMap fun c =>
        List.replicate (beta c) (timeVelocityBasis c)) =
      List.ofFn (fun i => timeVelocityBasis (beta.coordinateList.get i)) := by
    calc
      _ = beta.coordinateList.map timeVelocityBasis := by
        exact (map_flatMap_replicate timeVelocityBasis beta _).symm
      _ = _ := by
        symm
        simpa using! congrArg (List.map timeVelocityBasis)
          (List.ofFn_get beta.coordinateList)
  rw [hlist]
  unfold coordinateIteratedFDeriv
  apply dirs_ofFn_eq_iteratedFDeriv
  simpa [length_coordinateList_local] using hf

/-- Exact coordinate multi-index Leibniz formula for actual classical
derivatives. -/
theorem coordinateIteratedFDeriv_mul
    (beta : TimeVelocityMultiIndex d) (f g : TimeVelocity d → ℝ)
    (z : TimeVelocity d)
    (hf : ContDiff ℝ beta.order f) (hg : ContDiff ℝ beta.order g) :
    coordinateIteratedFDeriv beta (fun x => f x * g x) z =
      ∑ gamma : Split beta,
        (beta.choose gamma.left : ℝ) *
          coordinateIteratedFDeriv gamma.left f z *
          coordinateIteratedFDeriv gamma.right g z := by
  classical
  let cs : List (TimeVelocityCoord d) := Finset.univ.toList
  calc
    coordinateIteratedFDeriv beta (fun x => f x * g x) z =
        blockDirs timeVelocityBasis beta cs (fun x => f x * g x) z := by
      exact (blockDirs_univ_eq_coordinateIteratedFDeriv beta _ z
        (hf.mul hg)).symm
    _ = ∑ a : BlockSplit beta cs, (blockCoeff beta cs a : ℝ) *
          blockLeftDirs timeVelocityBasis beta cs a f z *
          blockRightDirs timeVelocityBasis beta cs a g z := by
      apply blockDirs_mul
      · simpa [cs, blockOrder_univ] using hf
      · simpa [cs, blockOrder_univ] using hg
    _ = ∑ a : BlockSplit beta cs,
          (beta.choose (blockSplitEquivSplit beta a).left : ℝ) *
            coordinateIteratedFDeriv (blockSplitEquivSplit beta a).left f z *
            coordinateIteratedFDeriv (blockSplitEquivSplit beta a).right g z := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [blockCoeff_eq_choose,
        blockLeftDirs_eq_coordinateIteratedFDeriv beta a f z hf,
        blockRightDirs_eq_coordinateIteratedFDeriv beta a g z hg]
    _ = _ := by
      exact sum_blockSplit_eq_sum_split beta (fun gamma =>
        (beta.choose gamma.left : ℝ) *
          coordinateIteratedFDeriv gamma.left f z *
          coordinateIteratedFDeriv gamma.right g z)

/-- Coordinate iterated derivatives depend only on the germ of a function at
the evaluation point. -/
theorem coordinateIteratedFDeriv_congr_of_eventuallyEq
    (beta : TimeVelocityMultiIndex d)
    {f g : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hfg : f =ᶠ[nhds z] g) :
    coordinateIteratedFDeriv beta f z =
      coordinateIteratedFDeriv beta g z := by
  unfold coordinateIteratedFDeriv
  exact congrArg
    (fun L => L (fun i => timeVelocityBasis (beta.coordinateList.get i)))
    (hfg.iteratedFDeriv ℝ beta.coordinateList.length).self_of_nhds

/-- On an open set, pointwise equality gives equality of every actual
coordinate iterated derivative at each point of that set. -/
theorem coordinateIteratedFDeriv_congr_of_eqOn
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (beta : TimeVelocityMultiIndex d)
    {f g : TimeVelocity d → ℝ}
    (hfg : Set.EqOn f g U)
    (z : TimeVelocity d) (hz : z ∈ U) :
    coordinateIteratedFDeriv beta f z =
      coordinateIteratedFDeriv beta g z := by
  apply coordinateIteratedFDeriv_congr_of_eventuallyEq beta
  filter_upwards [hU.mem_nhds hz] with x hx
  exact hfg hx

/-- Pointwise finite-order addition rule for actual coordinate derivatives. -/
theorem coordinateIteratedFDeriv_add_at
    (beta : TimeVelocityMultiIndex d)
    (f g : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ beta.order f z)
    (hg : ContDiffAt ℝ beta.order g z) :
    coordinateIteratedFDeriv beta (fun x ↦ f x + g x) z =
      coordinateIteratedFDeriv beta f z +
        coordinateIteratedFDeriv beta g z := by
  unfold coordinateIteratedFDeriv
  have hf' : ContDiffAt ℝ beta.coordinateList.length f z := by simpa using hf
  have hg' : ContDiffAt ℝ beta.coordinateList.length g z := by simpa using hg
  simpa only [Pi.add_def] using! congrArg
    (fun L => L (fun i => timeVelocityBasis (beta.coordinateList.get i)))
    (iteratedFDeriv_add_apply hf' hg')

/-- Pointwise finite-sum rule for actual coordinate derivatives. -/
theorem coordinateIteratedFDeriv_sum_at
    {A : Type*} [Fintype A]
    (beta : TimeVelocityMultiIndex d)
    (f : A → TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ∀ a, ContDiffAt ℝ beta.order (f a) z) :
    coordinateIteratedFDeriv beta (fun x ↦ ∑ a, f a x) z =
      ∑ a, coordinateIteratedFDeriv beta (f a) z := by
  classical
  induction (Finset.univ : Finset A) using Finset.induction_on with
  | empty =>
      unfold coordinateIteratedFDeriv
      simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [coordinateIteratedFDeriv_add_at]
      · rw [ih]
      · exact hf a
      · exact ContDiffAt.sum fun b _ => hf b


end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
