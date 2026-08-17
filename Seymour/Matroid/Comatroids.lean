import Seymour.Matroid.Duality
import Seymour.Matroid.Graphicness

open scoped Classical
open scoped Matrix

section typing_hell

private lemma l1_aux {α β γ : Type*} (X Y Z : Set α) (hZ : Y ∪ X = Z) (z : Z.Elem) (f : β → (Y ∪ X).Elem → γ) (j : β) :
    (hZ ▸ f) j z = (hZ ▸ f j) z := by
  subst hZ
  rfl

private lemma l1 {α β : Type*} [DecidableEq α] (X Y : Set α) (i : X.Elem) (j : Y.Elem) (A : Y.Elem → Y.Elem → β) (B : Y.Elem → X.Elem → β) :
    ((Set.union_comm X Y).symm ▸
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ =
    ((Set.union_comm X Y).symm ▸ (
    fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ⟨i.val, Set.subset_union_left i.property⟩ := by
  apply l1_aux

private lemma l2_aux {α β : Type*} (X Y Z : Set α) (hZ : Y ∪ X = Z) (z : Z.Elem) (f : (Y ∪ X).Elem → β) :
    (hZ ▸ f) z = f (hZ ▸ z) := by
  subst hZ
  rfl

private lemma l2 {α β : Type*} [DecidableEq α] (X Y : Set α) (i : X.Elem) (j : Y.Elem) (A : Y.Elem → Y.Elem → β) (B : Y.Elem → X.Elem → β) :
    ((Set.union_comm X Y).symm ▸ (
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ⟨i.val, Set.subset_union_left i.property⟩ =
    ((fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ((Set.union_comm X Y).symm ▸ ⟨i.val, Set.subset_union_left i.property⟩) := by
  apply l2_aux

private lemma ll {α β : Type*} [DecidableEq α] (X Y : Set α) (i : X.Elem) (j : Y.Elem) (A : Matrix Y.Elem Y.Elem β) (B : Matrix Y.Elem X.Elem β) :
    ((Set.union_comm X Y).symm ▸
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ =
    (fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_right i.property⟩ := by
  rw [l1, l2]
  congr
  ext
  apply Subtype.subst_elem

private lemma l1' {α β : Type*} [DecidableEq α] (X Y : Set α) (i : Y.Elem) (j : Y.Elem) (A : Y.Elem → Y.Elem → β) (B : Y.Elem → X.Elem → β) :
    ((Set.union_comm X Y).symm ▸
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_right i.property⟩ =
    ((Set.union_comm X Y).symm ▸ (
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ⟨i.val, Set.subset_union_right i.property⟩ := by
  apply l1_aux

private lemma l2' {α β : Type*} [DecidableEq α] (X Y : Set α) (i : Y.Elem) (j : Y.Elem) (A : Y.Elem → Y.Elem → β) (B : Y.Elem → X.Elem → β) :
    ((Set.union_comm X Y).symm ▸ (
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ⟨i.val, Set.subset_union_right i.property⟩ =
    ((fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j) ((Set.union_comm X Y).symm ▸ ⟨i.val, Set.subset_union_right i.property⟩) := by
  apply l2_aux

private lemma ll' {α β : Type*} [DecidableEq α] (X Y : Set α) (i : Y.Elem) (j : Y.Elem) (A : Matrix Y.Elem Y.Elem β) (B : Matrix Y.Elem X.Elem β) :
    ((Set.union_comm X Y).symm ▸
      fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_right i.property⟩ =
     (fun x : Y.Elem => (fun y : Y.Elem => Sum.elim (A y) (B y)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ := by
  rw [l1', l2']
  congr
  ext
  apply Subtype.subst_elem

private lemma eq_rec_set_apply {α R : Type*} {X Y1 Y2 : Set α}
  (h : Y1 = Y2) (f : ↑X → ↑Y1 → R) (i : ↑X) (j : ↑Y2) :
  Eq.rec (motive := fun (x : Set α) _ => ↑X → ↑x → R) f h i j = 
  f i (Eq.rec (motive := fun (x : Set α) _ => ↑x) j h.symm) := by
  subst h
  rfl
private lemma cast_val_eq {α : Type*} {s t : Set α} (h : s = t) (x : α) (hx : x ∈ s) :
  ↑(h ▸ Subtype.mk x hx : ↥t) = x := by
  subst h
  rfl

end typing_hell



variable {α R : Type*} [Field R]



lemma Matroid.isBase_ncard {M : Matroid α} (hM : M.RankFinite) {I J : Set α} (h_size : I.ncard = J.ncard) (hI : M.IsBase I) (hJ : M.Indep J) :
    M.IsBase J := by
  rw [Matroid.isBase_iff_maximal_indep]
  simp only [Maximal, hJ, Set.le_eq_subset, true_and]
  intro y hY hJ_y
  obtain ⟨B, ⟨hB_base, hB_subset⟩⟩ := hY.exists_isBase_superset
  obtain ⟨finite_base, h_finite_base⟩  := hM.exists_finite_isBase
  have hB_is_finite := h_finite_base.1.finite_of_finite h_finite_base.2 hB_base
  have hy_is_finite := hB_is_finite.subset hB_subset
  have : y.ncard ≤ J.ncard := by
    have : B.ncard = J.ncard := by
      rw [← h_size]
      have x := (Matroid.isBase_exchange M).encard_isBase_eq hB_base hI
      apply_fun ENat.toNat at x
      change B.ncard = I.ncard at x
      exact x
    rw [←this]
    have := Set.encard_le_encard hB_subset
    exact Set.ncard_le_ncard hB_subset hB_is_finite

  exact (Set.eq_of_subset_of_ncard_le hJ_y this hy_is_finite).symm.subset

lemma Matrix.almost_square_transpose_LinearIndependent {A B : Set α} [Fintype A] [Fintype B] (N : Matrix A B R) (h_card : #A = #B) :
    LinearIndependent R N → LinearIndependent R Nᵀ := by
  intro hN_rows
  rw [linearIndependent_iff_card_eq_finrank_span] at hN_rows
  rw [linearIndependent_iff_card_eq_finrank_span, ← h_card, hN_rows]
  have {U V : Set α}[Fintype U][Fintype V](M : Matrix U V R): Set.finrank R (Set.range M) = M.rank := by
    rw [Matrix.rank_eq_finrank_span_row M]
    rfl
  repeat rw [this]
  exact (Matrix.rank_transpose N).symm



variable [DecidableEq α]



lemma StandardRepr.toMatroid.isBase_iff {S : StandardRepr α R} [Fintype S.X] [Fintype S.Y] {I : Set α} (hI : I ⊆ (S.X ∪ S.Y)) :
    S.toMatroid.IsBase I ↔ (I.ncard = S.X.ncard ∧ LinearIndependent R (S.toFull.submatrix id hI.elem : Matrix S.X I R)ᵀ ) := by
  set small : Matrix S.X I R := S.toFull.submatrix id hI.elem 
  constructor
  · intro hI_base
    have hI_size : I.ncard = S.X.ncard := by
      have := (S.toMatroid.isBase_exchange).encard_isBase_eq hI_base S.toMatroid_isBase_X
      apply_fun ENat.toNat at this
      change I.ncard = S.X.ncard at this
      exact this
    simp only [hI_size, true_and]
    rw [StandardRepr.toMatroid, Matrix.toMatroid, IndepMatroid.matroid_IsBase, Maximal] at hI_base
    have : S.toMatroid.Indep I := hI_base.1
    rw [StandardRepr.toMatroid_indep_iff_submatrix] at this
    obtain ⟨hI, this⟩ := this
    convert this
  intro ⟨hI_size, linear_indep⟩
  apply Matroid.isBase_ncard (S.toMatroid_rankFinite_of_finite_X) hI_size.symm S.toMatroid_isBase_X
  rw [StandardRepr.toMatroid_indep_iff_submatrix]
  use hI
  convert linear_indep

private lemma dual_standardrepr_dual_matroid_helper (S S' : StandardRepr α R) [Fintype S.X][Fintype S.Y][Fintype S'.X][Fintype S'.Y](I : Set α)[Fintype I]
    (hXY : S.X = S'.Y) (hYX : S.Y = S'.X) (hI : I ⊆ (S.X ∪ S.Y)) (hSize : I.ncard = S.X.ncard) :
    let M : Matrix S.X (S.X ∪ S.Y).Elem R := S.toFull
    let N : Matrix S.Y (S.X ∪ S.Y).Elem R := hXY ▸ hYX ▸ Set.union_comm S'.Y S'.X ▸ S'.toFull
    M * Nᵀ = 0 →
    let M' : Matrix S.X I R := M.submatrix id hI.elem
    let N' : Matrix S.Y ((S.X ∪ S.Y) \ I).Elem R := N.submatrix id Set.diff_subset.elem
    LinearIndependent R M'ᵀ → LinearIndependent R N'ᵀ
    := by
  intro M N h0 M' N' hM'
  by_contra hN'
  let U := (S.X ∪ S.Y).Elem
  let p := fun (x : U) => x.val ∈ I

  have : ¬ LinearIndependent R N' := by
    intro hN_rows
    apply hN'
    have : #(S.Y) = #↑((S.X ∪ S.Y) \ I) := by
      repeat rw [Fintype.card_eq_nat_card]
      convert_to S.Y.ncard = ((S.X ∪ S.Y) \ I).ncard
      rw [Set.ncard_diff hI, Set.ncard_union_eq S.hXY]
      simp [hSize]
    apply Matrix.almost_square_transpose_LinearIndependent N' 
    convert this
    exact hN_rows

  have hN'2 : ∃ e: S.Y → R, N'ᵀ *ᵥ e = 0 ∧ e ≠ 0 := by
    obtain ⟨e, h_sum, h_nz⟩ := Fintype.not_linearIndependent_iff.mp this
    use e
    constructor
    · ext i
      have h_sum_i := congr_fun h_sum i
      rw [←h_sum_i]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · simp only [ne_eq]
      intro h
      obtain ⟨i, hi⟩ := h_nz
      exact hi (congr_fun h i)

  have hM'_isFull (e : I → R) : M' *ᵥ e = 0 → e = 0 := by 
    intro h_mul
    ext i
    apply Fintype.linearIndependent_iff.mp hM' e
    unfold Matrix.mulVec dotProduct at h_mul
    simp only at h_mul
    rw [← h_mul]
    ext x
    simp [mul_comm]
  have : LinearIndependent R N := by
    apply Fintype.linearIndependent_iff.mpr 
    intro g hg j
    rw [funext_iff] at hg
    have := hg ⟨j, Set.subset_union_right j.2⟩
    unfold N StandardRepr.toFull at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have : ∑ x : S.Y, g x * (1 : Matrix S.Y S.Y R) x j = 0 := by
      rw [← this]
      apply Fintype.sum_congr
      intro i
      congr 1
      simp only [Matrix.fromCols]
      clear this hg g hM'_isFull hN'2 p U hN' hM' M' h0 
      clear this N' N M hSize hI
      generalize hX : S.X = AX at *
      generalize hY : S.Y = AY at *
      subst hXY 
      subst hYX
      simp only
      rw [eq_rec_set_apply (Set.union_comm S'.X S'.Y)]
      simp only [Function.comp_apply, Subtype.toSum, Matrix.of_apply]
      split 
      · simp only [Sum.elim_inl]
        next h =>
          apply congrArg
          ext
          rw [cast_val_eq]
      · next h_not =>
          rw [cast_val_eq] at h_not
          exact False.elim (h_not j.property)
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at this
    exact this

  have hN_isFull (e : S.Y → R) :  Nᵀ *ᵥ e = 0 → e = 0 := by 
    intro h_mul
    ext i
    apply Fintype.linearIndependent_iff.mp this e
    unfold Matrix.mulVec dotProduct at h_mul
    simp only [Matrix.transpose_apply] at h_mul
    rw [← h_mul]
    ext x
    simp [mul_comm]
  let e_I : I ≃ { x : (S.X ∪ S.Y).Elem // p x } := {
    toFun := fun x => ⟨⟨x.val, hI x.prop⟩, x.prop⟩
    invFun := fun x => ⟨x.val.val, x.prop⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl
  }
  obtain ⟨e, he1⟩ := hN'2
  let v := Nᵀ *ᵥ e
  have he2 := hN_isFull e
  let v' : I → R := fun j => v ⟨j.val, hI j.prop⟩
  have he3 := hM'_isFull v'
  have he4 : M *ᵥ v = 0 := by -- from h0 and v
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  have hi : ∀ i : {x : U // ¬ p x}, v i = 0 := by -- from he1.1, N' and v
    intro i
    have := he1.1
    let i_cast : ↑((S.X ∪ S.Y) \ I) := ⟨i.val.val, ⟨i.val.property, i.property⟩⟩
    have hi := congr_fun this i_cast
    exact hi
  have he6 : M' *ᵥ v' = 0 := by
    ext i 
    have h4_i := congr_fun he4 i
    rw [← h4_i]
    simp only [M', Matrix.mulVec, Matrix.submatrix, dotProduct, v', id_eq, HasSubset.Subset.elem, Matrix.of_apply]
    symm
    have : ∑ x : U, M i x * v x = ∑ x : {x : U // p x}, M i x * v x + ∑ x : {x : U // ¬ p x}, M i x * v x := by
      classical
      symm
      exact Fintype.sum_subtype_add_sum_subtype (fun x => x.val ∈ I) (fun x => M i x * v x)

    have hh : ∑ x : {x : U // ¬ p x}, M i x * v x = 0 := by
      simp [p, hi]
    simp only [hh, add_zero, U, p, M] at this
    rw [this]
    symm
    exact Equiv.sum_comp e_I (fun x => M i x * v x)

  have v'_is_zero : v' = 0 := he3 he6
  clear he3 he6 
  have v_is_zero : v = 0 := by
    ext i
    by_cases h : p i
    · have h_in := congr_fun v'_is_zero ⟨i.val, h⟩
      exact h_in
    · exact hi ⟨i, h⟩
  exact he1.2 (he2 v_is_zero)

private lemma StandardDualOrto  (S : StandardRepr α R) [Fintype S.X][Fintype S.Y]:
    S.toFull * (Set.union_comm S.X S.Y ▸ S.dual.toFull)ᵀ = 0 := by
  unfold StandardRepr.toFull StandardRepr.dual
  dsimp only
  ext i j
  simp only [Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.fromCols]
  rw [←S.hXY.equivSumUnion.sum_comp, Fintype.sum_sum_type]
  conv_lhs => congr; simp only [equivSumUnion_apply_left, Function.comp_apply, Subtype.coe_prop,
    toSum_left, Subtype.coe_eta, Matrix.of_apply, Sum.elim_inl]; rw [sum_one_times_matrix]
  show ((Set.union_comm S.X S.Y).symm ▸
    fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j ⟨i.val, _⟩
    + _ = (0 : R)
  have hh :
      ((Set.union_comm S.X S.Y).symm ▸
        fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_left i.property⟩ =
       (fun x : S.Y.Elem => (fun i : S.Y.Elem => Sum.elim ((1 : Matrix S.Y.Elem S.Y.Elem R) i) ((-S.Bᵀ) i)) x ∘ Subtype.toSum) j ⟨i.val, Set.subset_union_right i.property⟩
  · convert ll S.X S.Y i j 1 (-S.Bᵀ)
  rw [hh]
  have hiY : i.val ∉ S.Y
  · exact S.hXY.ni_right_of_in_left i.property
  simp only [Function.comp_apply, Subtype.toSum, hiY, ↓reduceDIte, Subtype.coe_prop,
    Subtype.coe_eta, Sum.elim_inr, Matrix.neg_apply, Matrix.transpose_apply,
    equivSumUnion_apply_right, Matrix.of_apply]

  convert neg_add_cancel (S.B i j)
  have hSYX : ∀ y : S.Y, y.val ∉ S.X := (S.hXY.ni_left_of_in_right ·.property)
  conv_lhs => congr; rfl; ext y; simp only [hSYX, ↓reduceDIte, Sum.elim_inr]
  clear hSYX
  have hh : ∀ y : S.Y,
      ((Set.union_comm S.X S.Y).symm ▸
        fun x : S.Y => Matrix.of (fun i : S.Y => (1 : Matrix S.Y S.Y R) i ⊕ᵥ (-S.Bᵀ) i) x ∘ Subtype.toSum) j ⟨y.val, Set.subset_union_right y.property⟩ =
      (1 : Matrix S.Y S.Y R) j y
  · intro y
    show
      ((Set.union_comm S.X S.Y).symm ▸
        fun x : S.Y => (fun i : S.Y => (1 : Matrix S.Y S.Y R) i ⊕ᵥ (-S.Bᵀ) i) x ∘ Subtype.toSum) j ⟨y.val, Set.subset_union_right y.property⟩ =
      (1 : Matrix S.Y S.Y R) j y
    convert ll' S.X S.Y y j 1 (-S.Bᵀ)
    simp
  simp_rw [hh]
  rw [sum_matrix_times_one]

private lemma dual_toMatroid_one_way {I : Set α}(S : StandardRepr α R) (hI : I ⊆ S.dual.toMatroid.E) [Fintype S.X][Fintype S.Y]: S.toMatroid.IsBase I → S.dual.toMatroid.IsBase (S.dual.toMatroid.E \ I) := by
  intro hI_base
  set J := S.toMatroid.E \ I

  have same_E : S.toMatroid.E = S.dual.toMatroid.dual.E := by simp [StandardRepr.dual, Set.union_comm]
  have same_E2 : S.toMatroid.E = S.dual.toMatroid.E := by simp [StandardRepr.dual, Set.union_comm]
  have hI_size : I.ncard = S.X.ncard := congr_arg ENat.toNat ((S.toMatroid.isBase_exchange).encard_isBase_eq hI_base S.toMatroid_isBase_X)
  have hJ : J ⊆ S.dual.toMatroid.E := by unfold J; rw [same_E2]; exact Set.diff_subset
  have : Fintype S.dual.X := by dsimp [StandardRepr.dual]; assumption
  have : Fintype S.dual.Y := by dsimp [StandardRepr.dual]; assumption
  have hI' := by dsimp [J, StandardRepr.dual] at hI; rw [Set.union_comm] at hI; exact hI
  have h_union_fin : (S.X ∪ S.Y).Finite := (Set.toFinite S.X).union (Set.toFinite S.Y)
  have : Fintype ↑I := by exact (Set.Finite.subset h_union_fin hI').fintype
  
  rw [← same_E2, StandardRepr.toMatroid.isBase_iff (S := S.dual) (hI := hJ)]
  rw [StandardRepr.toMatroid.isBase_iff (S := S) (I := I) (hI := by rw [← same_E2] at hI; exact hI)] at hI_base

  constructor
  · convert_to (S.X ∪ S.Y).ncard - I.ncard = S.Y.ncard
    · rw [Set.ncard_diff, S.toMatroid_E]
      exact hI' 
    · have : S.X.ncard + S.Y.ncard = (S.X ∪ S.Y).ncard := by rw [Set.ncard_union_eq S.hXY]
      omega
  · 
    have := dual_standardrepr_dual_matroid_helper S S.dual I rfl rfl (subset_of_subset_of_eq hI same_E.symm) hI_size (StandardDualOrto S)
    set M := S.dual.toFull
    set N := S.toFull
    have t := this hI_base.2
    clear hI_base this N
    simp only [Matrix.transpose_submatrix] at t
    simp only [J, S.toMatroid_E]
    have h : S.dual.X = S.Y := by dsimp [StandardRepr.dual]
    convert t using 1
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, id]
    revert M
    congr! with M t
    generalize_proofs h_eq h_1
    have h_set : S✶.Y ∪ S✶.X = S✶.X ∪ S✶.Y := Set.union_comm S✶.Y S✶.X
    apply eq_of_heq

    have elim_cast (U : Set α) (heq : S.dual.X ∪ S.dual.Y = U) (elem_r : U) : elem_r.val = ↑r → HEq (M c (hJ.elem r)) ((heq ▸ M) c elem_r) := by
      intro h_val
      subst heq
      apply heq_of_eq
      congr 1
      apply Subtype.ext
      exact h_val.symm
    apply elim_cast (S✶.Y ∪ S✶.X) h_eq (h_1.elem r)
    rfl

lemma StandardRepr.dual_toMatroid_dual (S : StandardRepr α R) [Fintype S.X][Fintype S.Y]:
    S.toMatroid = S.dual.toMatroid.dual := by
  rw [Matroid.ext_iff_isBase]
  have same_E : S.toMatroid.E = S.dual.toMatroid.dual.E := by simp [StandardRepr.dual, Set.union_comm]
  have same_E2 : S.toMatroid.E = S.dual.toMatroid.E := by simp [StandardRepr.dual, Set.union_comm]
  constructor
  · exact same_E
  · intro I hI
    rw [Matroid.dual_isBase_iff']
    rw [same_E, Matroid.dual_ground] at hI
    simp only [hI, and_true]
    constructor
    · have := dual_toMatroid_one_way S hI
      exact this
    · set J := S.toMatroid.E \ I
      set hJ : J ⊆ S.toMatroid.E := Set.diff_subset
      have : Fintype S.dual.X := by
        dsimp [StandardRepr.dual]
        assumption
      have : Fintype S.dual.Y := by
        dsimp [StandardRepr.dual]
        assumption
      have := dual_toMatroid_one_way S.dual hJ
      simp only [Matrix.toMatroid_E, StandardRepr.dual_dual, sdiff_sdiff_right_self, Set.inf_eq_inter, J] at this
      convert_to S✶.toMatroid.IsBase ((S.X ∪ S.Y) \ I) → S.toMatroid.IsBase ((S.X ∪ S.Y) ∩ I)
      · rw [←same_E2]
        simp
      · rw [←same_E2] at hI
        dsimp at hI
        rw [Set.inter_eq_right.mpr hI]
      · exact this

lemma StandardRepr.dual_toMatroid (S : StandardRepr α R) [Fintype S.X][Fintype S.Y]:
    S.dual.toMatroid = S.toMatroid.dual := by
  rw [Matroid.eq_dual_comm]
  exact StandardRepr.dual_toMatroid_dual S

lemma Matroid.isRegular.dual {M : Matroid α} (hM : M.IsRegular) (hM_is_finite : M.Finite):
    (M✶).IsRegular := by
  obtain ⟨X, Y, x, hTU, hEq⟩ := hM
  obtain ⟨someBase, h_someBase⟩ := x.toMatroid.exists_isBase
  have h_someBase_finite : Fintype someBase := by
    have := h_someBase.subset_ground
    rw [hEq] at this
    exact (hM_is_finite.ground_finite.subset this).fintype
  obtain ⟨S, _, hS, hSTU⟩ := x.exists_standardRepr_isBase_isTotallyUnimodular h_someBase hTU 
  have x_finite: Fintype S.X := by
    have := Matroid.rankFinite_of_finite M
    rw [← hEq, ← hS] at this
    have := S.toMatroid_indep_X
    exact this.finite.fintype

  have y_finite: Fintype S.Y := by
    have x := hM_is_finite.ground_finite
    rw [← hEq, ← hS] at x
    have := S.toMatroid_E
    have h_sub : S.Y ⊆ S.toMatroid.E := by
      rw [this]
      exact Set.subset_union_right 
    have hY_fin : S.Y.Finite := x.subset h_sub
    exact hY_fin.fintype

  let S' := S.dual
  refine ⟨S'.X, S'.X ∪ S'.Y, S'.toFull, ?_⟩
  constructor
  · change Matrix.IsTotallyUnimodular (((1 : Matrix S.Y S.Y _) ◫ -S.Bᵀ) · ∘ Subtype.toSum)
    have h1 : S.Bᵀ.IsTotallyUnimodular := by 
      rw [← Matrix.transpose_isTotallyUnimodular_iff] at hSTU
      exact hSTU
    have h2 : (-S.Bᵀ).IsTotallyUnimodular := h1.neg
    have h3 : (1 ◫ -S.Bᵀ).IsTotallyUnimodular := h2.one_fromCols
    exact Matrix.IsTotallyUnimodular.comp_cols h3 Subtype.toSum
  · convert_to S.dual.toMatroid = M.dual
    rw [StandardRepr.dual_toMatroid, hS, hEq]

lemma Matroid.IsCographic.isRegular {M : Matroid α} (hM_fin : M.Finite) (hM : M.IsCographic) :
    M.IsRegular := by
  have := Matroid.isRegular.dual (Matroid.IsGraphic.isRegular hM) M.dual_finite
  rw [Matroid.dual_dual] at this
  exact this
