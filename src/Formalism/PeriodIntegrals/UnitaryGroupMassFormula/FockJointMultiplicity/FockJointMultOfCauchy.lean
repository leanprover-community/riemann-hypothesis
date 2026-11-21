import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.GlobalTheory
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.IsBlockHighestWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KroneckerOneRightSwap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistFin

section
noncomputable section

open Matrix FockH1Action

namespace PI.WFJM.Shape

open PI.FJM

section Gen

variable {n : ℕ}

def αP (f : Fin n → ℚ) : Fin (nP f) → ℕ := fun i => ⌊f (Fin.castLE (nP_le_nW f) i)⌋₊

def αN (f : Fin n → ℚ) : Fin (nN f) → ℕ := fun i => ⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊

def lpos {m : ℕ} (α : Fin m → ℕ) : List ℤ := List.ofFn fun i => (α i : ℤ)

def lneg {m : ℕ} (α : Fin m → ℕ) : List ℤ := (List.ofFn fun i => -(α i : ℤ)).reverse

theorem length_lpos {m : ℕ} (α : Fin m → ℕ) : (lpos α).length = m := by simp [lpos]

theorem length_lneg {m : ℕ} (α : Fin m → ℕ) : (lneg α).length = m := by simp [lneg]

theorem pos_iff (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin n) :
    0 < f i ↔ (i : ℕ) < nP f := by
  classical
  unfold nP
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => 0 < f j) := by
      intro j hj
      rw [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj.lt_or_eq with h | h
      · exact hseg j i h hi
      · rw [h]; exact hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => 0 < f j) ⊆ Finset.Iio i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hji
      push_neg at hji
      rcases hji.lt_or_eq with h | h
      · exact hn (hseg i j h hj)
      · rw [h] at hn; exact hn hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem neg_iff (f : Fin n → ℚ) (hseg : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin n) :
    f i < 0 ↔ n - nN f ≤ (i : ℕ) := by
  classical
  unfold nN
  have hin := i.isLt
  constructor
  · intro hi
    have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun j => f j < 0) := by
      intro j hj
      rw [Finset.mem_Ici] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj.lt_or_eq with h | h
      · exact hseg i j h hi
      · rw [← h]; exact hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => f j < 0) ⊆ Finset.Ioi i := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Ioi]
      by_contra hji
      push_neg at hji
      rcases hji.lt_or_eq with h | h
      · exact hn (hseg j i h hj)
      · rw [← h] at hn; exact hn hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    omega

theorem nP_add_nN_le (f : Fin n → ℚ) : nP f + nN f ≤ n := by
  classical
  unfold nP nN
  have hdis : Finset.univ.filter (fun j => 0 < f j) ∩ Finset.univ.filter (fun j => f j < 0) = ∅ := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, not_lt]
    intro h; exact h.le
  have h1 := Finset.card_union_add_card_inter (Finset.univ.filter (fun j => 0 < f j))
    (Finset.univ.filter (fun j => f j < 0))
  rw [hdis, Finset.card_empty, add_zero] at h1
  have h2 := Finset.card_le_univ (Finset.univ.filter (fun j => 0 < f j) ∪ Finset.univ.filter (fun j => f j < 0))
  rw [Fintype.card_fin] at h2
  omega

theorem natFloor_of_int (x : ℚ) (z : ℤ) (hz : (z : ℚ) = x) (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ z := by rw [hz]; exact hx
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz0
  rw [← hz]
  push_cast
  rw [Nat.floor_natCast]

theorem getD_pad (x y : List ℤ) (k i : ℕ) : (pad x k y).getD i 0 =
    if h : i < x.length then ((x[i] : ℤ) : ℚ) else if i < x.length + k then 0
      else ((y.getD (i - x.length - k) 0 : ℤ) : ℚ) := by
  unfold pad
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left h1]
    simp [h1]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
    simp [List.getElem?_replicate, show i - x.length < k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate]
    rw [List.getD_eq_getElem?_getD]
    have : i - (x.length + k) = i - x.length - k := by omega
    rw [this]
    cases y[i - x.length - k]? <;> simp

theorem getD_lneg {m : ℕ} (α : Fin m → ℕ) (t : ℕ) (ht : t < m) :
    (lneg α).getD t 0 = -(α ⟨m - 1 - t, by omega⟩ : ℤ) := by
  unfold lneg
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simpa using ht)]
  simp [show m - 1 - t < m by omega]

theorem eq_pad (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0)
    (i : Fin n) :
    f i = (pad (lpos (αP f)) (n - (lpos (αP f)).length - (lneg (αN f)).length) (lneg (αN f))).getD i 0 := by
  have hAB := nP_add_nN_le f
  have hi := i.isLt
  simp only [getD_pad, length_lpos, length_lneg]
  split_ifs with h1 h2
  ·
    have hpos : 0 < f i := (pos_iff f hp i).2 h1
    simp only [lpos, List.getElem_ofFn, αP]
    have hci : Fin.castLE (nP_le_nW f) ⟨(i : ℕ), h1⟩ = i := Fin.ext rfl
    rw [hci]
    push_cast
    exact (natFloor_of_int (f i) ⌊f i⌋ (hint i) hpos.le).symm
  ·
    have hnp : ¬ 0 < f i := fun h => h1 ((pos_iff f hp i).1 h)
    have hnn : ¬ f i < 0 := fun h => by have := (neg_iff f hn i).1 h; omega
    linarith [not_lt.1 hnp, not_lt.1 hnn]
  ·
    have hneg : f i < 0 := (neg_iff f hn i).2 (by omega)
    rw [getD_lneg _ _ (by omega)]
    simp only [αN]
    have hci : Fin.rev (Fin.castLE (nN_le f) ⟨nN f - 1 - (i - nP f - (n - nP f - nN f)), by omega⟩) = i :=
      Fin.ext (by simp [Fin.val_rev]; omega)
    rw [hci]
    push_cast
    have := natFloor_of_int (-f i) (-⌊f i⌋) (by push_cast; rw [hint i]) (by linarith)
    rw [this]; ring

theorem pos_of_αP (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hp : ∀ i i' : Fin n, i < i' → 0 < f i' → 0 < f i) (i : Fin (nP f)) : 0 < αP f i := by
  have hpos : 0 < f (Fin.castLE (nP_le_nW f) i) := (pos_iff f hp _).2 (by simp)
  have := natFloor_of_int _ _ (hint (Fin.castLE (nP_le_nW f) i)) hpos.le
  unfold αP
  have h2 : (0 : ℚ) < ((⌊f (Fin.castLE (nP_le_nW f) i)⌋₊ : ℕ) : ℚ) := by rw [this]; exact hpos
  exact_mod_cast h2

theorem pos_of_αN (f : Fin n → ℚ) (hint : ∀ i, ((⌊f i⌋ : ℤ) : ℚ) = f i)
    (hn : ∀ i i' : Fin n, i < i' → f i < 0 → f i' < 0) (i : Fin (nN f)) : 0 < αN f i := by
  have hneg : f (Fin.rev (Fin.castLE (nN_le f) i)) < 0 :=
    (neg_iff f hn _).2 (by simp [Fin.val_rev]; omega)
  have := natFloor_of_int (-f (Fin.rev (Fin.castLE (nN_le f) i))) (-⌊f (Fin.rev (Fin.castLE (nN_le f) i))⌋)
    (by push_cast; rw [hint]) (by linarith)
  unfold αN
  have h2 : (0 : ℚ) < ((⌊-f (Fin.rev (Fin.castLE (nN_le f) i))⌋₊ : ℕ) : ℚ) := by rw [this]; linarith
  exact_mod_cast h2

theorem lpos_eq_of_sq {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lpos α = lpos β := by
  obtain ⟨hmk, _, hd⟩ := h
  apply List.ext_getElem (by simp [lpos, hmk])
  intro t h1 h2
  simp only [lpos, List.getElem_ofFn]
  rw [hd ⟨t, by simpa [lpos] using h1⟩ ⟨t, by simpa [lpos] using h2⟩ rfl]

theorem lneg_eq_of_sq {m k : ℕ} {α : Fin m → ℕ} {β : Fin k → ℕ} (h : SqFacts α β) : lneg α = lneg β := by
  obtain ⟨hmk, _, hd⟩ := h
  unfold lneg
  congr 1
  apply List.ext_getElem (by simp [hmk])
  intro t h1 h2
  simp only [List.getElem_ofFn]
  rw [hd ⟨t, by simpa using h1⟩ ⟨t, by simpa using h2⟩ rfl]

theorem pairwise_lpos {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lpos α).Pairwise (· ≥ ·) := by
  unfold lpos
  rw [List.pairwise_ofFn]
  intro i j hij
  exact_mod_cast h hij.le

theorem pairwise_lneg {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lneg α).Pairwise (· ≥ ·) := by
  unfold lneg
  rw [List.pairwise_reverse, List.pairwise_ofFn]
  intro i j hij
  have : α j ≤ α i := h hij.le
  simp only [ge_iff_le, neg_le_neg_iff]
  exact_mod_cast this

end Gen

end PI.WFJM.Shape

namespace PI.FJM

open PI.WFJM.Shape

theorem shape_from_facts : ShapeFromFacts := by
  intro p q r s μ μ' hB hS hI
  obtain ⟨hA, hBb, hC, hD⟩ := hB
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hS
  obtain ⟨hI1, hI2⟩ := hI
  have iL1 : ∀ i, ((⌊leftWeightFirst p q r s μ i⌋ : ℤ) : ℚ) = leftWeightFirst p q r s μ i := fun i => hI1 (.inl i)
  have firstRealIndex : ∀ j, ((⌊leftWeightSecond p q r s μ j⌋ : ℤ) : ℚ) = leftWeightSecond p q r s μ j := fun j => hI1 (.inr j)
  have iL2 : ∀ k, ((⌊rightWeightFirst p q r s μ' k⌋ : ℤ) : ℚ) = rightWeightFirst p q r s μ' k := fun k => hI2 (.inl k)
  have secondRealIndex : ∀ l, ((⌊rightWeightSecond p q r s μ' l⌋ : ℤ) : ℚ) = rightWeightSecond p q r s μ' l := fun l => hI2 (.inr l)
  have eA : lpos (αA p q r s μ) = lpos (αP (rightWeightFirst p q r s μ')) := lpos_eq_of_sq hA
  have eB : lneg (αB p q r s μ) = lneg (αN (rightWeightSecond p q r s μ')) := lneg_eq_of_sq hBb
  have eC : lpos (αC p q r s μ) = lpos (αP (rightWeightSecond p q r s μ')) := lpos_eq_of_sq hC
  have eD : lneg (αD p q r s μ) = lneg (αN (rightWeightFirst p q r s μ')) := lneg_eq_of_sq hD
  have nA : nP (leftWeightFirst p q r s μ) = nP (rightWeightFirst p q r s μ') := hA.1
  have nB : nN (leftWeightFirst p q r s μ) = nN (rightWeightSecond p q r s μ') := hBb.1
  have nC : nP (leftWeightSecond p q r s μ) = nP (rightWeightSecond p q r s μ') := hC.1
  have nD : nN (leftWeightSecond p q r s μ) = nN (rightWeightFirst p q r s μ') := hD.1
  refine ⟨lpos (αA p q r s μ), lneg (αB p q r s μ), lpos (αC p q r s μ), lneg (αD p q r s μ),
    ?_, ?_, ?_, ?_, pairwise_lpos hA.2.1, pairwise_lneg hBb.2.1, pairwise_lpos hC.2.1, pairwise_lneg hD.2.1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [lpos, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact_mod_cast pos_of_αP (leftWeightFirst p q r s μ) iL1 s1 i
  · intro v hv
    simp only [lpos, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact_mod_cast pos_of_αP (leftWeightSecond p q r s μ) firstRealIndex s3 i
  · intro v hv
    simp only [lneg, List.mem_reverse, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := pos_of_αN (leftWeightFirst p q r s μ) iL1 s2 i
    simp only [Left.neg_neg_iff, Nat.cast_pos]
    exact this
  · intro v hv
    simp only [lneg, List.mem_reverse, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := pos_of_αN (leftWeightSecond p q r s μ) firstRealIndex s4 i
    simp only [Left.neg_neg_iff, Nat.cast_pos]
    exact this
  · rw [length_lpos, length_lneg]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg, nA, nD]; exact nP_add_nN_le _
  · rw [length_lpos, length_lneg, nC, nB]; exact nP_add_nN_le _
  · funext x
    rcases x with i | j
    · exact eq_pad (leftWeightFirst p q r s μ) iL1 s1 s2 i
    · exact eq_pad (leftWeightSecond p q r s μ) firstRealIndex s3 s4 j
  · rw [eA, eB, eC, eD]
    funext x
    rcases x with k | l
    · exact eq_pad (rightWeightFirst p q r s μ') iL2 s5 s6 k
    · exact eq_pad (rightWeightSecond p q r s μ') secondRealIndex s7 s8 l

end PI.FJM
end
end

section
noncomputable section

open Matrix FockH1Action

namespace PI.FJMD

open PI.FJM

theorem det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun τ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

theorem shapeProd_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {m k : ℕ} (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ (i : Fin m) (j : Fin k), i.val < α.length → j.val < α.length → M i j ∈ S) :
    shapeProd M α ∈ S := by
  unfold PI.FJM.shapeProd
  refine prod_mem fun t ht => pow_mem ?_ _
  have ht' : t < α.length := Finset.mem_range.mp ht
  unfold PI.FJM.leadT
  split_ifs with hc
  · apply det_mem_subalgebra S
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Matrix.submatrix_apply]
    exact h _ _ (show i.val < α.length by omega) (show j.val < α.length by omega)
  · exact zero_mem _

theorem det_vars_ne_zero {σ : Type*} {n : ℕ} (f : Fin n × Fin n → σ) (hf : Function.Injective f) :
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)).det ≠ 0 := by
  classical
  intro h0
  have hg : ∀ i j, (if ∃ i', f (i', i') = f (i, j) then (1 : ℂ) else 0) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos ⟨i, rfl⟩, if_pos rfl]
    · rw [if_neg hij, if_neg]
      rintro ⟨i', hi'⟩
      have hpair := hf hi'
      simp only [Prod.mk.injEq] at hpair
      exact hij (hpair.1.symm.trans hpair.2)
  have hmap : (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0)).mapMatrix
      (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply]
    exact hg i j
  have hdet := RingHom.map_det (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0))
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ))
  rw [h0, map_zero, hmap, Matrix.det_one] at hdet
  exact zero_ne_one hdet

theorem shapeProd_varMat_ne_zero {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (hρ : Function.Injective ρ) (hκ : Function.Injective κ) (α : List ℕ)
    (hm : α.length ≤ m) (hk : α.length ≤ k) : shapeProd (varMat (r := r) (s := s) ρ κ) α ≠ 0 := by
  unfold PI.FJM.shapeProd
  rw [Finset.prod_ne_zero_iff]
  intro t ht
  have ht' : t < α.length := Finset.mem_range.mp ht
  apply pow_ne_zero
  have hc : t + 1 ≤ m ∧ t + 1 ≤ k := ⟨by omega, by omega⟩
  unfold PI.FJM.leadT
  rw [dif_pos hc]
  have hinj : Function.Injective
      (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hxy
    simp only [Prod.mk.injEq] at hxy ⊢
    exact ⟨Fin.castLE_injective _ (hρ hxy.1), Fin.castLE_injective _ (hκ hxy.2)⟩
  exact det_vars_ne_zero
    (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) hinj

private theorem pderiv_pderiv_comm_of_complex {σ : Type*} (i j : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.pderiv_C, map_zero]
  next P Q hP hQ =>
    simp only [map_add, hP, hQ]
  next P n hP =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;>
      simp only [Derivation.map_one_eq_zero, map_zero, mul_zero, zero_mul, add_zero, zero_add,
        mul_one, one_mul, hP] <;> ring

private theorem pderiv_eq_zero_of_mem_supported_of_not_mem {σ : Type*} {S : Set σ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ MvPolynomial.supported ℂ S) {i : σ} (hi : i ∉ S) : MvPolynomial.pderiv i P = 0 := by
  have hv : i ∉ P.vars := fun hmem => hi ((MvPolynomial.mem_supported.mp hP) (Finset.mem_coe.mpr hmem))
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hv
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars hv

theorem dd_eq_zero {p q r s : ℕ} {S : Set (Ln p q r s)} {P : Pol p q r s}
    (hP : P ∈ MvPolynomial.supported ℂ S) {l l' : Ln p q r s} (h : l ∉ S ∨ l' ∉ S) : dd l l' P = 0 := by
  have key : PI.FJM.dd l l' P = MvPolynomial.pderiv l (MvPolynomial.pderiv l' P) := by
    first
    | rfl
    | simp [PI.FJM.dd]
  rw [key]
  rcases h with h | h
  · rw [pderiv_pderiv_comm_of_complex, pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]
  · rw [pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]

def inS {p q r s : ℕ} (la lb lc ld : ℕ) : Ln p q r s → Prop
  | (Sum.inl i, Sum.inl k) => i.val < la ∧ k.val < la
  | (Sum.inl i, Sum.inr l) => p ≤ i.val + lb ∧ s ≤ l.val + lb
  | (Sum.inr j, Sum.inr l) => j.val < lc ∧ l.val < lc
  | (Sum.inr j, Sum.inl k) => q ≤ j.val + ld ∧ r ≤ k.val + ld

theorem posPart_length (a : List ℤ) : (PI.FJM.posPart a).length = a.length := by
  simp [PI.FJM.posPart]

theorem negPart_length (b : List ℤ) : (PI.FJM.negPart b).length = b.length := by
  simp [PI.FJM.negPart]

private theorem fin_rev_val {n : ℕ} (i : Fin n) : (Fin.rev i).val = n - (i.val + 1) := rfl

private theorem varMat_apply_mem_supported {p q r s m k : ℕ} (ρ : Fin m → FockH1Action.Ix p q)
    (κ : Fin k → FockH1Action.Ix r s) (T : Set (FockH1Action.Ln p q r s)) (i : Fin m) (j : Fin k)
    (h : (ρ i, κ j) ∈ T) : PI.FJM.varMat ρ κ i j ∈ MvPolynomial.supported ℂ T := by
  rw [show PI.FJM.varMat ρ κ i j = MvPolynomial.X (ρ i, κ j) from rfl]
  first
  | exact MvPolynomial.X_mem_supported.mpr h
  | exact MvPolynomial.mem_supported.mpr (by rw [MvPolynomial.vars_X]; simpa using h)

theorem hwVec_mem_supported (p q r s : ℕ) (a b c d : List ℤ) :
    hwVec p q r s a b c d ∈ MvPolynomial.supported ℂ
      {l : Ln p q r s | inS a.length b.length c.length d.length l} := by
  unfold PI.FJM.hwVec
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega

theorem shapeVector_ne_zero : VecNe := by
  intro p q r s a b c d h
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  unfold PI.FJM.hwVec
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inl_injective hxy) (by intro x y hxy; exact Sum.inl_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inr_injective hxy) (by intro x y hxy; exact Sum.inr_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)

private theorem moduleEnd_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (t : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ x ∈ t, f x) v = ∑ x ∈ t, f x v := by
  first
  | exact LinearMap.sum_apply t f v
  | simp

theorem vecJ_of (hF : FormJ) : VecJ := by
  intro p q r s a b c d h
  have hsupp := hwVec_mem_supported p q r s a b c d
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  refine (hF p q r s (PI.FJM.hwVec p q r s a b c d)).mpr ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    unfold PI.FJM.lapA
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun l _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro i j
    unfold PI.FJM.lapB
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun k _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapC
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapD
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega

end PI.FJMD
end
end

section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMA

open PI.FJM

section Generic

variable {σ : Type}

def FreeOf (S : Set σ) (G : MvPolynomial σ ℂ) : Prop := ∀ e ∈ G.support, ∀ v ∈ S, e v = 0

theorem vars_zero_of_supported {S : Set σ} {F : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) :
    ∀ x ∈ F.support, ∀ v ∉ S, x v = 0 := by
  intro x hx v hv
  by_contra h
  exact hv ((mem_supported.1 hF) ((mem_vars_iff_mem_support v).2 ⟨x, hx, Finsupp.mem_support_iff.2 h⟩))

theorem exists_support_mul {S : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) {e' : σ →₀ ℕ} (he' : e' ∈ G.support) :
    ∃ e ∈ (F * G).support, ∀ v ∉ S, e v = e' v := by
  classical
  obtain ⟨e0, he0⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.2 (mt support_eq_empty.1 hF0)
  have hvars := vars_zero_of_supported hF
  refine ⟨e0 + e', ?_, fun v hv => by simp [hvars e0 he0 v hv]⟩
  rw [mem_support_iff, coeff_mul, Finset.sum_eq_single (e0, e')]
  · exact mul_ne_zero (mem_support_iff.1 he0) (mem_support_iff.1 he')
  · rintro ⟨x, y⟩ hxy hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
    by_contra h
    have hx : x ∈ F.support := mem_support_iff.2 (left_ne_zero_of_mul h)
    have hy : y ∈ G.support := mem_support_iff.2 (right_ne_zero_of_mul h)
    apply hne
    have h1 : x = e0 := by
      ext v
      have := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at this
      by_cases hv : v ∈ S
      · rw [hG y hy v hv, hG e' he' v hv] at this; omega
      · rw [hvars x hx v hv, hvars e0 he0 v hv]
    subst h1
    have h2 : y = e' := by
      ext v
      have := congrArg (fun f => f v) hxy
      simp only [Finsupp.add_apply] at this
      omega
    subst h2
    rfl
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (show (e0, e').1 + (e0, e').2 = e0 + e' from rfl)) h

theorem freeOf_of_mul {S T : Set σ} {F G : MvPolynomial σ ℂ} (hF : F ∈ supported ℂ S) (hF0 : F ≠ 0)
    (hG : FreeOf S G) (hH : FreeOf T (F * G)) (hST : Disjoint S T) : FreeOf T G := by
  intro e' he' v hv
  obtain ⟨e, he, hee⟩ := exists_support_mul hF hF0 hG he'
  have hvS : v ∉ S := fun h => Set.disjoint_left.1 hST h hv
  rw [← hee v hvS]
  exact hH e he v hv

theorem bRow_mul {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bRow ι a b (F * G) = F * bRow ι a b G := by
  unfold bRow
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, hF, smul_eq_mul, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem bCol_mul {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (F G : MvPolynomial σ ℂ)
    (hF : ∀ x, pderiv (ι x) F = 0) : bCol ι c d (F * G) = F * bCol ι c d G := by
  unfold bCol
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, hF, smul_eq_mul, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem shapeProd_supported {m n : ℕ} (ι : Fin m × Fin n → σ) (α : List ℕ) :
    shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) α ∈ supported ℂ (Set.range ι) :=
  PI.FJMD.shapeProd_mem _ _ _ (fun i k _ _ => by
    simp only [Matrix.of_apply]
    exact X_mem_supported.2 ⟨(i, k), rfl⟩)

theorem peel (hC : CauchyHW) {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (S : Set σ) (F G : MvPolynomial σ ℂ) (hF : F ∈ supported ℂ S)
    (hF0 : F ≠ 0) (hG : FreeOf S G) (hS : ∀ x, ι x ∉ S) (hG0 : G ≠ 0) (hP : IsBlockHighestWeight ι α β (F * G)) :
    SqFacts α β ∧ ∃ Q, FreeOf (Set.range ι) Q ∧
      G = shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have hFd : ∀ x, pderiv (ι x) F = 0 := fun x => PI.FJMX.pderiv_eq_zero_of_supported hF (hS x)
  have g1 : ∀ a b : Fin m, a < b → bRow ι a b G = 0 := by
    intro a b hab
    have := h1 a b hab
    rw [bRow_mul ι a b F G hFd] at this
    exact (mul_eq_zero.1 this).resolve_left hF0
  have g2 : ∀ c d : Fin n, c < d → bCol ι c d G = 0 := by
    intro c d hcd
    have := h2 c d hcd
    rw [bCol_mul ι c d F G hFd] at this
    exact (mul_eq_zero.1 this).resolve_left hF0
  have g3 : ∀ e ∈ G.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k) := by
    intro e' he'
    obtain ⟨e, he, hee⟩ := exists_support_mul hF hF0 hG he'
    obtain ⟨k1, k2⟩ := h3 e he
    refine ⟨fun i => ?_, fun k => ?_⟩
    · rw [← k1 i]; exact Finset.sum_congr rfl (fun k _ => (hee _ (hS _)).symm)
    · rw [← k2 k]; exact Finset.sum_congr rfl (fun i _ => (hee _ (hS _)).symm)
  obtain ⟨r1, r2, r3, Q, hQ, hGQ⟩ := hC σ m n ι hι α β G hG0 g1 g2 g3 h4 h5
  refine ⟨⟨r1, r2, r3⟩, Q, ?_, hGQ⟩
  intro e he v hv
  obtain ⟨x, rfl⟩ := hv
  exact hQ e he x

end Generic

section Blocks

variable {σ : Type}

abbrev blkP {m n : ℕ} (ι : Fin m × Fin n → σ) (α : Fin m → ℕ) : MvPolynomial σ ℂ :=
  shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α)

theorem freeOf_union {S T : Set σ} {G : MvPolynomial σ ℂ} (h1 : FreeOf S G) (h2 : FreeOf T G) :
    FreeOf (S ∪ T) G := by
  intro e he v hv
  rcases hv with hv | hv
  · exact h1 e he v hv
  · exact h2 e he v hv

theorem eq_C_of_support {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, e = 0) : Q = C (coeff 0 Q) := by
  classical
  ext m
  rw [coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm)]
    by_contra hc
    exact hm (h m (mem_support_iff.2 hc))

end Blocks

section Line

variable (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)

theorem injA : Function.Injective (ιA p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιA, Prod.mk.injEq, Sum.inl.injEq] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem injB : Function.Injective (ιB p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιB, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.rev_inj] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem injC : Function.Injective (ιC p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιC, Prod.mk.injEq, Sum.inr.injEq] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem injD : Function.Injective (ιD p q r s μ μ') := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ h
  simp only [ιD, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.rev_inj] at h
  exact Prod.ext (Fin.castLE_injective _ h.1) (Fin.castLE_injective _ h.2)

theorem dBA : ∀ x, ιB p q r s μ μ' x ∉ Set.range (ιA p q r s μ μ') := by
  rintro x ⟨y, hy⟩
  simp [ιA, ιB] at hy

theorem dCAB : ∀ x, ιC p q r s μ μ' x ∉ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') := by
  rintro x (⟨y, hy⟩ | ⟨y, hy⟩) <;> simp [ιA, ιB, ιC] at hy

theorem dDABC : ∀ x, ιD p q r s μ μ' x ∉
    Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') := by
  rintro x ((⟨y, hy⟩ | ⟨y, hy⟩) | ⟨y, hy⟩) <;> simp [ιA, ιB, ιC, ιD] at hy

theorem disj_of {S : Set (Ln p q r s)} {m n : ℕ} (ι : Fin m × Fin n → Ln p q r s) (h : ∀ x, ι x ∉ S) :
    Disjoint (Set.range ι) S := by
  refine Set.disjoint_left.2 ?_
  rintro v ⟨x, rfl⟩ hv
  exact h x hv

end Line

theorem line_of (hC : CauchyHW) (hA : HypA) (hB : HypB) (hCc : HypC) (hD : HypD) (hCov : CoverJ)
    (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s) (hP : MinHyp p q r s μ μ' P) :
    BlockFacts p q r s μ μ' ∧ ∃ c : ℂ, P = C c * vLine p q r s μ μ' := by
  have hP0 : P ≠ 0 := hP.2.1

  obtain ⟨sqA, QA, fA, eA⟩ := peel hC (ιA p q r s μ μ') (injA p q r s μ μ') _ _ ∅ 1 P
    (supported ℂ (∅ : Set (Ln p q r s))).one_mem one_ne_zero (fun _ _ _ h => h.elim) (fun _ h => h) hP0
    (by rw [one_mul]; exact hA p q r s μ μ' P hP)
  have hQA0 : QA ≠ 0 := by rintro rfl; rw [mul_zero] at eA; exact hP0 eA
  have shA0 : blkP (ιA p q r s μ μ') (αA p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιA p q r s μ μ') (αA p q r s μ) * QA ≠ 0 from eA ▸ hP0)
  have suA := shapeProd_supported (ιA p q r s μ μ') (List.ofFn (αA p q r s μ))

  obtain ⟨sqB, QB, fB, eB⟩ := peel hC (ιB p q r s μ μ') (injB p q r s μ μ') _ _ (Set.range (ιA p q r s μ μ'))
    _ QA suA shA0 fA (dBA p q r s μ μ') hQA0 (by rw [← eA]; exact hB p q r s μ μ' P hP)
  have hQB0 : QB ≠ 0 := by rintro rfl; rw [mul_zero] at eB; exact hQA0 eB
  have shB0 : blkP (ιB p q r s μ μ') (αB p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιB p q r s μ μ') (αB p q r s μ) * QB ≠ 0 from eB ▸ hQA0)
  have suB := shapeProd_supported (ιB p q r s μ μ') (List.ofFn (αB p q r s μ))
  have fBA : FreeOf (Set.range (ιA p q r s μ μ')) QB :=
    freeOf_of_mul suB shB0 fB (eB ▸ fA) (disj_of p q r s (ιB p q r s μ μ') (dBA p q r s μ μ'))

  obtain ⟨sqC, QC, fC, eC⟩ := peel hC (ιC p q r s μ μ') (injC p q r s μ μ') _ _
    (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ')) _ QB
    (Subalgebra.mul_mem _ (supported_mono Set.subset_union_left suA) (supported_mono Set.subset_union_right suB))
    (mul_ne_zero shA0 shB0) (freeOf_union fBA fB) (dCAB p q r s μ μ') hQB0
    (by rw [mul_assoc, ← eB, ← eA]; exact hCc p q r s μ μ' P hP)
  have hQC0 : QC ≠ 0 := by rintro rfl; rw [mul_zero] at eC; exact hQB0 eC
  have shC0 : blkP (ιC p q r s μ μ') (αC p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιC p q r s μ μ') (αC p q r s μ) * QC ≠ 0 from eC ▸ hQB0)
  have suC := shapeProd_supported (ιC p q r s μ μ') (List.ofFn (αC p q r s μ))
  have fCAB : FreeOf (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ')) QC :=
    freeOf_of_mul suC shC0 fC (eC ▸ freeOf_union fBA fB) (disj_of p q r s (ιC p q r s μ μ') (dCAB p q r s μ μ'))

  obtain ⟨sqD, QD, fD, eD⟩ := peel hC (ιD p q r s μ μ') (injD p q r s μ μ') _ _
    (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ')) _ QC
    (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (supported_mono (Set.subset_union_left.trans Set.subset_union_left) suA)
      (supported_mono (Set.subset_union_right.trans Set.subset_union_left) suB))
      (supported_mono Set.subset_union_right suC))
    (mul_ne_zero (mul_ne_zero shA0 shB0) shC0) (freeOf_union fCAB fC) (dDABC p q r s μ μ') hQC0
    (by rw [mul_assoc, ← eC, mul_assoc, ← eB, ← eA]; exact hD p q r s μ μ' P hP)
  have shD0 : blkP (ιD p q r s μ μ') (αD p q r s μ) ≠ 0 :=
    left_ne_zero_of_mul (show blkP (ιD p q r s μ μ') (αD p q r s μ) * QD ≠ 0 from eD ▸ hQC0)
  have suD := shapeProd_supported (ιD p q r s μ μ') (List.ofFn (αD p q r s μ))
  have fDABC : FreeOf (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ')) QD :=
    freeOf_of_mul suD shD0 fD (eD ▸ freeOf_union fCAB fC) (disj_of p q r s (ιD p q r s μ μ') (dDABC p q r s μ μ'))
  have hF4 : blkP (ιA p q r s μ μ') (αA p q r s μ) * blkP (ιB p q r s μ μ') (αB p q r s μ) *
      blkP (ιC p q r s μ μ') (αC p q r s μ) * blkP (ιD p q r s μ μ') (αD p q r s μ) ∈
      supported ℂ (Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
        Set.range (ιD p q r s μ μ')) :=
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (supported_mono ((Set.subset_union_left.trans Set.subset_union_left).trans Set.subset_union_left) suA)
      (supported_mono ((Set.subset_union_right.trans Set.subset_union_left).trans Set.subset_union_left) suB))
      (supported_mono (Set.subset_union_right.trans Set.subset_union_left) suC))
      (supported_mono Set.subset_union_right suD)
  have hF40 := mul_ne_zero (mul_ne_zero (mul_ne_zero shA0 shB0) shC0) shD0
  have hPeq : P = blkP (ιA p q r s μ μ') (αA p q r s μ) * blkP (ιB p q r s μ μ') (αB p q r s μ) *
      blkP (ιC p q r s μ μ') (αC p q r s μ) * blkP (ιD p q r s μ μ') (αD p q r s μ) * QD := by
    rw [eA, eB, eC, eD]; ring
  have fD4 := freeOf_union fDABC fD
  have hsupp : ∀ e' ∈ QD.support, e' = 0 := by
    intro e' he'
    obtain ⟨e, he, hee⟩ := exists_support_mul hF4 hF40 fD4 he'
    rw [← hPeq] at he
    ext v
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hv
    have hvS : v ∉ Set.range (ιA p q r s μ μ') ∪ Set.range (ιB p q r s μ μ') ∪ Set.range (ιC p q r s μ μ') ∪
        Set.range (ιD p q r s μ μ') := fun h => hv (fD4 e' he' v h)
    exact hvS (hCov p q r s μ μ' P hP e he v (by rw [hee v hvS]; exact hv))
  refine ⟨⟨sqA, sqB, sqC, sqD⟩, coeff 0 QD, ?_⟩
  conv_lhs => rw [hPeq, eq_C_of_support hsupp]
  unfold vLine
  ring

end PI.FJMA
end
end

section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJMF

def HwHarmDeg2 : Prop := ∀ p q r s : ℕ, ∀ (μ : Ix r s → ℚ) (e : ℕ) (v : Pol p q r s),
  v ∈ homog (Ix p q × Ix r s) e → IsHW (fockAct2 p q r s) μ v →
    (∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) v = 0) →
    (e : ℚ) = degW (cPair p q) μ

section Grade

variable {σ : Type*}

theorem hc_shift (L : Module.End ℂ (MvPolynomial σ ℂ)) (k : ℕ)
    (hL : ∀ (d : ℕ) (Q : MvPolynomial σ ℂ), Q ∈ homog σ d → L Q ∈ homog σ (d + k))
    (j : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent j (L P) = if k ≤ j then L (homogeneousComponent (j - k) P) else 0 := by
  have hP := sum_homogeneousComponent P
  conv_lhs => rw [← hP]
  rw [map_sum, map_sum]
  have hterm : ∀ d, homogeneousComponent j (L (homogeneousComponent d P)) =
      if j = d + k then L (homogeneousComponent d P) else 0 := by
    intro d
    exact homogeneousComponent_of_mem (hL d _ (homogeneousComponent_mem d P))
  simp only [hterm]
  split_ifs with hkj
  · rw [Finset.sum_eq_single (j - k)]
    · rw [if_pos (by omega)]
    · intro d _ hd
      rw [if_neg (by omega)]
    · intro hm
      rw [if_pos (by omega)]
      rw [Finset.mem_range] at hm
      rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
  · exact Finset.sum_eq_zero fun d _ => if_neg (by omega)

theorem hc_X (l : σ) (j : ℕ) (Q : MvPolynomial σ ℂ) :
    homogeneousComponent j (X l * Q) = if 1 ≤ j then X l * homogeneousComponent (j - 1) Q else 0 := by
  have h := hc_shift (LinearMap.mulLeft ℂ (X l : MvPolynomial σ ℂ)) 1 (fun d Q' hQ' => by
    have h1 := (isHomogeneous_X ℂ l).mul hQ'
    rw [add_comm] at h1
    exact h1) j Q
  simpa using h

theorem supp_hc {e : ℕ} {P : MvPolynomial σ ℂ} {m : σ →₀ ℕ}
    (h : m ∈ (homogeneousComponent e P).support) : m ∈ P.support := by
  rw [mem_support_iff, coeff_homogeneousComponent] at h
  rw [mem_support_iff]
  split_ifs at h
  · exact h
  · exact absurd rfl h

theorem low_hc (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) (h : L P = 0) (n : ℕ) : L (homogeneousComponent n P) = 0 := by
  have hz : ∀ e, homogeneousComponent e (L (homogeneousComponent n P)) = 0 := by
    intro e
    rw [hL e, homogeneousComponent_of_mem (homogeneousComponent_mem n P)]
    split_ifs with he
    · have h2 := hL e P
      rw [h, map_zero, he] at h2
      exact h2.symm
    · simp
  ext m
  have h3 := congrArg (coeff m) (hz (m.degree))
  rw [coeff_homogeneousComponent, if_pos rfl] at h3
  simpa using h3

theorem low_sum {ι : Type*} (t : Finset ι) (L : ι → Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ i (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L i P) = L i (homogeneousComponent (e + 2) P)) :
    ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e ((∑ i ∈ t, L i) P) = (∑ i ∈ t, L i) (homogeneousComponent (e + 2) P) := by
  intro e P
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hL i e P

theorem exists_homog_of (P : MvPolynomial σ ℂ) (h0 : P ≠ 0) (D : ℚ)
    (h : ∀ e : ℕ, homogeneousComponent e P ≠ 0 → (e : ℚ) = D) :
    ∃ d : ℕ, (d : ℚ) = D ∧ P ∈ homog σ d := by
  have hex : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h0
    rw [← sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun i _ => hall i
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, h d hd, ?_⟩
  have hP : P = homogeneousComponent d P := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    rw [Finset.sum_eq_single d]
    · intro i _ hi
      by_contra hne
      exact hi (by exact_mod_cast (h i hne).trans (h d hd).symm)
    · intro hdm
      exfalso
      apply hd
      apply homogeneousComponent_eq_zero
      rw [Finset.mem_range] at hdm
      omega
  rw [hP]
  exact homogeneousComponent_mem d P

end Grade

section Ops

variable {p q r s : ℕ}

theorem hc_raiLow (l l' : Ln p q r s) (h : linePos l = linePos l') (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e ((raiB l * lowB l') Q) = (raiB l * lowB l') (homogeneousComponent e Q) := by
  rw [Module.End.mul_apply, Module.End.mul_apply]
  cases hl : linePos l with
  | true =>
    have hl' : linePos l' = true := by rw [← h, hl]
    simp only [raiB, lowB, hl, hl', if_true, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [hc_X]
    cases e with
    | zero => simp
    | succ k => simp [PI.WFJM.hc_pderiv]
  | false =>
    have hl' : linePos l' = false := by rw [← h, hl]
    simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, LinearMap.neg_apply]
    rw [map_neg, PI.WFJM.hc_pderiv, hc_X, if_pos (by omega)]
    simp

theorem sameBlock_linePos_first {a b : Ix p q} (hab : sameBlock a b) (c : Ix r s) :
    linePos ((a, c) : Ln p q r s) = linePos ((b, c) : Ln p q r s) := by
  cases a <;> cases b <;> cases c <;> simp [sameBlock, linePos] at hab ⊢

theorem sameBlock_linePos_second {c d : Ix r s} (hcd : sameBlock c d) (a : Ix p q) :
    linePos ((a, c) : Ln p q r s) = linePos ((a, d) : Ln p q r s) := by
  cases c <;> cases d <;> cases a <;> simp [sameBlock, linePos] at hcd ⊢

theorem posC_sb {n m : ℕ} {a b : Ix n m} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> simp [posC, sameBlock] at h ⊢

theorem homogeneous_component_raise_first {a b : Ix p q} (hab : sameBlock a b) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai1 (r := r) (s := s) a b Q) =
      PI.FJM.rai1 (r := r) (s := s) a b (homogeneousComponent e Q) := by
  simp only [PI.FJM.rai1, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => hc_raiLow _ _ (sameBlock_linePos_first hab c) e Q

theorem homogeneous_component_raise_second {c d : Ix r s} (hcd : sameBlock c d) (e : ℕ) (Q : Pol p q r s) :
    homogeneousComponent e (PI.FJM.rai2 (p := p) (q := q) c d Q) =
      PI.FJM.rai2 (p := p) (q := q) c d (homogeneousComponent e Q) := by
  simp only [PI.FJM.rai2, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => hc_raiLow _ _ (sameBlock_linePos_second hcd a) e Q

theorem hc_mem_hwSub1 (μ : Ix p q → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct1 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct1 p q r s) μ := by
  rw [PI.WFJM.mem_hwSub1] at hP ⊢
  refine ⟨fun m hm a => hP.1 m (supp_hc hm) a, fun a b hab => ?_⟩
  rw [← homogeneous_component_raise_first (posC_sb hab), hP.2 a b hab, map_zero]

theorem hc_mem_hwSub2 (μ : Ix r s → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct2 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct2 p q r s) μ := by
  rw [PI.WFJM.mem_hwSub2] at hP ⊢
  refine ⟨fun m hm c => hP.1 m (supp_hc hm) c, fun c d hcd => ?_⟩
  rw [← homogeneous_component_raise_second (posC_sb hcd), hP.2 c d hcd, map_zero]

theorem span_jset (P : Pol p q r s) (hP : P ∈ Submodule.span ℂ (Jset p q r s)) : P ∈ Jset p q r s := by
  have key := PI.FJM.jointHarmonicsIffLaplacians p q r s
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact (key 0).2 ⟨fun i j => map_zero _, fun i j => map_zero _, fun k l => map_zero _,
      fun k l => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, a4⟩ := (key x).1 hx
    obtain ⟨b1, b2, b3, b4⟩ := (key y).1 hy
    exact (key (x + y)).2 ⟨fun i j => by rw [map_add, a1, b1, add_zero],
      fun i j => by rw [map_add, a2, b2, add_zero], fun k l => by rw [map_add, a3, b3, add_zero],
      fun k l => by rw [map_add, a4, b4, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, a4⟩ := (key x).1 hx
    exact (key (c • x)).2 ⟨fun i j => by rw [map_smul, a1, smul_zero],
      fun i j => by rw [map_smul, a2, smul_zero], fun k l => by rw [map_smul, a3, smul_zero],
      fun k l => by rw [map_smul, a4, smul_zero]⟩

theorem jset_hc (P : Pol p q r s) (hP : P ∈ Jset p q r s) (e : ℕ) :
    homogeneousComponent e P ∈ Jset p q r s := by
  have key := PI.FJM.jointHarmonicsIffLaplacians p q r s
  obtain ⟨a1, a2, a3, a4⟩ := (key P).1 hP
  refine (key _).2 ⟨fun i j => ?_, fun i j => ?_, fun k l => ?_, fun k l => ?_⟩
  · exact low_hc _ (by unfold PI.FJM.lapA; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a1 i j) e
  · exact low_hc _ (by unfold PI.FJM.lapB; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a2 i j) e
  · exact low_hc _ (by unfold PI.FJM.lapC; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a3 k l) e
  · exact low_hc _ (by unfold PI.FJM.lapD; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a4 k l) e

end Ops

theorem minDegJ_of (hT1 : PI.FockOneDegW.HwHarmDeg) (hT2 : HwHarmDeg2) : PI.FJM.MinDegJ := by
  intro p q r s μ μ' P hP h0
  simp only [PI.FJM.JH, Submodule.mem_inf] at hP
  obtain ⟨⟨h1, h2⟩, hJ⟩ := hP
  have hJ' := span_jset P hJ
  refine ⟨exists_homog_of P h0 _ fun e he => ?_, exists_homog_of P h0 _ fun e he => ?_⟩
  · obtain ⟨j1, j2⟩ := jset_hc P hJ' e
    exact hT1 p q r s μ e _ (homogeneousComponent_mem e P) ⟨he, hc_mem_hwSub1 μ P h1 e⟩ j2
  · obtain ⟨j1, j2⟩ := jset_hc P hJ' e
    exact hT2 p q r s μ' e _ (homogeneousComponent_mem e P) ⟨he, hc_mem_hwSub2 μ' P h2 e⟩ j1

theorem minimal_degree_joint : PI.FJM.MinDegJ := minDegJ_of (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
  (fun p q r s μ e v hv hw hm => PI.FockOneDegW.Swap.hwHarmDeg2
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff) p q r s μ e v hv hw hm)

end PI.FJMF
end
end

section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

theorem minHyp_of_mem {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ JH p q r s μ μ') (h0 : P ≠ 0) : MinHyp p q r s μ μ' P := by
  obtain ⟨⟨d1, hd1, hP1⟩, ⟨d2, hd2, hP2⟩⟩ := PI.FJMF.minimal_degree_joint p q r s μ μ' P hP h0
  have h12 : d1 = d2 :=
    ((mem_homogeneousSubmodule _ _).1 hP1).inj_right ((mem_homogeneousSubmodule _ _).1 hP2) h0
  subst h12
  exact ⟨hP, h0, d1, hd1, hd2, hP1⟩

theorem shapeOf_of_cauchy (hC : CauchyHW) : ShapeOf := by
  intro p q r s μ μ' P hP h0
  have hM := minHyp_of_mem hP h0
  exact shape_from_facts p q r s μ μ'
    (PI.FJMA.line_of hC PI.FJMS.hypothesis_first_cover PI.FJMS.hypothesis_second_cover PI.FJMS.hypothesis_third_cover PI.FJMS.hypothesis_fourth_cover
      PI.FJMS.cover_by_blocks p q r s μ μ' P hM).1
    (PI.FJMS.segs_of hM) (PI.FJMS.intFacts_of hM)

theorem rankLe_of_cauchy (hC : CauchyHW) : RankLe := by
  intro p q r s μ μ' _
  refine ⟨vLine p q r s μ μ', fun P hP => ?_⟩
  by_cases h0 : P = 0
  · rw [h0]; exact Submodule.zero_mem _
  · obtain ⟨c, hc⟩ := (PI.FJMA.line_of hC PI.FJMS.hypothesis_first_cover PI.FJMS.hypothesis_second_cover PI.FJMS.hypothesis_third_cover
      PI.FJMS.hypothesis_fourth_cover PI.FJMS.cover_by_blocks p q r s μ μ' P (minHyp_of_mem hP h0)).2
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, C_mul']⟩

theorem fockJointMult_of_cauchy (hC : CauchyHW) : PI.FockDegreeTwoParts.JointMult := jointMult_of
    (exist_of PI.FJMD.shapeVector_ne_zero (PI.FJMD.vecJ_of jointHarmonicsIffLaplacians) (PI.FJMX.vecHW1_of leftDiagonalActionFormula leftOffDiagonalActionFormula)
      (PI.FJMX.vecHW2_of rightDiagonalActionFormula rightOffDiagonalActionFormula))
    (shapeOf_of_cauchy hC) (rankLe_of_cauchy hC)

end PI.FJM
end
end
