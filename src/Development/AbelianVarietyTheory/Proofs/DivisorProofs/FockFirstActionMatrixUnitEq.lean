import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm

namespace GlobalTheory.CompactHarm

variable {m k l : ℕ}

def zVar (m k l : ℕ) : Fin k × Fin m → Ix m 0 × Ix k l := fun w => (.inl w.2, .inl w.1)

def yVar' (m k l : ℕ) : Fin l × Fin m → Ix m 0 × Ix k l := fun w => (.inl w.2, .inr w.1.rev)

theorem omE_pp {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = true) (hv : linePos v = true)
    (P : Pol p q r s) :
    omE u v P = X u * pderiv v P + (if u = v then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, hu, hv, if_true]
  split_ifs <;> simp

theorem omE_nn {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (P : Pol p q r s) :
    omE u v P = -(X v * pderiv u P) - (if u = v then (1 / 2 : ℂ) else 0) • P := by
  have : omE u v P = -(pderiv u (X v * P)) + (if u = v then (1 / 2 : ℂ) else 0) • P := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, pderiv_X_mul']
  split_ifs
  · module
  · simp

theorem fockFirstAction_matrixUnit_eq (i j : Fin m) (P : Pol m 0 k l) :
    fockAct1 m 0 k l (Eab (.inl i) (.inl j)) P = mixedOp ℂ (zVar m k l) (yVar' m k l) i j P +
      (if i = j then ((cPair k l : ℚ) : ℂ) else 0) • P := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, mixedOp_apply,
    ← Equiv.sum_comp Fin.revPerm (fun d : Fin l => omE _ _ P)]
  simp only [omE_pp (Sum.inl _, Sum.inl _) (Sum.inl _, Sum.inl _) rfl rfl,
    omE_nn (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, zVar, yVar',
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Fin.revPerm_apply,
    Prod.mk.injEq, Sum.inl.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    cPair, ← Nat.cast_smul_eq_nsmul ℂ]
  split_ifs
  · push_cast; module
  · simp [sub_eq_add_neg]



theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem mem_harm1_iff (P : Pol m 0 k l) : P ∈ harm1 m 0 k l ↔
    ∀ c d, ∑ i, pderiv (zVar m k l (c, i)) (pderiv (yVar' m k l (d, i)) P) = 0 := by
  have hf := fun Z hZ => ((GlobalTheory.FockParts.explicit_parts m 0 k l).2 Z hZ P).2
  constructor
  · intro h c d
    have hZ : IsPC (Eab (.inr d.rev) (.inl c) : Mat k l) := by
      rintro (a | a) (b | b) hab <;> simp [Eab, sameBlock] at hab ⊢
    have := h _ hZ
    rw [hf _ hZ] at this
    simp [Eab, Matrix.single_apply, ite_and, linePos, Fintype.sum_sum_type] at this
    simpa [zVar, yVar', pderiv_swap (Sum.inl _, Sum.inl _)] using this
  · intro h Z hZ
    rw [hf _ hZ]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rcases c with c | c
    · simp [linePos, Fintype.sum_sum_type]
    rcases d with d | d
    · have := h d c.rev
      simp only [zVar, yVar', Fin.rev_rev, pderiv_swap (Sum.inl _, Sum.inl _)] at this
      simp [linePos, Fintype.sum_sum_type, ← Finset.smul_sum, this]
    · simp [hZ (.inr c) (.inr d) trivial]

theorem mem_span_harm1_iff (P : Pol m 0 k l) :
    P ∈ Submodule.span ℂ (harm1 m 0 k l) ↔ P ∈ harm1 m 0 k l := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem P hP => exact hP
  | zero => simp [mem_harm1_iff]
  | add P Q _ _ hP hQ =>
    rw [mem_harm1_iff] at *
    intro c d
    simp only [map_add, Finset.sum_add_distrib, hP, hQ, add_zero]
  | smul s P _ hP =>
    rw [mem_harm1_iff] at *
    intro c d
    simp only [Derivation.map_smul, ← Finset.smul_sum, hP, smul_zero]


theorem getD_pad (x : List ℤ) (n : ℕ) (y : List ℤ) (i : ℕ) :
    (pad x n y).getD i 0 = ((x.getD i 0 +
      if x.length + n ≤ i then y.getD (i - (x.length + n)) 0 else 0 : ℤ) : ℚ) := by
  refine (List.getD_map (x ++ List.replicate n 0 ++ y) (0 : ℤ) (fun v : ℤ => (v : ℚ))).trans ?_
  congr 1
  by_cases h1 : i < x.length
  · rw [List.append_assoc, List.getD_append _ _ _ _ h1, if_neg (by omega), add_zero]
  · rw [List.getD_eq_default x _ (by omega), zero_add]
    split_ifs with h2
    · rw [List.getD_append_right _ _ _ _ (by simpa using h2)]
      simp
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp








end GlobalTheory.CompactHarm
