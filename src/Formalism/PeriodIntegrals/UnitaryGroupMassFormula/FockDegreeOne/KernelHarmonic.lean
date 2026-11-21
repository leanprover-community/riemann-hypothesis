import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockRaiseLow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight

section
noncomputable section

open Matrix FockH1Action MvPolynomial FockRaiseLowInner

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_apply (c d : Ix r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d P = ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
      pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P) else 0) := by
  unfold lowOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl

theorem hc_lowOp (c d : Ix r s) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (lowOp (p := p) (q := q) c d P) =
      lowOp (p := p) (q := q) c d (homogeneousComponent (e + 2) P) := by
  rw [lowOp_apply, lowOp_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [FockRL.hc_pderiv, FockRL.hc_pderiv]
  · exact map_zero _

theorem hc_comm_of_homog {σ : Type} (T : Module.End ℂ (MvPolynomial σ ℂ))
    (hT : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → T P ∈ homog σ d) (e : ℕ)
    (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (T P) = T (homogeneousComponent e P) := by
  have key : ∀ d, homogeneousComponent e (T (homogeneousComponent d P)) =
      if e = d then T (homogeneousComponent d P) else 0 := fun d =>
    homogeneousComponent_of_mem (hT d _ ((mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous d P)))
  conv_lhs => rw [← sum_homogeneousComponent P]
  rw [map_sum, map_sum]
  simp only [key]
  rw [Finset.sum_ite_eq]
  split_ifs with he
  · rfl
  · simp only [Finset.mem_range, not_lt] at he
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem inner_posOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (posOp a b Q) = fockInner (posOp b a P) Q := by
  rw [posOp_apply, posOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_mul_X, fockInner_X_mul]
  · rw [fockInner_zero_right, fockInner_zero_left]

theorem inner_negOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (negOp a b Q) = fockInner (negOp b a P) Q := by
  rw [negOp_apply, negOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_zero_right, fockInner_zero_left]
  · rw [fockInner_mul_X, fockInner_X_mul]

theorem dd_X_mul (m m' l : Ln p q r s) (Q : Pol p q r s) :
    pderiv m (pderiv m' (X l * Q)) = X l * pderiv m (pderiv m' Q) +
      (if m' = l then pderiv m Q else 0) + (if m = l then pderiv m' Q else 0) := by
  classical
  by_cases h1 : m' = l <;> by_cases h2 : m = l <;>
    simp [h1, h2, Derivation.leibniz, pderiv_X, Pi.single_apply, eq_comm] <;> ring

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem harmonic_submodule : HarmSub := by
  intro p q r s
  refine ⟨?_, ?_, ?_⟩
  · rw [harmIff]; intro c d _; exact map_zero _
  · intro P Q hP hQ
    rw [harmIff] at hP hQ ⊢
    intro c d hcd
    rw [map_add, hP c d hcd, hQ c d hcd, add_zero]
  · intro k P hP
    rw [harmIff] at hP ⊢
    intro c d hcd
    rw [map_smul, hP c d hcd, smul_zero]

theorem highest_weight_harmonic : HcHarm := by
  intro p q r s e P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  apply FockRaiseLowGrade.eq_zero_of_hc
  intro e'
  rw [hc_lowOp, FockRaiseLowGrade.hc_hc]
  split_ifs with h
  · subst h
    rw [← hc_lowOp, hP c d hcd, map_zero]
  · exact map_zero _

theorem kernel_highest_weight : KHc := by
  intro p q r s a b hab e P
  refine hc_comm_of_homog _ (fun d P hP => ?_) e P
  have hKC : IsKC (Eab a b) := by
    intro x y hxy
    simp only [Eab, Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd hab hxy
    · rfl
  exact (gradedOscillatorProperty p q r s).1 (Eab a b) hKC d P hP

theorem fock_kernel_adjoint : KAdj := by
  intro p q r s a b hab P Q
  have hba : sameBlock b a := FockRL.sameBlock_symm hab
  rw [fock_operators_kernel p q r s a b hab, fock_operators_kernel p q r s b a hba]
  simp only [sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply, fockInner_add_right,
    fockInner_add_left, fockInner_neg_right, fockInner_neg_left, inner_posOp a b hab,
    inner_negOp b a hba]
  by_cases h : a = b
  · subst h
    simp [fockInner_smul_right, fockInner_smul_left]
  · simp [h, Ne.symm h, fockInner_zero_right, fockInner_zero_left]

end PI.FockOneDegW
end
end

section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_Xd (c d : Ix r s) (l l' : Ln p q r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (X l * pderiv l' P) =
      X l * pderiv l' (lowOp (p := p) (q := q) c d P) +
      ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
        ((if ((a, d) : Ln p q r s) = l then pderiv ((a, c) : Ln p q r s) (pderiv l' P) else 0) +
         (if ((a, c) : Ln p q r s) = l then pderiv ((a, d) : Ln p q r s) (pderiv l' P) else 0))
        else 0) := by
  rw [lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : linePos ((a, d) : Ln p q r s) = true
  · simp only [h, ↓reduceIte]
    have hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) =
        pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P)) := by
      rw [PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P,
        PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]
    rw [dd_X_mul, hc]
    abel
  · simp [h]

theorem sum_rows (c d e : Ix r s) (a : Ix p q) (F G : Ix p q → Pol p q r s) :
    ∑ a' : Ix p q, (if linePos ((a', d) : Ln p q r s) = true then
      ((if ((a', d) : Ln p q r s) = (a, e) then F a' else 0) +
       (if ((a', c) : Ln p q r s) = (a, e) then G a' else 0)) else 0) =
    if linePos ((a, d) : Ln p q r s) = true then
      ((if d = e then F a else 0) + (if c = e then G a else 0)) else 0 := by
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro b _ hb
    simp [Prod.mk.injEq, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem not_both (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False :=
  hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))

theorem lowOp_posOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (posOp a b P) =
      posOp a b (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  rw [posOp_apply, posOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) P else 0) =
      (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P) else 0) +
      (if linePos ((a, e) : Ln p q r s) = true then
        (if linePos ((a, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((a, c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((a, d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0))
          else 0) else 0) := by
    intro e
    by_cases h : linePos ((a, e) : Ln p q r s) = true
    · simp only [h, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e a (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))]
    · simp [h]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single d]
  · by_cases h : linePos ((a, d) : Ln p q r s) = true
    · simp [h, hcd']
    · simp [h]
  · intro e _ hed
    by_cases h1 : linePos ((a, e) : Ln p q r s) = true
    · by_cases h2 : linePos ((a, d) : Ln p q r s) = true
      · have hce : c ≠ e := by
          rintro rfl; exact not_both c d hcd a h1 h2
        simp [h1, h2, Ne.symm hed, hce]
      · simp [h1, h2]
    · simp [h1]
  · simp

theorem lowOp_negOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (hab : sameBlock a b)
    (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (negOp b a P) =
      negOp b a (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  have hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s) :=
    (FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)
  rw [negOp_apply, negOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) =
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) +
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        (if linePos ((b, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((b, c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((b, d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0))
          else 0)) := by
    intro e
    by_cases h : linePos ((b, e) : Ln p q r s) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases h : linePos ((b, d) : Ln p q r s) = true
    · have hbc : linePos ((b, c) : Ln p q r s) = false := by
        cases h' : linePos ((b, c) : Ln p q r s)
        · rfl
        · exact (not_both c d hcd b h' h).elim
      rw [← hba]
      simp [h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]
    · rw [← hba]
      simp [h]
  · intro e _ hec
    by_cases h1 : linePos ((b, e) : Ln p q r s) = true
    · simp [h1]
    · by_cases h2 : linePos ((b, d) : Ln p q r s) = true
      · have hde : d ≠ e := by
          rintro rfl; exact h1 h2
        simp [h1, h2, hde, Ne.symm hec]
      · simp [h1, h2]
  · simp

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem kernel_harmonic : KHarm := by
  intro p q r s a b hab P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  rw [fock_operators_kernel p q r s a b hab]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, lowOp_posOp c d hcd,
    lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]
  split_ifs <;> simp [hP c d hcd]

end PI.FockOneDegW
end
end
