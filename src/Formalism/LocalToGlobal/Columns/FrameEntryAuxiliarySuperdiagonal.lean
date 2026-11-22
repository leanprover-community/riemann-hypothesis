module

public import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem finset_range_sum_split {A : Type} [AddCommMonoid A] (f : ℕ → A) (c j : ℕ) :
    ∑ i ∈ Finset.range (c + j - 1), f i =
      ∑ i ∈ Finset.range (c - 1), f i + (if 1 ≤ c ∧ 1 ≤ j then f (c - 1) else 0) + ∑ i ∈ Finset.range (j - 1), f (c + i) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  rw [if_pos ⟨hc, hj⟩, show c + j - 1 = (c - 1 + 1) + (j - 1) by omega, Finset.sum_range_add, Finset.sum_range_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  omega

section ChrLoc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem frameIndex_of_lt {k₀ c n s : ℕ} (hs : s < k₀) : LocE.fIdx k₀ c n s = s := by
  unfold LocE.fIdx
  rw [if_pos hs]

theorem frameIndex_of_ge {k₀ c n s : ℕ} (h : k₀ + c ≤ s) : LocE.fIdx k₀ c n s = s - c := by
  unfold LocE.fIdx
  rw [if_neg (show ¬ s < k₀ by omega), if_neg (show ¬ s < k₀ + c by omega)]

theorem frameEntry_eq_coord_of_extension {k₀ n c : ℕ} {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) {a b : ℕ} (ha : a < n) (hb : b < n) {p p' : ℕ}
    (hpa : LocE.fIdx k₀ c n p = a) (hpb : LocE.fIdx k₀ c n p' = b) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p' = g (Pi.single ⟨b, hb⟩ 1) ⟨a, ha⟩ := by
  unfold LocE.entB
  rw [hpa, hpb, ciScE_lt _ ha, ciScE_lt _ hb, sub_self, zpow_zero, mul_one, ciEN hb]
  show Loc.atN (rr (Loc.inX E n c (Pi.single ⟨b, hb⟩ 1))) a = _
  rw [hg, ciAtN_inX ha]

theorem reduction_frameEntry_of_extension {k₀ n c : ℕ} {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) {a b : ℕ} (ha : a < n) (hb : b < n) {p p' : ℕ}
    (hpa : LocE.fIdx k₀ c n p = a) (hpb : LocE.fIdx k₀ c n p' = b) :
    redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p') = ocbM hbar a b := by
  rw [frameEntry_eq_coord_of_extension hg ha hb hpa hpb, ← ciEntry hred]
  unfold ocbM
  rw [dite_eq_left ⟨ha, hb⟩]

theorem frameEntry_auxiliary_superdiagonal {k₀ n c i : ℕ} (hi : i + 1 < c) (rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1) =
      (q : E) * Loc.atN (rr (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have h1 : LocE.fIdx k₀ c n (k₀ + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + i < k₀ by omega), if_pos (show k₀ + i < k₀ + c by omega)]
    omega
  have h2 : LocE.fIdx k₀ c n (k₀ + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + i + 1 < k₀ by omega), if_pos (show k₀ + i + 1 < k₀ + c by omega)]
    omega
  have h3 : LocE.scE n (fun i => i + 1) (n + i + 1) = (i : ℤ) + 2 := by
    simp only [LocE.scE, if_neg (show ¬ n + i + 1 < n by omega), show n + i + 1 - n = i + 1 by omega]
    push_cast
    ring
  have h4 : LocE.scE n (fun i => i + 1) (n + i) = (i : ℤ) + 1 := by
    simp only [LocE.scE, if_neg (show ¬ n + i < n by omega), show n + i - n = i by omega]
    push_cast
    ring
  unfold LocE.entB
  rw [h1, h2, h3, h4, show (i : ℤ) + 2 - (i + 1) = 1 by ring, zpow_one, mul_comm]
  rfl

theorem frameEntry_last_auxiliary_zero {k₀ n c : ℕ} (hc : 1 ≤ c) (hkn : k₀ < n) {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c - 1)) (k₀ + (c - 1) + 1) = 0 := by
  have h1 : LocE.fIdx k₀ c n (k₀ + (c - 1)) = n + (c - 1) := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + (c - 1) < k₀ by omega), if_pos (show k₀ + (c - 1) < k₀ + c by omega)]
    omega
  have h2 : LocE.fIdx k₀ c n (k₀ + (c - 1) + 1) = k₀ := by
    rw [frameIndex_of_ge (by omega)]
    omega
  unfold LocE.entB
  rw [h1, h2, ciEN hkn]
  show Loc.atN (rr (Loc.inX E n c (Pi.single ⟨k₀, hkn⟩ 1))) (n + (c - 1)) * _ = 0
  rw [hg]
  unfold Loc.atN
  rw [dite_eq_left (show n + (c - 1) < n + c by omega), ciInX_apply]
  split_ifs with h
  · simp only at h
    omega
  · rw [zero_mul]

theorem columns_fact {k₀ n c : ℕ} (rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (q : E) * Loc.n1Arg rr = ∑ i ∈ Finset.range (c - 1), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [frameEntry_auxiliary_superdiagonal (by have := Finset.mem_range.1 hi; omega)]

theorem addChar_apply_ne_zero' {A : Type} [AddGroup A] (ψ : AddChar A K) (a : A) : ψ a ≠ 0 := fun h => by
  have h1 := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end ChrLoc

section ChrGlob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end ChrGlob

end Formalism.L2.Col
