import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Comb

open MvPolynomial Finset Equiv

noncomputable section

open scoped Classical

variable {m : ℕ}

def pcnt {n : ℕ} (w : Fin n → Fin m) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.filter (fun s : Fin n => (s : ℕ) < t ∧ w s = i)).card

def IsLattice {n : ℕ} (w : Fin n → Fin m) : Prop :=
  ∀ t ≤ n, ∀ i j : Fin m, i ≤ j → pcnt w t j ≤ pcnt w t i

def latticeWords (n : ℕ) (lam : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  univ.filter (fun w => IsLattice w ∧ ∀ i, pcnt w n i = lam i)

theorem pcnt_castSucc_snoc {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (t : ℕ) (ht : t ≤ n) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) t i = pcnt w t i := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  rw [if_neg (by omega), add_zero]

theorem pcnt_snoc_last {n : ℕ} (w : Fin n → Fin m) (a : Fin m) (i : Fin m) :
    pcnt (Fin.snoc w a : Fin (n + 1) → Fin m) (n + 1) i = pcnt w n i + if a = i then 1 else 0 := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have := s.isLt
    by_cases h : w s = i <;> simp [h, this, Nat.lt_succ_of_lt this]
  · simp

theorem pcnt_zero {n : ℕ} (w : Fin n → Fin m) (i : Fin m) : pcnt w 0 i = 0 := by
  unfold pcnt; simp

theorem pcnt_le_of_le {n : ℕ} (w : Fin n → Fin m) {t t' : ℕ} (h : t ≤ t') (i : Fin m) :
    pcnt w t i ≤ pcnt w t' i := by
  unfold pcnt
  exact Finset.card_le_card (fun s => by simp only [mem_filter, mem_univ, true_and]; omega)

theorem sum_pcnt {n : ℕ} (w : Fin n → Fin m) : ∑ i, pcnt w n i = n := by
  unfold pcnt
  rw [← Finset.card_biUnion]
  · have : (univ : Finset (Fin m)).biUnion (fun i => univ.filter (fun s : Fin n => (s : ℕ) < n ∧ w s = i))
        = univ := by
      ext s; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    rintro s _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hij (h1 ▸ h2)

theorem update_pred_sub (lam : Fin m → ℕ) (a i : Fin m) (h : 1 ≤ lam a) :
    Function.update lam a (lam a - 1) i + (if a = i then 1 else 0) = lam i := by
  by_cases hai : a = i
  · subst hai; simp; omega
  · simp [Function.update_of_ne (Ne.symm hai), hai]

theorem card_latticeWords_succ (n : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (latticeWords (n + 1) lam).card =
      ∑ a : Fin m, if 1 ≤ lam a then (latticeWords n (Function.update lam a (lam a - 1))).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w (Fin.last n)) (t := univ)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · refine Finset.card_nbij' (fun w => Fin.init w) (fun w => Fin.snoc w a) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨⟨hlat, hcont⟩, hlast⟩ := hw
      have hw' : w = Fin.snoc (Fin.init w) a := by
        rw [← hlast]; exact (Fin.snoc_init_self w).symm
      refine ⟨fun t ht i j hij => ?_, fun i => ?_⟩
      · have := hlat t (by omega) i j hij
        rwa [hw', pcnt_castSucc_snoc _ _ _ ht, pcnt_castSucc_snoc _ _ _ ht] at this
      · have := hcont i
        rw [hw', pcnt_snoc_last] at this
        have h2 := update_pred_sub lam a i ha
        omega
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq, latticeWords, mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨hlat, hcont⟩ := hw
      refine ⟨⟨fun t ht i j hij => ?_, fun i => ?_⟩, by simp⟩
      · rcases Nat.lt_or_ge t (n + 1) with htn | htn
        · rw [pcnt_castSucc_snoc _ _ _ (by omega), pcnt_castSucc_snoc _ _ _ (by omega)]
          exact hlat t (by omega) i j hij
        · have ht' : t = n + 1 := by omega
          subst ht'
          rw [pcnt_snoc_last, pcnt_snoc_last, hcont, hcont, update_pred_sub lam a i ha,
            update_pred_sub lam a j ha]
          exact hlam hij
      · rw [pcnt_snoc_last, hcont, update_pred_sub lam a i ha]
    · intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      rw [← hw.2]; exact Fin.snoc_init_self w
    · intro w hw
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw hlast
    simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
    have := hw.2 a
    have h1 : 1 ≤ pcnt w (n + 1) a := by
      unfold pcnt
      exact Finset.card_pos.mpr ⟨Fin.last n, by simp [hlast]⟩
    omega

theorem latticeWords_eq_empty_of_sum_ne (n : ℕ) (lam : Fin m → ℕ) (h : ∑ i, lam i ≠ n) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  rw [← sum_pcnt w]
  exact Finset.sum_congr rfl fun i _ => (hw.2 i).symm

theorem latticeWords_eq_empty_of_not_antitone (n : ℕ) (lam : Fin m → ℕ) (h : ¬ Antitone lam) :
    latticeWords n lam = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [latticeWords, mem_filter, mem_univ, true_and] at hw
  apply h
  intro i j hij
  rw [← hw.2 i, ← hw.2 j]
  exact hw.1 n le_rfl i j hij

end

end GroundTheory.Heights₂.Heights.RestTerms.Comb
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv

noncomputable section

namespace Comb

def alternantPsum (m : ℕ) (ρ : List ℕ) : MvPolynomial (Fin m) ℚ :=
  vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
    (ρ.map fun q => psum (Fin m) ℚ q).prod

def IsStandard {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) : Prop :=
  ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q

def rowWord {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) :
    Fin (youngCells lam).card → Fin m :=
  fun t => (T.symm t).1.1

def cellOfWord {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) : Fin m × ℕ :=
  (w t, pcnt w t (w t))

end Comb

open Comb

def CombCardYoungCells.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), (youngCells lam).card = ∑ i, lam i

def CombYoungRowCard.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (i : Fin m),
    (univ.filter fun p : youngCells lam => p.1.1 = i).card = lam i

def CombTableauRowCount.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card) (t : ℕ)
    (i : Fin m),
    pcnt (rowWord T) t i = (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card

def CombTableauRowPrefix.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ t : Fin (youngCells lam).card,
      (univ.filter fun p : youngCells lam =>
        p.1.1 = (T.symm t).1.1 ∧ (T p : ℕ) < (t : ℕ)).card = (T.symm t).1.2

def CombTableauRowLattice.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ (t : ℕ) (i j : Fin m), i ≤ j →
      (univ.filter fun p : youngCells lam => p.1.1 = j ∧ (T p : ℕ) < t).card ≤
        (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card

def CombWordOfTableau.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
      rowWord T ∈ latticeWords (youngCells lam).card lam ∧
        ∀ t, cellOfWord (rowWord T) t = (T.symm t).1

def CombCellOfWordMem.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (w : Fin (youngCells lam).card → Fin m),
    w ∈ latticeWords (youngCells lam).card lam → ∀ t, cellOfWord w t ∈ youngCells lam

def CombCellOfWordInj.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), Function.Injective (cellOfWord w)

def CombCellOfWordMono.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), IsLattice w → ∀ s t : Fin n,
    (cellOfWord w s).1 ≤ (cellOfWord w t).1 → (cellOfWord w s).2 ≤ (cellOfWord w t).2 → s ≤ t

def CombTableauOfWord.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ w ∈ latticeWords (youngCells lam).card lam,
      ∃ T : youngCells lam ≃ Fin (youngCells lam).card, IsStandard T ∧ rowWord T = w

def CombTableEqWords.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    numStandardTable lam = (latticeWords (∑ i, lam i) lam).card

def CombCfUpdateZero.Statement : Prop :=
  ∀ (m : ℕ) (A : MvPolynomial (Fin m) ℚ), IsAlt A →
    ∀ (lam : Fin m → ℕ), Antitone lam → ∀ i : Fin m, 1 ≤ lam i + stair m i →
      (lam i = 0 ∨ ¬ Antitone (Function.update lam i (lam i - 1))) →
        cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1)) A = 0

def CombCfAtStair.Statement : Prop :=
  ∀ (m n : ℕ) (lam : Fin m → ℕ), Antitone lam →
    cf (fun i => lam i + stair m i) (alternantPsum m (List.replicate n 1)) =
      (latticeWords n lam).card

def CombCfMonomialPsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (v l : Fin m → ℕ),
    cf l (monomial (ex v) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
      if (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + n then
        (n.factorial : ℚ) / ∏ i, ((l i - v i).factorial : ℚ)
      else 0

def CombDetDescFactorial.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ),
    (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)).det =
      vandermondeOf (fun i => (l i : ℚ))

def CombCfVandermondePsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (l : Fin m → ℕ), ∑ i, l i = ∑ i, stair m i + n →
    cf l (alternantPsum m (List.replicate n 1)) =
      (n.factorial : ℚ) * vandermondeOf (fun i => (l i : ℚ)) / ∏ i, ((l i).factorial : ℚ)

def CombVandermondeSucc.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) → ℚ),
    vandermondeOf v = (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ)

def CombHookShapeFacts.Statement : Prop :=
  ∀ r s l : ℕ, l < s → s ≤ r → Antitone (hookShape r s l) ∧ ∑ i, hookShape r s l i = s

def CombHookBranch.Statement : Prop :=
  ∀ r s l : ℕ, 1 ≤ s → l ≤ s → s + 1 ≤ r → ∀ a : Fin r,
    (if 1 ≤ hookShape r (s + 1) l a then
      (latticeWords s (Function.update (hookShape r (s + 1) l) a
        (hookShape r (s + 1) l a - 1))).card else 0) =
      (if (a : ℕ) = 0 ∧ l < s then (latticeWords s (hookShape r s l)).card else 0) +
        (if (a : ℕ) = l ∧ 1 ≤ l then (latticeWords s (hookShape r s (l - 1))).card else 0)

def CombHookCount.Statement : Prop :=
  ∀ r s l : ℕ, l < s → s ≤ r → (latticeWords s (hookShape r s l)).card = (s - 1).choose l

def CombSortLe.Statement : Prop :=
  ∀ (m : ℕ) (u l : Fin m → ℕ) (σ : Perm (Fin m)), Antitone l → (∀ i, u i ≤ l i) →
    Antitone (u ∘ σ) → ∀ k, u (σ k) ≤ l k

def CombSortShift.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam → ∀ (q : ℕ) (i : Fin m), q ≤ lam i + stair m i →
    Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q)) →
    ∃ (σ : Perm (Fin m)) (μ : Fin m → ℕ), Antitone μ ∧ (∀ k, μ k ≤ lam k) ∧
      ∀ k, Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) (σ k) =
        μ k + stair m k

def CombSortShiftDistinct.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ), Function.Injective l → ∀ q : ℕ, 1 ≤ q →
    ∀ i j : Fin m, i ≠ j → q ≤ l i → q ≤ l j → ∀ σ τ : Perm (Fin m),
      Function.update l i (l i - q) ∘ σ ≠ Function.update l j (l j - q) ∘ τ

def CombPcntAppend.Statement : Prop :=
  ∀ (m n q : ℕ) (w : Fin n → Fin m) (s : Fin q → Fin m) (t : ℕ) (i : Fin m),
    pcnt (Fin.append w s) t i = pcnt w t i + pcnt s (t - n) i

def CombExtendWord.Statement : Prop :=
  ∀ (m n q : ℕ) (μ lam : Fin m → ℕ), Antitone μ → Antitone lam → (∀ i, μ i ≤ lam i) →
    ∑ i, lam i = ∑ i, μ i + q →
      ∃ s : Fin q → Fin m, ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam

def CombStripSum.Statement : Prop :=
  ∀ (m n q : ℕ) (lam : Fin m → ℕ), Antitone lam → 1 ≤ q →
    ∑ i : Fin m, (if q ≤ lam i + stair m i then
      |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        (alternantPsum m (List.replicate n 1))| else 0) ≤
      ((latticeWords (n + q) lam).card : ℚ)

def CombCfBound.Statement : Prop :=
  ∀ (m : ℕ) (ρ : List ℕ), (∀ q ∈ ρ, 1 ≤ q) → ∀ lam : Fin m → ℕ, Antitone lam →
    |cf (fun i => lam i + stair m i) (alternantPsum m ρ)| ≤ ((latticeWords ρ.sum lam).card : ℚ)

end

end GroundTheory.Heights₂.Heights.RestTerms
end
