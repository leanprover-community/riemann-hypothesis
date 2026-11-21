import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjInvOfReal
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.SquareNormIntegralNonneg
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

section
noncomputable section

open Formalism.IndefR.Datum Matrix

namespace Formalism.IndefR.Fock.Alg

open Formalism.IndefR.Fock.Sk

section CCRAlg

variable {ι X : Type} [DecidableEq ι] {Sm : Set (X → ℂ)} {aP aM : ι → (X → ℂ) → (X → ℂ)} {v : X → ℂ}

def lpow (aP : ι → (X → ℂ) → (X → ℂ)) (l : List ι) (v : X → ℂ) : X → ℂ := l.foldr (fun i g => aP i g) v

theorem opPow_eq (k : ι →₀ ℕ) : opPow aP k v = lpow aP (Finsupp.toMultiset k).toList v := rfl

theorem lpow_nil : lpow aP [] v = v := rfl

theorem lpow_cons (j : ι) (l : List ι) : lpow aP (j :: l) v = aP j (lpow aP l v) := rfl

theorem creation_zero (h : IsCCR Sm aP aM) (i : ι) : aP i 0 = 0 := by
  have e := h.linP i 1 0 0 h.zero_mem h.zero_mem
  rw [smul_zero, add_zero, one_smul] at e
  have e2 : aP i 0 + aP i 0 = aP i 0 + 0 := by rw [add_zero]; exact e.symm
  exact add_left_cancel e2

theorem aM_zero (h : IsCCR Sm aP aM) (i : ι) : aM i 0 = 0 := by
  have e := h.linM i 1 0 0 h.zero_mem h.zero_mem
  rw [smul_zero, add_zero, one_smul] at e
  have e2 : aM i 0 + aM i 0 = aM i 0 + 0 := by rw [add_zero]; exact e.symm
  exact add_left_cancel e2

theorem creation_smul (h : IsCCR Sm aP aM) (i : ι) (c : ℂ) {f : X → ℂ} (hf : f ∈ Sm) : aP i (c • f) = c • aP i f := by
  have e := h.linP i c 0 f h.zero_mem hf
  rwa [zero_add, creation_zero h i, zero_add] at e

theorem aM_smul (h : IsCCR Sm aP aM) (i : ι) (c : ℂ) {f : X → ℂ} (hf : f ∈ Sm) : aM i (c • f) = c • aM i f := by
  have e := h.linM i c 0 f h.zero_mem hf
  rwa [zero_add, aM_zero h i, zero_add] at e

theorem aM_add (h : IsCCR Sm aP aM) (i : ι) {f g : X → ℂ} (hf : f ∈ Sm) (hg : g ∈ Sm) :
    aM i (f + g) = aM i f + aM i g := by
  have e := h.linM i 1 f g hf hg
  rwa [one_smul, one_smul] at e

theorem lpow_mem (h : IsCCR Sm aP aM) (hv : v ∈ Sm) : ∀ l : List ι, lpow aP l v ∈ Sm
  | [] => hv
  | j :: l => h.memP j _ (lpow_mem h hv l)

theorem lpow_perm (h : IsCCR Sm aP aM) (hv : v ∈ Sm) {l l' : List ι} (hp : l.Perm l') :
    lpow aP l v = lpow aP l' v := by
  induction hp with
  | nil => rfl
  | cons x _ ih => rw [lpow_cons, lpow_cons, ih]
  | swap x y l =>
    show aP y (aP x (lpow aP l v)) = aP x (aP y (lpow aP l v))
    exact h.commP y x _ (lpow_mem h hv l)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem opPow_of_list (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (k : ι →₀ ℕ) (l : List ι)
    (hl : (l : Multiset ι) = Finsupp.toMultiset k) : opPow aP k v = lpow aP l v := by
  rw [opPow_eq]
  apply lpow_perm h hv
  have e : ((Finsupp.toMultiset k).toList : Multiset ι) = (l : Multiset ι) := by
    rw [Multiset.coe_toList, hl]
  exact Multiset.coe_eq_coe.mp e

theorem opPow_mem (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (k : ι →₀ ℕ) : opPow aP k v ∈ Sm := by
  rw [opPow_eq]
  exact lpow_mem h hv _

theorem opPow_zero : opPow aP (0 : ι →₀ ℕ) v = v := by
  rw [opPow_eq]
  simp [lpow]

theorem opPow_add_single (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (k : ι →₀ ℕ) (j : ι) :
    opPow aP (k + Finsupp.single j 1) v = aP j (opPow aP k v) := by
  rw [opPow_of_list h hv (k + Finsupp.single j 1) (j :: (Finsupp.toMultiset k).toList)]
  · rfl
  · rw [← Multiset.cons_coe, Multiset.coe_toList, map_add, Finsupp.toMultiset_single, one_smul, add_comm,
      Multiset.singleton_add]

theorem aM_lpow (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (i : ι) (hi : aM i v = 0) : ∀ l : List ι,
    aM i (lpow aP l v) = ((l.count i : ℕ) : ℂ) • lpow aP (l.erase i) v
  | [] => by simp [lpow_nil, hi]
  | j :: l => by
    have ih := aM_lpow h hv i hi l
    have hc := h.ccr i j _ (lpow_mem h hv l)
    rw [sub_eq_iff_eq_add] at hc
    rw [lpow_cons, hc, ih, creation_smul h _ _ (lpow_mem h hv _)]
    by_cases hij : i = j
    · subst hij
      rw [List.count_cons_self, List.erase_cons_head, if_pos rfl]
      by_cases hm : i ∈ l
      · rw [show aP i (lpow aP (l.erase i) v) = lpow aP l v from (lpow_perm h hv (List.perm_cons_erase hm)).symm]
        push_cast
        rw [add_smul, one_smul, add_comm]
      · rw [List.count_eq_zero_of_not_mem hm]
        simp
    · rw [if_neg hij, zero_add, List.erase_cons_tail (by simpa using Ne.symm hij), lpow_cons]
      congr 2
      simp [Ne.symm hij]

theorem toMultiset_sub_single (k : ι →₀ ℕ) (i : ι) :
    Finsupp.toMultiset (k - Finsupp.single i 1) = (Finsupp.toMultiset k).erase i := by
  ext a
  rw [Finsupp.count_toMultiset, Finsupp.tsub_apply]
  by_cases ha : a = i
  · subst ha
    rw [Multiset.count_erase_self, Finsupp.count_toMultiset, Finsupp.single_eq_same]
  · rw [Multiset.count_erase_of_ne ha, Finsupp.count_toMultiset]
    simp [Finsupp.single_apply, Ne.symm ha]

theorem aM_opPow (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (i : ι) (hi : aM i v = 0) (k : ι →₀ ℕ) :
    aM i (opPow aP k v) = ((k i : ℕ) : ℂ) • opPow aP (k - Finsupp.single i 1) v := by
  rw [opPow_eq, aM_lpow h hv i hi, opPow_of_list h hv (k - Finsupp.single i 1) ((Finsupp.toMultiset k).toList.erase i)]
  · rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
  · rw [← Multiset.coe_erase, Multiset.coe_toList, toMultiset_sub_single]

theorem pt_monomial (k : ι →₀ ℕ) (c : ℂ) :
    pureTensorL aP v (MvPolynomial.monomial k c) = c • opPow aP k v := by
  rw [show MvPolynomial.monomial k c = c • MvPolynomial.monomial k (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  congr 1
  unfold pureTensorL
  have e : MvPolynomial.monomial k (1 : ℂ) = MvPolynomial.basisMonomials ι ℂ k := by
    rw [MvPolynomial.coe_basisMonomials]
  rw [e, (MvPolynomial.basisMonomials ι ℂ).constr_basis]

theorem pt_sum (P : MvPolynomial ι ℂ) :
    pureTensorL aP v P = ∑ α ∈ P.support, P.coeff α • opPow aP α v := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun α _ => pt_monomial α _)

end CCRAlg

theorem ccrMemAbs : CCRMemAbs := by
  classical
  unfold CCRMemAbs
  intro ι X _ Sm aP aM v h hv P
  rw [pt_sum]
  have key : ∀ s : Finset (ι →₀ ℕ), ∑ α ∈ s, P.coeff α • opPow aP α v ∈ Sm := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact h.zero_mem
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact h.add_mem _ _ (h.smul_mem _ _ (opPow_mem h hv a)) ih
  exact key _

theorem ccrDerivAt : CCRDerivAt := by
  classical
  unfold CCRDerivAt
  intro ι X _ Sm aP aM v h hv i hi P
  have mem : ∀ s : Finset (ι →₀ ℕ), ∑ α ∈ s, P.coeff α • opPow aP α v ∈ Sm := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact h.zero_mem
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact h.add_mem _ _ (h.smul_mem _ _ (opPow_mem h hv a)) ih
  have key : ∀ s : Finset (ι →₀ ℕ), aM i (∑ α ∈ s, P.coeff α • opPow aP α v) =
      ∑ α ∈ s, pureTensorL aP v (MvPolynomial.pderiv i (MvPolynomial.monomial α (P.coeff α))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact aM_zero h i
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, aM_add h i (h.smul_mem _ _ (opPow_mem h hv a)) (mem s), ih,
        aM_smul h i _ (opPow_mem h hv a), aM_opPow h hv i hi a, MvPolynomial.pderiv_monomial, pt_monomial,
        smul_smul]
  conv_lhs => rw [pt_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum]
  exact key _

section Norm

variable {ι X : Type} [DecidableEq ι] {Sm : Set (X → ℂ)} {aP aM : ι → (X → ℂ) → (X → ℂ)} {v : X → ℂ}
  {ip : (X → ℂ) → (X → ℂ) → ℂ}

theorem ip_zero_left (hs : IsSesq Sm ip) (h0 : (0 : X → ℂ) ∈ Sm) {f : X → ℂ} (hf : f ∈ Sm) : ip 0 f = 0 := by
  have e := (hs 0 0 f 1 h0 h0 hf).1
  rw [smul_zero, add_zero, one_mul] at e
  linear_combination -e

theorem ip_zero_right (hs : IsSesq Sm ip) (h0 : (0 : X → ℂ) ∈ Sm) {f : X → ℂ} (hf : f ∈ Sm) : ip f 0 = 0 := by
  have e := (hs 0 0 f 1 h0 h0 hf).2
  rw [smul_zero, add_zero, map_one, one_mul] at e
  linear_combination -e

theorem ip_smul_left (hs : IsSesq Sm ip) (h0 : (0 : X → ℂ) ∈ Sm) (c : ℂ) {g h : X → ℂ} (hg : g ∈ Sm) (hh : h ∈ Sm) :
    ip (c • g) h = c * ip g h := by
  have e := (hs 0 g h c h0 hg hh).1
  rwa [zero_add, ip_zero_left hs h0 hh, zero_add] at e

theorem ip_smul_right (hs : IsSesq Sm ip) (h0 : (0 : X → ℂ) ∈ Sm) (c : ℂ) {g h : X → ℂ} (hg : g ∈ Sm) (hh : h ∈ Sm) :
    ip h (c • g) = starRingEnd ℂ c * ip h g := by
  have e := (hs 0 g h c h0 hg hh).2
  rwa [zero_add, ip_zero_right hs h0 hh, zero_add] at e

theorem ip_add_left (hs : IsSesq Sm ip) {f g h : X → ℂ} (hf : f ∈ Sm) (hg : g ∈ Sm) (hh : h ∈ Sm) :
    ip (f + g) h = ip f h + ip g h := by
  have e := (hs f g h 1 hf hg hh).1
  rwa [one_smul, one_mul] at e

theorem ip_add_right (hs : IsSesq Sm ip) {f g h : X → ℂ} (hf : f ∈ Sm) (hg : g ∈ Sm) (hh : h ∈ Sm) :
    ip h (f + g) = ip h f + ip h g := by
  have e := (hs f g h 1 hf hg hh).2
  rwa [one_smul, map_one, one_mul] at e

theorem sum_mem' (h : IsCCR Sm aP aM) {β : Type} (S : Finset β) (c : β → ℂ) (f : β → X → ℂ)
    (hf : ∀ b ∈ S, f b ∈ Sm) : ∑ b ∈ S, c b • f b ∈ Sm := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact h.zero_mem
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact h.add_mem _ _ (h.smul_mem _ _ (hf a (Finset.mem_insert_self a s)))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem ip_sum_left (h : IsCCR Sm aP aM) (hs : IsSesq Sm ip) {β : Type} (S : Finset β) (c : β → ℂ)
    (f : β → X → ℂ) (hf : ∀ b ∈ S, f b ∈ Sm) {g : X → ℂ} (hg : g ∈ Sm) :
    ip (∑ b ∈ S, c b • f b) g = ∑ b ∈ S, c b * ip (f b) g := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ip_zero_left hs h.zero_mem hg
  | @insert a s ha ih =>
    have hf' : ∀ b ∈ s, f b ∈ Sm := fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have ha' : f a ∈ Sm := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ip_add_left hs (h.smul_mem _ _ ha') (sum_mem' h s c f hf') hg,
      ip_smul_left hs h.zero_mem _ ha' hg, ih hf']

theorem ip_sum_right (h : IsCCR Sm aP aM) (hs : IsSesq Sm ip) {β : Type} (S : Finset β) (c : β → ℂ)
    (f : β → X → ℂ) (hf : ∀ b ∈ S, f b ∈ Sm) {g : X → ℂ} (hg : g ∈ Sm) :
    ip g (∑ b ∈ S, c b • f b) = ∑ b ∈ S, starRingEnd ℂ (c b) * ip g (f b) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ip_zero_right hs h.zero_mem hg
  | @insert a s ha ih =>
    have hf' : ∀ b ∈ s, f b ∈ Sm := fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have ha' : f a ∈ Sm := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ip_add_right hs (h.smul_mem _ _ ha') (sum_mem' h s c f hf') hg,
      ip_smul_right hs h.zero_mem _ ha' hg, ih hf']

def fct (α : ι →₀ ℕ) : ℕ := ∏ k ∈ α.support, (α k).factorial

private theorem fct_eq_lemma {β : ι →₀ ℕ} {T : Finset ι} (hT : β.support ⊆ T) :
    fct β = ∏ k ∈ T, (β k).factorial := by
  unfold fct
  refine Finset.prod_subset hT (fun k _ hk => ?_)
  have e : β k = 0 := by simpa using hk
  rw [e, Nat.factorial_zero]

theorem fct_add_single (α : ι →₀ ℕ) (j : ι) : fct (α + Finsupp.single j 1) = (α j + 1) * fct α := by
  classical
  have hT1 : (α + Finsupp.single j 1).support ⊆ insert j α.support := by
    intro k hk
    by_cases hkj : k = j
    · rw [hkj]; exact Finset.mem_insert_self j _
    · rw [Finset.mem_insert]
      right
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa [Finsupp.single_apply, Ne.symm hkj] using hk
  have hT0 : α.support ⊆ insert j α.support := Finset.subset_insert _ _
  rw [fct_eq_lemma hT1, fct_eq_lemma hT0, ← Finset.mul_prod_erase (insert j α.support) _ (Finset.mem_insert_self j _),
    ← Finset.mul_prod_erase (insert j α.support) (fun k => (α k).factorial) (Finset.mem_insert_self j _)]
  have e : ∏ x ∈ (insert j α.support).erase j, ((α + Finsupp.single j 1 : ι →₀ ℕ) x).factorial =
      ∏ x ∈ (insert j α.support).erase j, (α x).factorial :=
    Finset.prod_congr rfl (fun x hx => by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero])
  rw [e, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, mul_assoc]

private theorem sub_single_add_lemma_2 (β : ι →₀ ℕ) (a : ι) (h : β a ≠ 0) :
    β - Finsupp.single a 1 + Finsupp.single a 1 = β := by
  ext k
  by_cases hk : a = k
  · subst hk
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply, if_neg hk]
    omega

theorem ip_opPow (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (hvac : ∀ i, aM i v = 0) (hs : IsSesq Sm ip)
    (hMP : ∀ i f g, f ∈ Sm → g ∈ Sm → ip (aM i f) g = ip f (aP i g))
    (hPM : ∀ i f g, f ∈ Sm → g ∈ Sm → ip (aP i f) g = ip f (aM i g)) (s : Multiset ι) :
    ∀ β : ι →₀ ℕ, ip (opPow aP (Multiset.toFinsupp s) v) (opPow aP β v) =
      if Multiset.toFinsupp s = β then (fct β : ℂ) * ip v v else 0 := by
  induction s using Multiset.induction_on with
  | empty =>
    intro β
    rw [Multiset.toFinsupp_zero, opPow_zero]
    by_cases hβ : (0 : ι →₀ ℕ) = β
    · rw [if_pos hβ, ← hβ, opPow_zero]
      simp [fct]
    · rw [if_neg hβ]
      obtain ⟨j, hj⟩ : ∃ j, β j ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hβ (Finsupp.ext fun k => (hc k).symm)
      rw [← sub_single_add_lemma_2 β j hj, opPow_add_single h hv, ← hMP j v _ hv (opPow_mem h hv _), hvac j,
        ip_zero_left hs h.zero_mem (opPow_mem h hv _)]
  | @cons a t ih =>
    intro β
    have e : Multiset.toFinsupp (a ::ₘ t) = Multiset.toFinsupp t + Finsupp.single a 1 := by
      rw [← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton, add_comm]
    rw [e, opPow_add_single h hv, hPM a _ _ (opPow_mem h hv _) (opPow_mem h hv _), aM_opPow h hv a (hvac a),
      ip_smul_right hs h.zero_mem _ (opPow_mem h hv _) (opPow_mem h hv _), ih, map_natCast]
    by_cases hβa : β a = 0
    · rw [hβa, Nat.cast_zero, zero_mul, if_neg]
      intro hc
      have := congrArg (fun f => f a) hc
      simp [hβa] at this
    · have hd := sub_single_add_lemma_2 β a hβa
      by_cases ht : Multiset.toFinsupp t = β - Finsupp.single a 1
      · rw [if_pos ht, if_pos (by rw [ht, hd])]
        conv_rhs => rw [← hd, fct_add_single]
        have e' : (((β - Finsupp.single a 1 : ι →₀ ℕ) a + 1 : ℕ) : ℂ) = ((β a : ℕ) : ℂ) := by
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hβa)]
        rw [Nat.cast_mul, e', mul_assoc]
      · rw [if_neg ht, if_neg, mul_zero]
        intro hc
        apply ht
        rw [← hc, add_tsub_cancel_right]

end Norm

theorem fockNormAbs : FockNormAbs := by
  unfold FockNormAbs
  intro ι X _ Sm aP aM v ip h hv hvac hs hMP hPM P Q
  have hO : ∀ α β : ι →₀ ℕ, ip (opPow aP α v) (opPow aP β v) = if α = β then (fct β : ℂ) * ip v v else 0 :=
    fun α β => by
      have e := ip_opPow h hv hvac hs hMP hPM (Finsupp.toMultiset α) β
      first | simpa only [Finsupp.toMultiset_toFinsupp] using e | simpa using e
  rw [pt_sum, pt_sum, ip_sum_left h hs _ _ _ (fun α _ => opPow_mem h hv α)
    (sum_mem' h _ _ _ (fun β _ => opPow_mem h hv β))]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [ip_sum_right h hs _ _ _ (fun β _ => opPow_mem h hv β) (opPow_mem h hv α)]
  simp only [hO, mul_ite, mul_zero, Finset.sum_ite_eq, starRingEnd_apply]
  by_cases hα : α ∈ Q.support
  · rw [if_pos hα]
    unfold fct
    ring
  · rw [if_neg hα]
    have e : Q.coeff α = 0 := by simpa using hα
    rw [e]
    simp

section Mat

theorem cart_of {k : ℕ} {B Bi D s G : Matrix (Fin k) (Fin k) ℂ} (h1 : Bi * B = 1) (h2 : B * Bi = 1)
    (hD : D * D = 1) (hDh : Dᴴ = D) (hs : s = B * D * Bi) (hG : G = Biᴴ * D * Bi) :
    s * s = 1 ∧ sᴴ * G * s = G ∧ sᴴ * G = G * s ∧ (B * D * Bᴴ) * sᴴ = s * (B * D * Bᴴ) ∧ G * (B * D * Bᴴ) = 1 := by
  have hBh : Bᴴ * Biᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hBh2 : Biᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have c1 : ∀ Y : Matrix (Fin k) (Fin k) ℂ, Bi * (B * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have c2 : ∀ Y : Matrix (Fin k) (Fin k) ℂ, B * (Bi * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ Y : Matrix (Fin k) (Fin k) ℂ, D * (D * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hD, Matrix.one_mul]
  have c4 : ∀ Y : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Biᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hBh, Matrix.one_mul]
  have c5 : ∀ Y : Matrix (Fin k) (Fin k) ℂ, Biᴴ * (Bᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hBh2, Matrix.one_mul]
  subst hs hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.conjTranspose_mul, hDh, Matrix.mul_assoc, c1, c2, c3, c4, c5, h2, hBh2, hD]

theorem onb_data {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) :
    ∃ ε : Fin k → ℝ, (∀ a, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) ∧ B⁻¹ * B = 1 ∧ B * B⁻¹ = 1 ∧
      s = B * diagonal (fun a => (ε a : ℂ)) * B⁻¹ ∧ G = B⁻¹ᴴ * diagonal (fun a => (ε a : ℂ)) * B⁻¹ ∧
      G⁻¹ = B * diagonal (fun a => (ε a : ℂ)) * Bᴴ ∧
      s * s = 1 ∧ sᴴ * G * s = G ∧ sᴴ * G = G * s ∧ G⁻¹ * sᴴ = s * G⁻¹ := by
  unfold IsONBasis at h
  obtain ⟨ε, hε, hG, hs⟩ := h
  refine ⟨ε, hε, ?_⟩
  have hD : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hDh : (diagonal fun a => (ε a : ℂ))ᴴ = diagonal fun a => (ε a : ℂ) := by
    rw [diagonal_conjTranspose]
    congr 1
    funext a
    simp
  generalize (diagonal fun a => (ε a : ℂ)) = D at hG hs hD hDh ⊢
  have hB : IsUnit B.det :=
    Matrix.isUnit_det_of_left_inverse (show (D * (Bᴴ * G)) * B = 1 by rw [Matrix.mul_assoc, hG, hD])
  have hBi1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBi2 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hs' : s = B * D * B⁻¹ := by rw [← hs, Matrix.mul_assoc, hBi2, Matrix.mul_one]
  have c : ∀ Y : Matrix (Fin k) (Fin k) ℂ, B⁻¹ᴴ * (Bᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hBi2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hG' : G = B⁻¹ᴴ * D * B⁻¹ := by
    rw [← hG]
    simp only [Matrix.mul_assoc, c, hBi2, Matrix.mul_one]
  have hc := cart_of hBi1 hBi2 hD hDh hs' hG'
  have hGinv : G⁻¹ = B * D * Bᴴ := Matrix.inv_eq_right_inv hc.2.2.2.2
  exact ⟨hBi1, hBi2, hs', hG', hGinv, hc.1, hc.2.1, hc.2.2.1, by rw [hGinv]; exact hc.2.2.2.1⟩

theorem eps_prod {m n pS pT : ℕ} {εS : Fin n → ℝ} {εT : Fin m → ℝ}
    (hεS : ∀ a, (εS a = 1 ∧ a.val < pS) ∨ (εS a = -1 ∧ pS ≤ a.val))
    (hεT : ∀ a, (εT a = 1 ∧ a.val < pT) ∨ (εT a = -1 ∧ pT ≤ a.val)) (i : Fin m) (c : Fin n) :
    (εT i : ℂ) * (εS c : ℂ) = if PosF pS pT i c then 1 else -1 := by
  rcases hεS c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hεT i with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h1, h3]
  · rw [if_pos (show PosF pS pT i c from iff_of_true h4 h2)]; norm_num
  · rw [if_neg (show ¬ PosF pS pT i c from fun hp => absurd (Iff.mpr hp h2) (by omega))]; norm_num
  · rw [if_neg (show ¬ PosF pS pT i c from fun hp => absurd (Iff.mp hp h4) (by omega))]; norm_num
  · rw [if_pos (show PosF pS pT i c from iff_of_false (by omega) (by omega))]; norm_num

theorem diag_single_diag {p q r : ℕ} (d : Fin p → ℂ) (d' : Fin q → ℂ) (a : Fin p) (b : Fin q) (x : ℂ)
    (Y : Matrix (Fin q) (Fin r) ℂ) :
    diagonal d * (Matrix.single a b x * (diagonal d' * Y)) = Matrix.single a b (d a * x * d' b) * Y := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.diagonal_apply, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mul_sum, Finset.sum_mul]
  split_ifs <;> subst_vars <;> first | ring1 | (exfalso; simp_all)

theorem trace_single_mul_single {p q : ℕ} (a : Fin p) (b b' : Fin q) (e : Fin p) (x y : ℂ) :
    (Matrix.single a b x * Matrix.single b' e y).trace = if b = b' ∧ a = e then x * y else 0 := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  split_ifs <;> simp_all

variable {m n : ℕ}

def tt (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  (GS⁻¹ * wᴴ * GT * z).trace

theorem eM_eq (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (ξ : ℂ) (z w : Matrix (Fin m) (Fin n) ℂ) :
    eM GS GT ξ z w = 2 * (ξ * tt GS GT z w).re := rfl

theorem tt_smul_left (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (z w : Matrix (Fin m) (Fin n) ℂ) : tt GS GT (c • z) w = c * tt GS GT z w := by
  unfold tt
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem tt_smul_right (GS : Matrix (Fin n) (Fin n) ℂ) (GT : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (z w : Matrix (Fin m) (Fin n) ℂ) : tt GS GT z (c • w) = star c * tt GS GT z w := by
  unfold tt
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem tt_JJ {GS sS : Matrix (Fin n) (Fin n) ℂ} {GT sT : Matrix (Fin m) (Fin m) ℂ} (hS : sS * sS = 1)
    (hS3 : GS⁻¹ * sSᴴ = sS * GS⁻¹) (hT2 : sTᴴ * GT * sT = GT) (z w : Matrix (Fin m) (Fin n) ℂ) :
    tt GS GT (cplxO sS sT z) (cplxO sS sT w) = tt GS GT z w := by
  have hI : Complex.I * star Complex.I = 1 := by
    first | simp | simp [Complex.ext_iff]
  unfold cplxO
  rw [tt_smul_left, tt_smul_right, ← mul_assoc, hI, one_mul]
  unfold tt
  have e1 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, GS⁻¹ * (sSᴴ * Y) = sS * (GS⁻¹ * Y) := fun Y => by
    rw [← Matrix.mul_assoc, hS3, Matrix.mul_assoc]
  have e2 : ∀ Y : Matrix (Fin m) (Fin n) ℂ, sTᴴ * (GT * (sT * Y)) = GT * Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hT2]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, e2]
  rw [Matrix.trace_mul_comm sS]
  simp only [Matrix.mul_assoc]
  rw [hS, Matrix.mul_one]

theorem tt_swap {GS sS : Matrix (Fin n) (Fin n) ℂ} {GT sT : Matrix (Fin m) (Fin m) ℂ}
    (hS3 : GS⁻¹ * sSᴴ = sS * GS⁻¹) (hT1 : sTᴴ * GT = GT * sT) (z w : Matrix (Fin m) (Fin n) ℂ) :
    tt GS GT z (sT * w * sS) = tt GS GT (sT * z * sS) w := by
  unfold tt
  have e1 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, GS⁻¹ * (sSᴴ * Y) = sS * (GS⁻¹ * Y) := fun Y => by
    rw [← Matrix.mul_assoc, hS3, Matrix.mul_assoc]
  have e2 : sTᴴ * (GT * z) = GT * (sT * z) := by rw [← Matrix.mul_assoc, hT1, Matrix.mul_assoc]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, e2]
  rw [Matrix.trace_mul_comm sS]
  simp only [Matrix.mul_assoc]

theorem J_unit {pS pT : ℕ} {GS sS BS : Matrix (Fin n) (Fin n) ℂ} {GT sT BT : Matrix (Fin m) (Fin m) ℂ}
    (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (i : Fin m) (c : Fin n) :
    cplxO sS sT (unitMap BS BT i c) = (if PosF pS pT i c then Complex.I else -Complex.I) • unitMap BS BT i c := by
  obtain ⟨εS, hεS, hS1, hS2, hsS, -, -, -, -, -, -⟩ := onb_data hS
  obtain ⟨εT, hεT, hT1, hT2, hsT, -, -, -, -, -, -⟩ := onb_data hT
  unfold cplxO unitMap
  rw [hsS, hsT]
  have key : BT * diagonal (fun a : Fin m => (εT a : ℂ)) * BT⁻¹ * (BT * single i c (1 : ℂ) * BS⁻¹) *
      (BS * diagonal (fun a : Fin n => (εS a : ℂ)) * BS⁻¹) =
      BT * (single i c ((εT i : ℂ) * 1 * (εS c : ℂ)) * BS⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc BT⁻¹ BT, hT1, Matrix.one_mul, ← Matrix.mul_assoc BS⁻¹ BS, hS1, Matrix.one_mul,
      diag_single_diag]
  rw [key, mul_one, eps_prod hεS hεT i c]
  split_ifs
  · rw [Matrix.mul_assoc BT]
  · have e : single i c (-1 : ℂ) = (-1 : ℂ) • single i c 1 := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc BT]
    congr 1
    ring

theorem tt_unit {pS pT : ℕ} {GS sS BS : Matrix (Fin n) (Fin n) ℂ} {GT sT BT : Matrix (Fin m) (Fin m) ℂ}
    (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (i : Fin m) (c : Fin n) (i' : Fin m) (c' : Fin n) :
    tt GS GT (unitMap BS BT i c) (unitMap BS BT i' c') =
      if i = i' ∧ c = c' then (if PosF pS pT i c then 1 else -1) else 0 := by
  obtain ⟨εS, hεS, hS1, hS2, -, -, hGSi, -, -, -, -⟩ := onb_data hS
  obtain ⟨εT, hεT, hT1, hT2, -, hGT, -, -, -, -, -⟩ := onb_data hT
  unfold tt unitMap
  rw [hGSi, hGT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one]
  have cS : ∀ Y : Matrix (Fin n) (Fin n) ℂ, BSᴴ * (BS⁻¹ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hS1, Matrix.conjTranspose_one, Matrix.one_mul]
  have cT : ∀ Y : Matrix (Fin m) (Fin n) ℂ, BTᴴ * (BT⁻¹ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hT1, Matrix.conjTranspose_one, Matrix.one_mul]
  have cT2 : ∀ Y : Matrix (Fin m) (Fin n) ℂ, BT⁻¹ * (BT * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hT1, Matrix.one_mul]
  simp only [Matrix.mul_assoc, cS, cT, cT2]
  rw [diag_single_diag, Matrix.trace_mul_comm BS]
  simp only [Matrix.mul_assoc]
  rw [hS1, Matrix.mul_one, trace_single_mul_single]
  beta_reduce
  by_cases hic : i = i' ∧ c = c'
  · rw [← hic.1, ← hic.2, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, ← eps_prod hεS hεT i c]
    ring
  · rw [if_neg (fun h' => hic ⟨h'.1.symm, h'.2.symm⟩), if_neg hic]

end Mat

theorem unitBracket : UnitBracket := by
  unfold UnitBracket
  intro m n pS pT GS sS BS GT sT BT ξ hS hT hre him
  obtain ⟨εS, hεS, hS1, hS2, hsS, hGS, hGSi, hSS, hS2', hSG, hS3⟩ := onb_data hS
  obtain ⟨εT, hεT, hT1, hT2, hsT, hGT, hGTi, hTT, hTG2, hTG, hT3⟩ := onb_data hT
  have hJ : ∀ z w : Matrix (Fin m) (Fin n) ℂ, tt GS GT (cplxO sS sT z) (cplxO sS sT w) = tt GS GT z w :=
    fun z w => tt_JJ hSS hS3 hTG2 z w
  have hL : ∀ z w : Matrix (Fin m) (Fin n) ℂ,
      tt GS GT (cplxO sS sT z) w = Complex.I * tt GS GT (sT * z * sS) w := by
    intro z w
    unfold cplxO
    rw [tt_smul_left]
  have hR : ∀ z w : Matrix (Fin m) (Fin n) ℂ,
      tt GS GT z (cplxO sS sT w) = -Complex.I * tt GS GT (sT * z * sS) w := by
    intro z w
    unfold cplxO
    rw [tt_smul_right, tt_swap hS3 hTG]
    congr 1
    first | simp | rfl
  refine ⟨fun i c => J_unit hS hT i c, fun i c i' c' => ?_, fun z w => ?_⟩
  · have hu : sT * unitMap BS BT i c * sS =
        (if PosF pS pT i c then (1 : ℂ) else -1) • unitMap BS BT i c := by
      have e := J_unit hS hT i c
      unfold cplxO at e
      calc sT * unitMap BS BT i c * sS
          = ((-Complex.I) * Complex.I) • (sT * unitMap BS BT i c * sS) := by
            rw [show (-Complex.I) * Complex.I = 1 by simp, one_smul]
        _ = (-Complex.I) • (Complex.I • (sT * unitMap BS BT i c * sS)) := by rw [smul_smul]
        _ = (-Complex.I) • ((if PosF pS pT i c then Complex.I else -Complex.I) • unitMap BS BT i c) := by
            rw [e]
        _ = (if PosF pS pT i c then (1 : ℂ) else -1) • unitMap BS BT i c := by
            rw [smul_smul]
            congr 1
            split_ifs <;> simp
    unfold brk
    simp only [eM_eq, hJ, hL, hR]
    rw [hu, tt_smul_left, tt_unit hS hT i c i' c']
    by_cases hic : i = i' ∧ c = c'
    · rw [if_pos hic, if_pos hic]
      by_cases hP : PosF pS pT i c
      · simp only [hP, if_true]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre] <;> ring
      · simp only [hP, if_false]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre] <;> ring
    · rw [if_neg hic, if_neg hic]
      simp
  · unfold brkPP
    simp only [eM_eq, hJ, hL, hR]
    rw [neg_mul, mul_neg, Complex.neg_re]
    push_cast
    ring

end Formalism.IndefR.Fock.Alg

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder Pointwise

namespace Formalism.IndefR.Fock.Skew

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem psi_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    ψ a * starRingEnd ℂ (ψ a) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 a]
  simp

theorem prod_inv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (γ : ratL T S) (w : WO S T) :
    f (γ +ᵥ w) * starRingEnd ℂ (g (γ +ᵥ w)) = f w * starRingEnd ℂ (g w) := by
  obtain ⟨e, he⟩ := γ.2
  have hγ : γ +ᵥ w = ratW T S e + w := by
    show (γ : WO S T) + w = _
    rw [← he]
    rfl
  rw [hγ, hf.quasi, hg.quasi, map_mul]
  calc _ = (ψ (-(symplOH S T (ratW T S e) w)) * starRingEnd ℂ (ψ (-(symplOH S T (ratW T S e) w)))) *
        (f w * starRingEnd ℂ (g w)) := by ring
    _ = _ := by rw [psi_mul_conj hψ]; ring

theorem bdd_of_inv {S T : HSp D} (F : WO S T → ℂ) (hc : Continuous F) (hinv : ∀ (γ : ratL T S) w, F (γ +ᵥ w) = F w) :
    ∃ C, ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨K, hK, hsub⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, -⟩ := Formalism.IndefR.PHeisFC.exU T S x
  rw [← hinv γ x]
  exact hC _ (hsub hγ)

theorem integral_translate {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) [μ.IsAddHaarMeasure]
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (F : WO S T → ℂ)
    (hinv : ∀ (γ : ratL T S) w, F (γ +ᵥ w) = F w) (v : WO S T) :
    ∫ w in 𝓕, F (v + w) ∂μ = ∫ w in 𝓕, F w ∂μ := by
  have := Formalism.IndefR.PHeisFC.countable_ratL T S
  have : MeasurableConstVAdd (ratL T S) (WO S T) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have : MeasurableConstVAdd (WO S T) (WO S T) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (WO S T) (WO S T) μ :=
    ⟨fun c s _ => measure_preimage_add μ c s⟩
  have : VAddCommClass (WO S T) (ratL T S) (WO S T) :=
    ⟨fun a γ x => by
      show a + ((γ : WO S T) + x) = (γ : WO S T) + (a + x)
      abel⟩
  have h𝓕' : IsAddFundamentalDomain (ratL T S) (v +ᵥ 𝓕) μ := h𝓕.vadd_of_comm v
  have hemb : MeasurableEmbedding (fun w : WO S T => v + w) := (Homeomorph.addLeft v).measurableEmbedding
  have hpre : (fun w : WO S T => v + w) ⁻¹' (v +ᵥ 𝓕) = 𝓕 := by
    ext w
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have key := (measurePreserving_add_left μ v).setIntegral_preimage_emb hemb F (v +ᵥ 𝓕)
  rw [hpre] at key
  rw [key]
  exact h𝓕'.setIntegral_eq h𝓕 hinv

theorem heis_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (f g : WO S T → ℂ)
    (v w : WO S T) :
    heisO ψ S T v f w * starRingEnd ℂ (heisO ψ S T v g w) = f (w + v) * starRingEnd ℂ (g (w + v)) := by
  unfold heisO
  rw [map_mul]
  calc _ = (ψ (symplOH S T w v) * starRingEnd ℂ (ψ (symplOH S T w v))) * (f (w + v) * starRingEnd ℂ (g (w + v))) := by
        ring
    _ = _ := by rw [psi_mul_conj hψ]; ring

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (f : WO S T → ℂ) (w : WO S T) :
    heisO ψ S T 0 f w = f w := by
  unfold heisO symplOH symplO hO
  simp

theorem skew_core {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1)) {S T : HSp D} (μ : Measure (WO S T))
    (𝓕 : Set (WO S T)) [μ.IsAddHaarMeasure] (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (h1 : μ 𝓕 = 1)
    (L : ℝ →+ WO S T) (f g df dg : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (hdf : IsThetaFunO ψ S T df) (hdg : IsThetaFunO ψ S T dg)
    (hderf : ∀ x, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f x) (df x) 0)
    (hderg : ∀ x, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) g x) (dg x) 0) :
    ∫ w in 𝓕, df w * starRingEnd ℂ (g w) ∂μ = -∫ w in 𝓕, f w * starRingEnd ℂ (dg w) ∂μ := by
  obtain ⟨G, hG⟩ : ∃ G : WO S T → ℂ, G = fun w => f w * starRingEnd ℂ (g w) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : WO S T → ℂ, H = fun w => df w * starRingEnd ℂ (g w) + f w * starRingEnd ℂ (dg w) :=
    ⟨_, rfl⟩
  have hcc : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  have hGc : Continuous G := by rw [hG]; exact hf.cont.mul (hcc.comp hg.cont)
  have hH1c : Continuous fun w => df w * starRingEnd ℂ (g w) := hdf.cont.mul (hcc.comp hg.cont)
  have hH2c : Continuous fun w => f w * starRingEnd ℂ (dg w) := hf.cont.mul (hcc.comp hdg.cont)
  have hHc : Continuous H := by rw [hH]; exact hH1c.add hH2c
  have hGi : ∀ (γ : ratL T S) w, G (γ +ᵥ w) = G w := by rw [hG]; exact prod_inv hstd hf hg
  have hH1i : ∀ (γ : ratL T S) w, df (γ +ᵥ w) * starRingEnd ℂ (g (γ +ᵥ w)) = df w * starRingEnd ℂ (g w) :=
    prod_inv hstd hdf hg
  have hH2i : ∀ (γ : ratL T S) w, f (γ +ᵥ w) * starRingEnd ℂ (dg (γ +ᵥ w)) = f w * starRingEnd ℂ (dg w) :=
    prod_inv hstd hf hdg
  have hHi : ∀ (γ : ratL T S) w, H (γ +ᵥ w) = H w := fun γ w => by
    rw [hH]; simp only; rw [hH1i, hH2i]
  obtain ⟨CG, hCG⟩ := bdd_of_inv G hGc hGi
  obtain ⟨CH, hCH⟩ := bdd_of_inv H hHc hHi
  obtain ⟨C1, hC1⟩ := bdd_of_inv _ hH1c hH1i
  obtain ⟨C2, hC2⟩ := bdd_of_inv _ hH2c hH2i

  have hd0 : ∀ w, HasDerivAt (fun t : ℝ => G (w + L t)) (H w) 0 := by
    intro w
    have hp : HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w * star (heisO ψ S T (L t) g w))
        (df w * star (heisO ψ S T (L 0) g w) + heisO ψ S T (L 0) f w * star (dg w)) 0 :=
      (hderf w).mul (hderg w).star
    have e1 : (fun t : ℝ => heisO ψ S T (L t) f w * star (heisO ψ S T (L t) g w)) = fun t => G (w + L t) := by
      funext t
      rw [← starRingEnd_apply, heis_mul_conj hstd, hG]
    have e2 : df w * star (heisO ψ S T (L 0) g w) + heisO ψ S T (L 0) f w * star (dg w) = H w := by
      rw [map_zero, heisO_zero, heisO_zero, hH, ← starRingEnd_apply, ← starRingEnd_apply]
    rw [e1, e2] at hp
    exact hp
  have hdt : ∀ w (t : ℝ), HasDerivAt (fun s : ℝ => G (w + L s)) (H (w + L t)) t := by
    intro w t
    have h0 : HasDerivAt (fun s : ℝ => G (w + L t + L s)) (H (w + L t)) (t - t) := by
      rw [sub_self]; exact hd0 (w + L t)
    have h2 := h0.comp_sub_const t t
    have e : (fun s : ℝ => G (w + L s)) = fun s => G (w + L t + L (s - t)) := by
      funext s
      rw [add_assoc, ← map_add, add_sub_cancel]
    rw [e]
    exact h2

  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  have hint : ∀ (F : WO S T → ℂ) (C : ℝ), Continuous F → (∀ x, ‖F x‖ ≤ C) → Integrable F (μ.restrict 𝓕) :=
    fun F C hc hb => Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hb)
  have hsh : ∀ t : ℝ, Continuous fun w : WO S T => w + L t := fun t => continuous_id.add continuous_const

  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) w => G (w + L t)) (F' := fun (t : ℝ) w => H (w + L t)) (bound := fun _ => CH)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hGc.comp (hsh t)).aestronglyMeasurable)
    (hint _ CG (hGc.comp (hsh 0)) fun x => hCG _)
    ((hHc.comp (hsh 0)).aestronglyMeasurable)
    (ae_of_all _ fun w t _ => hCH _) (integrable_const CH)
    (ae_of_all _ fun w t _ => hdt w t)
  have hconst : (fun t : ℝ => ∫ w in 𝓕, G (w + L t) ∂μ) = fun _ => ∫ w in 𝓕, G w ∂μ := by
    funext t
    rw [← integral_translate μ 𝓕 h𝓕 G hGi (L t)]
    congr 1
    funext w
    rw [add_comm]
  have hzero : ∫ w in 𝓕, H (w + L 0) ∂μ = 0 := by
    have h := hmain.2
    rw [hconst] at h
    exact h.unique (hasDerivAt_const _ _)
  rw [map_zero] at hzero
  simp only [add_zero] at hzero
  rw [hH] at hzero
  rw [integral_add (hint _ C1 hH1c hC1) (hint _ C2 hH2c hC2)] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

theorem dRhoSkew_of (D : D7) (hT : Formalism.IndefR.Fock.Sk.ThetaDRho D) : Formalism.IndefR.Fock.Sk.DRhoSkew D := by
  intro ψ θ hstd hinf hline S T τ z μ 𝓕 hcov f g hf hg
  obtain ⟨hdf, hderf⟩ := hT ψ θ hstd hinf hline S T τ z f hf
  obtain ⟨hdg, hderg⟩ := hT ψ θ hstd hinf hline S T τ z g hg
  obtain ⟨hHaar, h𝓕, h1⟩ := hcov
  exact skew_core hstd μ 𝓕 h𝓕 h1 (lineAt θ τ z) f g _ _ hf hg hdf hdg hderf hderg

theorem thetaIntO (D : D7) : Formalism.IndefR.Fock.Sk.ThetaIntO D := by
  intro ψ hstd S T μ 𝓕 hcov f g hf hg
  obtain ⟨hHaar, h𝓕, h1⟩ := hcov
  have hc : Continuous fun w => f w * starRingEnd ℂ (g w) := hf.cont.mul (Complex.continuous_conj.comp hg.cont)
  obtain ⟨C, hC⟩ := bdd_of_inv _ hc (prod_inv hstd hf hg)
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)

end Formalism.IndefR.Fock.Skew

end
end

section
noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fock.DeltaPf

open Formalism.REAL

theorem fockF_eq_sum_of_subset {σ : Type*} {f g : MvPolynomial σ ℂ} {s : Finset (σ →₀ ℕ)} (h : f.support ⊆ s) :
    fockF f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_one {σ : Type*} : fockF (1 : MvPolynomial σ ℂ) 1 = 1 := by
  classical
  rw [fockF_eq_sum_of_subset (s := {0})]
  · simp
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    rw [Finset.mem_singleton]
    by_contra h0
    exact hm (if_neg (Ne.symm h0))


theorem fockF_rename {σ τ : Type*} {i : σ → τ} (hi : Function.Injective i) (f g : MvPolynomial σ ℂ) :
    fockF (rename i f) (rename i g) = fockF f g := by
  classical
  unfold fockF
  rw [MvPolynomial.support_rename_of_injective hi, Finset.sum_image (by
    intro a _ b _ hab
    exact Finsupp.mapDomain_injective hi hab)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain i hi, MvPolynomial.coeff_rename_mapDomain i hi,
    Finsupp.mapDomain_support_of_injective hi, Finset.prod_image (by
      intro a _ b _ hab
      exact hi hab)]
  simp only [Finsupp.mapDomain_apply hi]





theorem rename_mem_supported {σ τ : Type*} (i : σ → τ) (f : MvPolynomial σ ℂ) :
    rename i f ∈ supported ℂ (Set.range i) := by
  classical
  rw [MvPolynomial.mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename i f (Finset.mem_coe.1 hv))
  exact ⟨w, rfl⟩

def PmEq {R : Type*} [Ring R] (f g : R) : Prop := f = g ∨ f = -g

theorem PmEq.mul {R : Type*} [Ring R] {f g f' g' : R} (h : PmEq f g) (h' : PmEq f' g') : PmEq (f * f') (g * g') := by
  unfold PmEq at *
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (mul_neg _ _)
  · exact Or.inr (neg_mul _ _)
  · exact Or.inl (neg_mul_neg _ _)

theorem PmEq.pow {R : Type*} [Ring R] {f g : R} (h : PmEq f g) (k : ℕ) : PmEq (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact Or.inl (by rw [pow_zero, pow_zero])
  | succ k ih => simpa only [pow_succ] using ih.mul h

theorem PmEq.prod {ι R : Type*} [CommRing R] (s : Finset ι) (f g : ι → R) (h : ∀ i ∈ s, PmEq (f i) (g i)) :
    PmEq (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))



theorem PmEq.mem {σ : Type*} {S : Set σ} {f g : MvPolynomial σ ℂ} (h : PmEq f g) (hg : g ∈ supported ℂ S) :
    f ∈ supported ℂ S := by
  unfold PmEq at h
  rcases h with rfl | rfl
  · exact hg
  · exact neg_mem hg


section Spec

variable {D : D7} {m n : ℕ}

def iotaP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (v : Fin P × Fin P) : FVar D m n :=
  (τ, Fin.castLE hm v.2, Fin.castLE hn v.1)

def embedding₂ (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (v : Fin Q × Fin Q) : FVar D m n :=
  (τ, ⟨P + v.2, by have := v.2.isLt; omega⟩, ⟨n - 1 - v.1, by have := v.1.isLt; omega⟩)



def psiP (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) :
    MvPolynomial (Fin P × Fin P) ℚ →+* MvPolynomial (FVar D m n) ℂ :=
  (rename (iotaP τ hm hn)).toRingHom.comp (map (algebraMap ℚ ℂ))

def psiM (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) :
    MvPolynomial (Fin Q × Fin Q) ℚ →+* MvPolynomial (FVar D m n) ℂ :=
  (rename (embedding₂ τ P hm hn)).toRingHom.comp (map (algebraMap ℚ ℂ))

theorem minorPlus_eq (τ : D.what₂.Tau) {P : ℕ} (hm : P ≤ m) (hn : P ≤ n) (k : ℕ) (hk : k ≤ P) (hk' : k ≤ P) :
    psiP τ hm hn (Formalism.GradedWeylDivisibility.lpMinor ℚ k hk hk') = minorPlus τ k := by
  unfold minorPlus Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun α β => ?_)
  have hα := α.isLt
  have hβ := β.isLt
  simp [psiP, iotaP, varF, RingHom.mapMatrix_apply]
  split_ifs with h
  · rfl
  · exact absurd ⟨by omega, by omega⟩ h

theorem minorMinus_eq (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n) (k : ℕ) (hk : k ≤ Q)
    (hk' : k ≤ Q) :
    minorMinus τ P k =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : MvPolynomial (FVar D m n) ℂ) *
        psiM τ P hm hn (Formalism.GradedWeylDivisibility.lpMinor ℚ k hk hk') := by
  unfold minorMinus Formalism.GradedWeylDivisibility.lpMinor
  rw [RingHom.map_det, ← Matrix.det_permute]
  refine congrArg Matrix.det (Matrix.ext fun α β => ?_)
  have hα := α.isLt
  have hβ := β.isLt
  simp [psiM, embedding₂, varF, RingHom.mapMatrix_apply, Fin.revPerm_apply]
  split_ifs with h
  · first
      | rfl
      | (congr 1
         refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> (try simp [Fin.val_rev]) <;> omega)
      | (simp [Fin.val_rev]; omega)
  · exact absurd ⟨by omega, by omega⟩ h



end Spec

section Asm

variable {D : D7} {m n : ℕ}




theorem psiM_mem (τ : D.what₂.Tau) (P : ℕ) {Q : ℕ} (hm : P + Q ≤ m) (hn : Q ≤ n)
    (x : MvPolynomial (Fin Q × Fin Q) ℚ) :
    psiM τ P hm hn x ∈ supported ℂ {v : FVar D m n | v.1 = τ ∧ P ≤ (v.2.1 : ℕ)} := by
  show rename (embedding₂ τ P hm hn) (map (algebraMap ℚ ℂ) x) ∈ _
  refine MvPolynomial.supported_mono ?_ (rename_mem_supported (embedding₂ τ P hm hn) _)
  rintro _ ⟨v, rfl⟩
  simp [embedding₂]



end Asm


end Formalism.IndefR.Fock.DeltaPf

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Fock.Sk

namespace Formalism.IndefR.Fock.Final

theorem ccrTheta_of_drho {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : CCRTheta D :=
  Formalism.IndefR.Fock.CCR.ccrTheta_of Formalism.IndefR.Fock.Alg.unitBracket hT hL hC

theorem fockNormO_of_drho {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : FockNormO D :=
  Formalism.IndefR.Fock.Norm.fockNormO_of (ccrTheta_of_drho hT hL hC) Formalism.IndefR.Fock.Alg.fockNormAbs
    (Formalism.IndefR.Fock.Skew.dRhoSkew_of D hT) (Formalism.IndefR.Fock.Skew.thetaIntO D) hT

theorem fockNormO (D : D7) : FockNormO D :=
  fockNormO_of_drho (Formalism.IndefR.Fock.DRho.thetaDRho D) (Formalism.IndefR.Fock.DRho.dRhoLin D) (Formalism.IndefR.Fock.DRho.dRhoComm D)

open Formalism.IndefR.Datum in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem fockNormO_lines (D : D7) :
    ∀ (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) sS sT BS BT
      (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (Formalism.L2.Theta.ratL T S) μ 𝓕 →
      ∀ f : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T f →
        (∀ τ, Formalism.IndefR.Datum.IsFockVacAt (Formalism.IndefR.Datum.heisO ψ S T) θ τ
          (Formalism.IndefR.Datum.cplxO (sS τ) (sT τ)) f) →
        ∀ P Q : MvPolynomial (Formalism.IndefR.Datum.FVar D T.rank S.rank) ℂ,
          ∫ w in 𝓕, Formalism.IndefR.Datum.pureTensorO ψ θ S T sS sT BS BT f P w *
              starRingEnd ℂ (Formalism.IndefR.Datum.pureTensorO ψ θ S T sS sT BS BT f Q w) ∂μ =
            Formalism.REAL.fockF P Q * ∫ w in 𝓕, f w * starRingEnd ℂ (f w) ∂μ :=
  fockNormO D (Formalism.IndefR.Eqv.lineAtExists_holds D)

end Formalism.IndefR.Fock.Final

end
end
