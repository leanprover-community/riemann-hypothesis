import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SegDefs
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

def vG {σ : Type} (F : MvPolynomial σ K) : WithTop ℚ := F.support.inf fun α => v (F.coeff α)

variable {v}
variable {σ τ : Type}

theorem le_vG_iff (F : MvPolynomial σ K) (n : WithTop ℚ) :
    n ≤ vG v F ↔ ∀ α, n ≤ v (F.coeff α) := by
  unfold vG
  rw [Finset.le_inf_iff]
  constructor
  · intro h α
    by_cases hα : α ∈ F.support
    · exact h α hα
    · rw [notMem_support_iff.mp hα, AddValuation.map_zero]; exact le_top
  · intro h α _; exact h α

theorem vG_le_coeff (F : MvPolynomial σ K) (α : σ →₀ ℕ) : vG v F ≤ v (F.coeff α) :=
  (le_vG_iff F _).mp le_rfl α

theorem integral_iff (F : MvPolynomial σ K) : Integral v F ↔ 0 ≤ vG v F :=
  (le_vG_iff F 0).symm

theorem vG_zero : vG v (0 : MvPolynomial σ K) = ⊤ := by
  simp [vG]

theorem vG_one : vG v (1 : MvPolynomial σ K) = 0 := by
  classical
  apply le_antisymm
  · have h := vG_le_coeff (v := v) (1 : MvPolynomial σ K) 0
    simpa using h
  · rw [le_vG_iff]
    intro α
    rw [coeff_one]
    split_ifs
    · simp
    · simp

theorem exists_coeff_eq_vG (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ α ∈ F.support, v (F.coeff α) = vG v F := by
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hF (support_eq_empty.mp h)
  obtain ⟨α, hα, h⟩ := Finset.exists_mem_eq_inf F.support hne fun α => v (F.coeff α)
  exact ⟨α, hα, h.symm⟩

theorem vG_ne_top (F : MvPolynomial σ K) (hF : F ≠ 0) : vG v F ≠ ⊤ := by
  obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
  rw [← h]
  intro ht
  exact (mem_support_iff.mp hα) ((AddValuation.top_iff v).mp ht)

theorem vG_add_vG_le_vG_mul (F G : MvPolynomial σ K) : vG v F + vG v G ≤ vG v (F * G) := by
  classical
  rw [le_vG_iff]
  intro γ
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_le_add (vG_le_coeff F _) (vG_le_coeff G _)

theorem exists_monomialOrder (σ : Type) : Nonempty (MonomialOrder.{0, 0} σ) := by
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT σ
  let _ : LinearOrder σ := @OrderDual.instLinearOrder σ lo
  have : WellFoundedGT σ := ⟨wf.wf⟩
  exact ⟨MonomialOrder.lex⟩

theorem vG_mul (F G : MvPolynomial σ K) : vG v (F * G) = vG v F + vG v G := by
  classical
  by_cases hF : F = 0
  · simp [hF, vG_zero]
  by_cases hG : G = 0
  · simp [hG, vG_zero]
  refine le_antisymm ?_ (vG_add_vG_le_vG_mul F G)
  obtain ⟨m⟩ := exists_monomialOrder σ
  have haT := vG_ne_top (v := v) F hF
  have hbT := vG_ne_top (v := v) G hG
  set SF := F.support.filter fun α => v (F.coeff α) = vG v F with hSF
  set SG := G.support.filter fun α => v (G.coeff α) = vG v G with hSG
  have hSFne : SF.Nonempty := by
    obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
    exact ⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩
  have hSGne : SG.Nonempty := by
    obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) G hG
    exact ⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩
  obtain ⟨α0, hα0, hαmin⟩ := Finset.exists_min_image SF m.toSyn hSFne
  obtain ⟨β0, hβ0, hβmin⟩ := Finset.exists_min_image SG m.toSyn hSGne
  have hα0v : v (F.coeff α0) = vG v F := (Finset.mem_filter.mp hα0).2
  have hβ0v : v (G.coeff β0) = vG v G := (Finset.mem_filter.mp hβ0).2
  have hmem : (α0, β0) ∈ antidiagonal (α0 + β0) := by simp
  have hrest : vG v F + vG v G <
      v (∑ x ∈ (antidiagonal (α0 + β0)).erase (α0, β0), F.coeff x.1 * G.coeff x.2) := by
    apply AddValuation.map_lt_sum
    · exact WithTop.add_ne_top.mpr ⟨haT, hbT⟩
    intro x hx
    obtain ⟨hxne, hxa⟩ := Finset.mem_erase.mp hx
    have hsum : x.1 + x.2 = α0 + β0 := by simpa using hxa
    rw [AddValuation.map_mul]
    rcases lt_or_eq_of_le (vG_le_coeff (v := v) F x.1) with h1 | h1
    · exact WithTop.add_lt_add_of_lt_of_le hbT h1 (vG_le_coeff G x.2)
    rcases lt_or_eq_of_le (vG_le_coeff (v := v) G x.2) with h2 | h2
    · exact WithTop.add_lt_add_of_le_of_lt haT (vG_le_coeff F x.1) h2
    exfalso
    have hx1 : x.1 ∈ SF := by
      refine Finset.mem_filter.mpr ⟨?_, h1.symm⟩
      rw [mem_support_iff]; intro h0
      rw [h0, AddValuation.map_zero] at h1; exact haT h1
    have hx2 : x.2 ∈ SG := by
      refine Finset.mem_filter.mpr ⟨?_, h2.symm⟩
      rw [mem_support_iff]; intro h0
      rw [h0, AddValuation.map_zero] at h2; exact hbT h2
    have l1 := hαmin x.1 hx1
    have l2 := hβmin x.2 hx2
    have hs : m.toSyn x.1 + m.toSyn x.2 = m.toSyn α0 + m.toSyn β0 := by
      rw [← map_add, ← map_add, hsum]
    have e1 : m.toSyn x.1 = m.toSyn α0 := by
      rcases lt_or_eq_of_le l1 with h | h
      · exact absurd hs (ne_of_gt (add_lt_add_of_lt_of_le h l2))
      · exact h.symm
    have e2 : m.toSyn x.2 = m.toSyn β0 := by
      rw [e1] at hs; exact add_left_cancel hs
    exact hxne (Prod.ext (m.toSyn.injective e1) (m.toSyn.injective e2))
  have hc : v ((F * G).coeff (α0 + β0)) = vG v F + vG v G := by
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have h0 : v (F.coeff α0 * G.coeff β0) = vG v F + vG v G := by
      rw [AddValuation.map_mul, hα0v, hβ0v]
    rw [← h0] at hrest ⊢
    exact AddValuation.map_add_eq_of_lt_left v hrest
  rw [← hc]
  exact vG_le_coeff _ _

theorem vG_prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    vG v (∏ k ∈ s, f k) = ∑ k ∈ s, vG v (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vG_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, vG_mul, ih]

theorem vG_rename (f : σ → τ) (hf : Function.Injective f) (F : MvPolynomial σ K) :
    vG v (rename f F) = vG v F := by
  classical
  apply le_antisymm
  · rw [le_vG_iff]
    intro α
    rw [← coeff_rename_mapDomain f hf F α]
    exact vG_le_coeff _ _
  · rw [le_vG_iff]
    intro β
    by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
    · obtain ⟨u, rfl⟩ := h
      rw [coeff_rename_mapDomain f hf]
      exact vG_le_coeff _ _
    · rw [coeff_rename_eq_zero f F β (fun u hu => absurd ⟨u, hu⟩ h), AddValuation.map_zero]
      exact le_top

theorem integral_prod_rename {ι : Type} [Fintype ι] (col : ι → MvPolynomial σ K) (f : ι → σ → τ)
    (hf : ∀ k, Function.Injective (f k)) (h : Integral v (∏ k, col k)) :
    Integral v (∏ k, rename (f k) (col k)) := by
  rw [integral_iff] at h ⊢
  rw [vG_prod] at h ⊢
  simpa only [vG_rename _ (hf _)] using h

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

section General

variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}

theorem integral_zero' : Integral v (0 : MvPolynomial σ K) := by
  unfold Integral
  intro α
  simp

theorem integral_add' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F + G) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_add]
  exact le_trans (le_min (hF α) (hG α)) (v.map_add _ _)

theorem integral_sum' {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ K)
    (h : ∀ k ∈ s, Integral v (f k)) : Integral v (∑ k ∈ s, f k) := by
  exact Finset.sum_induction f (fun F => Integral v F) (fun _ _ hF hG => integral_add' hF hG)
    integral_zero' h

theorem integral_smul' {a : K} {F : MvPolynomial σ K} (ha : 0 ≤ v a) (hF : Integral v F) :
    Integral v (a • F) := by
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact add_nonneg ha (hF α)

theorem integral_mul' {F G : MvPolynomial σ K} (hF : Integral v F) (hG : Integral v G) :
    Integral v (F * G) := by
  classical
  unfold Integral at *
  intro α
  rw [MvPolynomial.coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_nonneg (hF _) (hG _)

theorem integral_monomial' (α : σ →₀ ℕ) {c : K} (hc : 0 ≤ v c) : Integral v (monomial α c) := by
  classical
  unfold Integral
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hc
  · simp

end General

section Deg

variable {K : Type} [Field K] {L L' : Type} {r : ℕ}

theorem ldeg_mapDomain [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L') (β : L × Fin r →₀ ℕ)
    (i' : L') :
    ldeg (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) i' =
      ∑ l, if f l = i' then ldeg β l else 0 := by
  classical
  have key : ∀ a : Fin r, (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) (i', a) =
      ∑ l, if f l = i' then β (l, a) else 0 := by
    intro a
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : f l = i'
    · simp [Finsupp.single_apply, hl]
    · simp [Finsupp.single_apply, hl]
  simp only [ldeg, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs <;> simp

theorem HomD_prod {κ : Type} (s : Finset κ) (d : κ → L → ℕ) (f : κ → MvPolynomial (L × Fin r) K)
    (h : ∀ k ∈ s, HomD (d k) (f k)) : HomD (fun i => ∑ k ∈ s, d k i) (∏ k ∈ s, f k) := by
  classical
  have hadd : ∀ (β γ : L × Fin r →₀ ℕ) (i : L), ldeg (β + γ) i = ldeg β i + ldeg γ i := by
    intro β γ i
    simp [ldeg, Finset.sum_add_distrib]
  have hmul : ∀ (d₁ d₂ : L → ℕ) (F G : MvPolynomial (L × Fin r) K), HomD d₁ F → HomD d₂ G →
      HomD (fun i => d₁ i + d₂ i) (F * G) := by
    intro d₁ d₂ F G hF hG β hβ i
    obtain ⟨β₁, h₁, β₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul F G hβ)
    rw [hadd, hF β₁ h₁ i, hG β₂ h₂ i]
  induction s using Finset.induction_on with
  | empty =>
    intro β hβ i
    simp only [Finset.prod_empty, MvPolynomial.support_one, Finset.mem_singleton] at hβ
    subst hβ
    simp [ldeg]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : (fun i => ∑ k ∈ insert a s, d k i) = fun i => d a i + ∑ k ∈ s, d k i := by
      funext i
      rw [Finset.sum_insert ha]
    rw [e]
    exact hmul _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem HomD_rename [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L')
    (hf : Function.Injective f) (d : L → ℕ) (G : MvPolynomial (L × Fin r) K) (hG : HomD d G) :
    HomD (fun i' => ∑ l, if f l = i' then d l else 0) (rename (Prod.map f (id : Fin r → Fin r)) G) := by
  classical
  intro β hβ i'
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) := by
    rintro ⟨a, b⟩ ⟨c, e⟩ hac
    simp only [Prod.map, id, Prod.mk.injEq] at hac
    exact Prod.ext (hf hac.1) hac.2
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hβ
  obtain ⟨β₀, h₀, rfl⟩ := hβ
  rw [ldeg_mapDomain]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hG β₀ h₀ l]

theorem valS_prod_le [DecidableEq L] (sg : L → Bool) (S : Finset L) {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (L × Fin r) K) :
    ∑ k ∈ s, valS sg S (f k) ≤ valS sg S (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    simp [valS, lord, MvPolynomial.support_one]
    intro b hb a ha
    rw [MvPolynomial.coeff_one] at hb ha
    split_ifs at hb ha with hb0
    · rw [AddMonoidAlgebra.one_def] at ha
      unfold AddMonoidAlgebra.single at ha
      simp at ha
      rw [Finsupp.single_apply] at ha
      split_ifs at ha with ha0
      · subst ha0
        simp
      · exact absurd rfl ha
    · exact absurd rfl hb
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (add_le_add le_rfl ih).trans (by apply valS_mul_le)

end Deg

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

theorem mem_initSet (N i : ℕ) (k : Fin N) : k ∈ initSet N i ↔ k.val < i := by
  simp [initSet]

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def nB : ℕ := (D.LLj j).card

def eB (a : Fin (D.nB j)) : D.Lb := ((D.LLj j).equivFin.symm a).1

theorem seg_eB (a : Fin (D.nB j)) : D.seg (D.eB j a) = j := by
  unfold eB
  have h : ((D.LLj j).equivFin.symm a).1 ∈ D.LLj j := ((D.LLj j).equivFin.symm a).2
  unfold LLj at h
  exact (Finset.mem_filter.1 h).2

theorem eB_inj : Function.Injective (D.eB j) := by
  intro a b h
  unfold eB at h
  exact (D.LLj j).equivFin.symm.injective (Subtype.ext h)

theorem eB_surj (b : D.Lb) (hb : D.seg b = j) : ∃ a, D.eB j a = b := by
  refine ⟨(D.LLj j).equivFin ⟨b, by simp [LLj, hb]⟩, ?_⟩
  simp [eB]

theorem dLL_eq_sum : D.dLL j = ∑ a, D.dB (D.eB j a) := by
  unfold dLL
  rw [← Finset.sum_coe_sort (D.LLj j)]
  exact (Equiv.sum_comp (D.LLj j).equivFin.symm (fun x => D.dB x.1)).symm

def eA : Fin (D.nB j + D.r) → D.OL :=
  Fin.addCases (motive := fun _ => D.OL) (fun a => Sum.inl (D.eB j a)) (fun m => Sum.inr (j, Fin.rev m))

def e0 : Fin (D.nB j + D.r) → D.ML :=
  Fin.addCases (motive := fun _ => D.ML) (fun a => D.mb (D.eB j a)) (fun m => D.mlab (j, Fin.rev m))

def e1 : Fin (D.nB j + D.r) → D.ML :=
  Fin.addCases (motive := fun _ => D.ML) (fun a => D.mb (D.eB j a))
    (fun m => if (Fin.rev m).val = 0 then D.mlab (j, Fin.rev m) else D.mtp (j, Fin.rev m))

@[simp] theorem eA_castAdd (a : Fin (D.nB j)) : D.eA j (Fin.castAdd D.r a) = Sum.inl (D.eB j a) := by
  simp [eA]
@[simp] theorem eA_natAdd (m : Fin D.r) : D.eA j (Fin.natAdd (D.nB j) m) = Sum.inr (j, Fin.rev m) := by
  simp [eA]
@[simp] theorem first_embedding_castAdd (a : Fin (D.nB j)) : D.e0 j (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  simp [e0]
@[simp] theorem first_embedding_natAdd (m : Fin D.r) : D.e0 j (Fin.natAdd (D.nB j) m) = D.mlab (j, Fin.rev m) := by
  simp [e0]
@[simp] theorem second_embedding_castAdd (a : Fin (D.nB j)) : D.e1 j (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  simp [e1]
@[simp] theorem second_embedding_natAdd (m : Fin D.r) : D.e1 j (Fin.natAdd (D.nB j) m) =
    if (Fin.rev m).val = 0 then D.mlab (j, Fin.rev m) else D.mtp (j, Fin.rev m) := by
  simp [e1]

theorem index_embedding_injective : Function.Injective (D.e0 j) := by
  intro x y h
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left b =>
      simp only [first_embedding_castAdd, mb, Sum.inl.injEq] at h
      rw [D.eB_inj j h]
    | right m => simp [mb, mlab] at h
  | right m =>
    induction y using Fin.addCases with
    | left b => simp [mb, mlab] at h
    | right m' =>
      simp only [first_embedding_natAdd, mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and, Fin.rev_inj] at h
      rw [h]

theorem second_embedding_injective : Function.Injective (D.e1 j) := by
  intro x y h
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left b =>
      simp only [second_embedding_castAdd, mb, Sum.inl.injEq] at h
      rw [D.eB_inj j h]
    | right m =>
      simp only [second_embedding_castAdd, second_embedding_natAdd] at h
      split_ifs at h <;> simp [mb, mlab, mtp] at h
  | right m =>
    induction y using Fin.addCases with
    | left b =>
      simp only [second_embedding_castAdd, second_embedding_natAdd] at h
      split_ifs at h <;> simp [mb, mlab, mtp] at h
    | right m' =>
      simp only [second_embedding_natAdd] at h
      split_ifs at h <;> simp_all [mlab, mtp]

theorem second_embedding_mark_eq_first (k : Fin (D.nB j + D.r)) : D.msg (D.e1 j k) = D.msg (D.e0 j k) := by
  induction k using Fin.addCases with
  | left a => simp
  | right m =>
    simp only [second_embedding_natAdd, first_embedding_natAdd]
    split_ifs <;> simp [msg, mlab, mtp]

theorem range_first_embedding (i : D.ML) : (∃ k, D.e0 j k = i) ↔
    (∃ b, D.seg b = j ∧ i = D.mb b) ∨ (∃ m, i = D.mlab (j, m)) := by
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left a => exact Or.inl ⟨D.eB j a, D.seg_eB j a, by simp⟩
    | right m => exact Or.inr ⟨Fin.rev m, by simp⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m, rfl⟩)
    · obtain ⟨a, rfl⟩ := D.eB_surj j b hb
      exact ⟨Fin.castAdd D.r a, by simp⟩
    · exact ⟨Fin.natAdd (D.nB j) (Fin.rev m), by simp⟩

theorem segment_letter_first_embedding (k : Fin (D.nB j + D.r)) : D.SegL j (D.e0 j k) := by
  rcases (D.range_first_embedding j _).1 ⟨k, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem segment_letter_second_embedding (k : Fin (D.nB j + D.r)) : D.SegL j (D.e1 j k) := by
  induction k using Fin.addCases with
  | left a => exact Or.inl ⟨D.eB j a, D.seg_eB j a, by simp⟩
  | right m =>
    rw [second_embedding_natAdd]
    split_ifs
    · exact Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)
    · exact Or.inr (Or.inr ⟨Fin.rev m, rfl⟩)

def stg (m : Fin D.r) : ℕ := D.nB j + (D.r - 1 - m.val)

theorem TL_preimage (m : Fin D.r) :
    (D.TLset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn = initSet (D.nB j + D.r) (D.stg j m) := by
  ext k
  simp only [Finset.mem_preimage, mem_initSet]
  induction k using Fin.addCases with
  | left a =>
    have h1 : D.e0 j (Fin.castAdd D.r a) ∈ D.TLset j m := by
      rw [first_embedding_castAdd]
      unfold TLset
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [LLj, seg_eB]))
    have h2 : (Fin.castAdd D.r a).val < D.stg j m := by
      simp only [Fin.coe_castAdd, stg]
      have := a.2
      omega
    exact iff_of_true h1 h2
  | right m' =>
    rw [first_embedding_natAdd]
    have hm := m.2
    have hm' := m'.2
    simp only [TLset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
    rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
    omega

theorem YP_preimage1 (m : Fin D.r) :
    (D.YPset j m).preimage (D.e1 j) (D.second_embedding_injective j).injOn = initSet (D.nB j + D.r) (D.stg j m) := by
  ext k
  simp only [Finset.mem_preimage, mem_initSet]
  induction k using Fin.addCases with
  | left a =>
    have h1 : D.e1 j (Fin.castAdd D.r a) ∈ D.YPset j m := by
      rw [second_embedding_castAdd]
      unfold YPset
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [LLj, seg_eB]))
    have h2 : (Fin.castAdd D.r a).val < D.stg j m := by
      simp only [Fin.coe_castAdd, stg]
      have := a.2
      omega
    exact iff_of_true h1 h2
  | right m' =>
    rw [second_embedding_natAdd]
    have hm := m.2
    have hm' := m'.2
    split_ifs with h0
    · simp only [YPset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
      rw [Fin.val_rev] at h0
      constructor
      · intro h
        exact h.elim
      · intro h
        omega
    · simp only [YPset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mb, mlab, mtp,
      reduceCtorEq, and_false, exists_false, false_or, or_false, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq,
      exists_eq_right, Fin.coe_natAdd, stg]
      rw [Fin.val_rev] at h0
      rw [Fin.lt_iff_val_lt_val, Fin.val_rev]
      omega

theorem YP_preimage0 (m : Fin D.r) (k : Fin (D.nB j + D.r))
    (hk : k ∈ (D.YPset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn) : k.val < D.nB j := by
  rw [Finset.mem_preimage] at hk
  induction k using Fin.addCases with
  | left a => simp
  | right m' =>
    rw [first_embedding_natAdd] at hk
    simp [YPset, mb, mlab, mtp] at hk

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def Marked (o : Finset (Fin (D.nB j + D.r))) : Prop := ∃ l ∈ o, l.val < D.nB j

open Classical in

def fk (o : Finset (Fin (D.nB j + D.r))) : Fin (D.nB j + D.r) → D.ML :=
  if D.Marked j o then D.e1 j else D.e0 j

theorem fk_inj (o : Finset (Fin (D.nB j + D.r))) : Function.Injective (D.fk j o) := by
  unfold fk; split_ifs
  · exact D.second_embedding_injective j
  · exact D.index_embedding_injective j

theorem segL_fk (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) :
    D.SegL j (D.fk j o l) := by
  unfold fk; split_ifs
  · exact D.segment_letter_second_embedding j l
  · exact D.segment_letter_first_embedding j l

theorem fk_castAdd (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.fk j o (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  unfold fk; split_ifs <;> simp

def cnt (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : ℕ :=
  ∑ l, if D.fk j o l = i then (if l ∈ o then 1 else 0) else 0

theorem cnt_eq (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (l0 : Fin (D.nB j + D.r))
    (h : D.fk j o l0 = i) : D.cnt j o i = if l0 ∈ o then 1 else 0 := by
  unfold cnt
  rw [Finset.sum_eq_single l0]
  · rw [if_pos h]
  · intro l _ hl
    rw [if_neg]
    intro h2
    exact hl (D.fk_inj j o (h2.trans h.symm))
  · intro h2; exact absurd (Finset.mem_univ _) h2

theorem cnt_zero (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (h : ∀ l, D.fk j o l ≠ i) :
    D.cnt j o i = 0 := by
  unfold cnt
  exact Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem cnt_le_one (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : D.cnt j o i ≤ 1 := by
  by_cases h : ∃ l, D.fk j o l = i
  · obtain ⟨l0, h0⟩ := h
    rw [D.cnt_eq j o i l0 h0]
    split_ifs <;> simp
  · push_neg at h
    rw [D.cnt_zero j o i h]; exact Nat.zero_le _

theorem first_embedding_ne_tangent (l : Fin (D.nB j + D.r)) (t : D.Tau) : D.e0 j l ≠ D.mtp t := by
  refine Fin.addCases (fun a => ?_) (fun m => ?_) l <;> simp [mb, mlab, mtp]

theorem second_embedding_tangent_index (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mtp (j, m)) :
    m.val ≠ 0 ∧ l = Fin.natAdd (D.nB j) (Fin.rev m) := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mtp]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · simp [mlab, mtp]
    · intro h
      simp only [mtp, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨h0, by rw [Fin.rev_rev]⟩

theorem second_embedding_label_index_zero (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mlab (j, m)) :
    m.val = 0 := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mlab]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · intro h
      simp only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact h0
    · simp [mlab, mtp]

theorem cnt_mb (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.cnt j o (D.mb (D.eB j a)) = if Fin.castAdd D.r a ∈ o then 1 else 0 :=
  D.cnt_eq j o _ _ (D.fk_castAdd j o a)

theorem cnt_lab_add_tp (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mlab (j, m)) + D.cnt j o (D.mtp (j, m)) =
      if Fin.natAdd (D.nB j) (Fin.rev m) ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · have hf : D.fk j o = D.e1 j := by unfold fk; rw [if_pos hM]
    by_cases h0 : m.val = 0
    · rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_pos h0]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact (D.second_embedding_tangent_index j l m hl).1 h0), add_zero]
    · rw [D.cnt_eq j o (D.mtp (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_neg h0]),
        D.cnt_zero j o (D.mlab (j, m)) (by
          intro l hl; rw [hf] at hl; exact h0 (D.second_embedding_label_index_zero j l m hl)), zero_add]
  · have hf : D.fk j o = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, first_embedding_natAdd, Fin.rev_rev]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact D.first_embedding_ne_tangent j l _ hl), add_zero]

theorem cnt_tp_zero (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) (h0 : m.val = 0) :
    D.cnt j o (D.mtp (j, m)) = 0 := by
  apply D.cnt_zero
  intro l hl
  unfold fk at hl
  split_ifs at hl
  · exact (D.second_embedding_tangent_index j l m hl).1 h0
  · exact D.first_embedding_ne_tangent j l _ hl

theorem cnt_tp_le (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mtp (j, m)) ≤ ∑ a : Fin (D.nB j), if Fin.castAdd D.r a ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · obtain ⟨l, hl, hln⟩ := hM
    refine le_trans (D.cnt_le_one j o _) ?_
    have : (if Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) ∈ o then 1 else 0 : ℕ) = 1 := by
      rw [if_pos]
      have : Fin.castAdd D.r (⟨l.val, hln⟩ : Fin (D.nB j)) = l := by ext; simp
      rw [this]; exact hl
    have h2 := Finset.single_le_sum (f := fun a : Fin (D.nB j) => if Fin.castAdd D.r a ∈ o then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨l.val, hln⟩ : Fin (D.nB j)))
    simp only [this] at h2
    exact h2
  · rw [D.cnt_zero j o]
    · exact Nat.zero_le _
    · intro l hl
      unfold fk at hl
      rw [if_neg hM] at hl
      exact D.first_embedding_ne_tangent j l _ hl

theorem cnt_not_segL (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (hi : ¬ D.SegL j i) :
    D.cnt j o i = 0 := by
  apply D.cnt_zero
  intro l hl
  exact hi (hl ▸ D.segL_fk j o l)

def PsiP {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) : MvPolynomial (D.ML × Fin D.r) K :=
  ∏ k, rename (Prod.map (D.fk j (occ k)) id) (col k)

theorem PsiP_HomD {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0)) :
    HomD (fun i => ∑ k, D.cnt j (occ k) i) (D.PsiP j col occ) := by
  unfold PsiP
  refine HomD_prod _ _ _ fun k _ => ?_
  exact HomD_rename (D.fk j (occ k)) (D.fk_inj j _) _ _ ((mem_PolK_iff _ _).mp (hcol k))

theorem PsiP_support {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (hcount : ∀ i, (univ.filter fun k => i ∈ occ k).card = D.dO (D.eA j i))
    (ξ : D.EM) (hξ : ξ ∈ (D.PsiP j col occ).support) :
    D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := by
  have hd := D.PsiP_HomD j col occ hcol ξ hξ
  have hc : ∀ i, (∑ k, if i ∈ occ k then 1 else 0) = D.dO (D.eA j i) := by
    intro i; rw [← hcount i, Finset.card_filter]
  have hz : ∀ i, ldeg ξ i = 0 → ∀ a, ξ (i, a) = 0 := by
    intro i h a
    unfold ldeg at h
    exact (Finset.sum_eq_zero_iff.mp h) a (Finset.mem_univ a)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨a, rfl⟩ := D.eB_surj j b hb
    rw [hd]
    simp only [cnt_mb]
    rw [hc, eA_castAdd]; rfl
  · intro m
    rw [hd, hd, ← Finset.sum_add_distrib]
    simp only [cnt_lab_add_tp]
    rw [hc, eA_natAdd, Fin.rev_rev]; rfl
  · intro m
    rw [hd]
    refine le_trans (Finset.sum_le_sum fun k _ => D.cnt_tp_le j (occ k) m) ?_
    rw [Finset.sum_comm, dLL_eq_sum]
    refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
    rw [hc, eA_castAdd]; rfl
  · intro m h0
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_tp_zero j _ m h0
  · intro i hi
    apply hz
    rw [hd]
    exact Finset.sum_eq_zero fun k _ => D.cnt_not_segL j _ i hi

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem PsiP_integral {v : AddValuation K (WithTop ℚ)} {nc : ℕ}
    (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) (h : Integral v (∏ k, col k)) :
    Integral v (D.PsiP j col occ) :=
  integral_prod_rename col (fun k => Prod.map (D.fk j (occ k)) id)
    (fun k => (D.fk_inj j (occ k)).prodMap Function.injective_id) h

theorem ph_X_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.fk j o l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold fk ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · split_ifs <;> simp [mb]
  · split_ifs
    · rw [second_embedding_natAdd]
      split_ifs <;> simp [mlab, mtp]
    · simp [mlab]

theorem substitution_X_first_embedding (p : ℕ) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.e0 j l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · simp [mb]
  · simp [mlab]

theorem ph_rename_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r)))
    (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.fk j o) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.fk j o) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.ph_X_fk j p o l a
  exact DFunLike.congr_fun this G

theorem substitution_rename_first_embedding (p : ℕ) (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.e0 j) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.substitution_X_first_embedding j p l a
  exact DFunLike.congr_fun this G

theorem PsiP_ph (p : ℕ) {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) :
    D.ph p (D.PsiP j col occ) = rename (Prod.map (D.eA j) id) (∏ k, col k) := by
  unfold PsiP
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => D.ph_rename_fk j p _ _

theorem card_unmarked (o : Finset (Fin (D.nB j + D.r))) (hM : ¬ D.Marked j o) (m : Fin D.r) :
    (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card < D.r := by
  have h1 : (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card ≤
      (Finset.Ico (D.nB j) (D.stg j m)).card := by
    refine Finset.card_le_card_of_injOn (fun l => l.val) ?_ ?_
    · intro l hl
      have hl' := Finset.mem_filter.mp (Finset.mem_coe.mp hl)
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, hl'.2.1⟩
      by_contra hlt
      exact hM ⟨l, hl'.1, not_le.mp hlt⟩
    · intro x _ y _ h
      exact Fin.ext h
  rw [Nat.card_Ico] at h1
  have := m.2
  have h2 : D.stg j m - D.nB j < D.r := by unfold stg; omega
  omega

theorem PsiP_val {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (cidx : Fin nc → ℤ) (hts : Fin nc → ℕ) (m : Fin D.r)
    (h14 : ∀ k, 1 ≤ cidx k →
      hts k ≤ ((occ k).filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card)
    (h16 : ∀ k, ((colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) (col k)) :
    ((∑ k, colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS D.msg (D.YPset j m) (D.PsiP j col occ) := by
  unfold PsiP
  refine le_trans ?_ (valS_prod_le D.msg (D.YPset j m) Finset.univ _)
  rw [WithTop.coe_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hM : D.Marked j (occ k)
  · have hf : D.fk j (occ k) = D.e1 j := by unfold fk; rw [if_pos hM]
    rw [hf, valS_rename (D.e1 j) (D.second_embedding_injective j), YP_preimage1]
    have : D.msg ∘ D.e1 j = D.msg ∘ D.e0 j := funext fun l => D.second_embedding_mark_eq_first j l
    rw [this]
    exact h16 k
  · have hf : D.fk j (occ k) = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [hf, valS_rename (D.e0 j) (D.index_embedding_injective j)]
    have h0 : (0 : WithTop ℤ) ≤ valS (D.msg ∘ D.e0 j)
        ((D.YPset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn) (col k) := by
      apply valS_nonneg_of_free
      intro α hα i hi a
      have hlt := D.YP_preimage0 j m i hi
      have hi2 : i ∉ occ k := fun h => hM ⟨i, h, hlt⟩
      have hd := (mem_PolK_iff _ _).mp (hcol k) α hα i
      rw [if_neg hi2] at hd
      unfold ldeg at hd
      exact (Finset.sum_eq_zero_iff.mp hd) a (Finset.mem_univ a)
    refine le_trans ?_ h0
    have : colVal (cidx k) (hts k) D.r ≤ 0 := by
      unfold colVal
      by_cases hc : 1 ≤ cidx k
      · have h1 := h14 k hc
        have h2 := D.card_unmarked j (occ k) hM m
        have h3 : ¬ (1 ≤ cidx k ∧ hts k = D.r) := by
          rintro ⟨-, h⟩; omega
        rw [if_neg h3]
        split_ifs <;> simp
      · have h3 : ¬ (1 ≤ cidx k ∧ hts k = D.r) := fun h => hc h.1
        rw [if_neg h3]
        split_ifs <;> simp
    exact_mod_cast this

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

theorem monomial_mem_PolK_sg {K : Type} [Field K] {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ)
    (c : K) (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by
  rw [mem_PolK_iff]
  intro β hβ
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hβ)]
  exact h

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def outSeg (i : D.ML) : Prop := ¬ ∃ k, D.e0 j k = i

instance : DecidablePred (D.outSeg j) := Classical.decPred _
instance : DecidablePred (D.SegL j) := Classical.decPred _

def pullE (ζ : D.EM) : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ :=
  Finsupp.comapDomain (Prod.map (D.e0 j) id) ζ
    (((D.index_embedding_injective j).prodMap (Function.injective_id (α := Fin D.r))).injOn)

theorem pullE_apply (ζ : D.EM) (k : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.pullE j ζ (k, a) = ζ (D.e0 j k, a) := by
  exact Finsupp.comapDomain_apply _ _ _ _

theorem ldeg_pullE (ζ : D.EM) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = ldeg ζ (D.e0 j k) := by
  unfold ldeg
  simp only [pullE_apply]

theorem mapDomain_pullE (ζ : D.EM) :
    Finsupp.mapDomain (Prod.map (D.e0 j) id) (D.pullE j ζ) = eIn (D.outSeg j) ζ := by
  ext ⟨i, a⟩
  by_cases hi : ∃ k, D.e0 j k = i
  · obtain ⟨k, rfl⟩ := hi
    have hinj : Function.Injective (Prod.map (D.e0 j) (id : Fin D.r → Fin D.r)) :=
      (D.index_embedding_injective j).prodMap Function.injective_id
    have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
    exact (Finsupp.mapDomain_apply hinj (D.pullE j ζ) (k, a)).trans
      ((D.pullE_apply j ζ k a).trans ((eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)).symm)
  · have hout : D.outSeg j i := hi
    rw [Finsupp.mapDomain_notin_range]
    · exact ((eIn_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos hout)).symm
    · rintro ⟨⟨k, b⟩, hkb⟩
      exact hi ⟨k, (Prod.mk.inj hkb).1⟩

theorem pullE_congr (ζ ζ' : D.EM) (h : ∀ k a, ζ (D.e0 j k, a) = ζ' (D.e0 j k, a)) :
    D.pullE j ζ = D.pullE j ζ' := by
  ext ⟨k, a⟩
  rw [pullE_apply, pullE_apply]
  exact h k a

theorem pullE_eIn (ζ : D.EM) : D.pullE j (eIn (D.outSeg j) ζ) = D.pullE j ζ := by
  apply D.pullE_congr j
  intro k a
  have hout : ¬ D.outSeg j (D.e0 j k) := fun h => h ⟨k, rfl⟩
  exact (eIn_apply (out := D.outSeg j) ζ (D.e0 j k, a)).trans (if_neg hout)

theorem pullE_deg (ζ : D.EM) (h : D.PreE j ζ) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = D.dO (D.eA j k) := by
  rw [ldeg_pullE]
  cases k using Fin.addCases with
  | left a =>
    have hseg : D.seg (D.eB j a) = j := (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2
    rw [first_embedding_castAdd, h.1 _ hseg]
    simp only [eA, dO, Fin.addCases_left, Sum.elim_inl]
  | right m =>
    rw [first_embedding_natAdd, h.2.1]
    simp only [eA, dO, Fin.addCases_right, Sum.elim_inr]

variable {ι : Type} [Fintype ι]

def TT (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun lam => ∑ b, cc lam b • PP b

def Th (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  lsup fun ζ => monomial (eOut (D.outSeg j) ζ) 1 * D.TT j cc PP (monomial (D.pullE j ζ) 1)

variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem TT_monomial (lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) :
    D.TT j cc PP (monomial lam 1) = ∑ b, cc lam b • PP b := by
  simp only [TT, lsup_monomial, one_smul]

theorem Th_monomial (ζ : D.EM) :
    D.Th j cc PP (monomial ζ 1) =
      monomial (eOut (D.outSeg j) ζ) 1 * ∑ b, cc (D.pullE j ζ) b • PP b := by
  simp only [Th, lsup_monomial, one_smul, TT_monomial]

theorem TT_expand (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (Q : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hQ : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k))) (a : ι → K) (ha : Q = ∑ b, a b • Ψ b) :
    D.TT j cc PP Q = ∑ b, a b • PP b := by
  classical
  have hQsupp : ∀ lam ∈ Q.support, ∀ k, ldeg lam k = D.dO (D.eA j k) := by
    intro lam hlam k
    exact (mem_PolK_iff _ Q).mp hQ lam hlam k
  set c : ι → K := fun b => ∑ lam ∈ Q.support, Q.coeff lam * cc lam b with hc
  have hT : D.TT j cc PP Q = ∑ b, c b • PP b := by
    simp only [TT, lsup_apply, Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
    exact Finset.sum_comm
  have hQ' : Q = ∑ b, c b • Ψ b := by
    calc Q = ∑ lam ∈ Q.support, Q.coeff lam • monomial lam (1 : K) := by
            conv_lhs => rw [Q.as_sum]
            refine Finset.sum_congr rfl fun lam _ => ?_
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      _ = ∑ lam ∈ Q.support, Q.coeff lam • ∑ b, cc lam b • Ψ b := by
            refine Finset.sum_congr rfl fun lam hlam => ?_
            rw [hcc lam (hQsupp lam hlam)]
      _ = ∑ b, c b • Ψ b := by
            simp only [Finset.smul_sum, smul_smul, hc, Finset.sum_smul]
            exact Finset.sum_comm
  have hca : ∀ b, c b = a b := by
    have h0 : ∑ b, (c b - a b) • Ψ b = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hQ', ← ha, sub_self]
    intro b
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 b)
  rw [hT]
  exact Finset.sum_congr rfl fun b _ => by rw [hca b]

theorem Th_integral {v : AddValuation K (WithTop ℚ)}
    (hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b))
    (hPP : ∀ b, Integral v (PP b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    Integral v (D.Th j cc PP (monomial ζ 1)) := by
  rw [Th_monomial]
  apply integral_mul' (integral_monomial' _ (by simp))
  apply integral_sum'
  intro b _
  exact integral_smul' (hccint _ (D.pullE_deg j ζ hζ) b) (hPP b)

theorem Th_ph (p : ℕ) (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (hPP : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    D.ph p (D.Th j cc PP (monomial ζ 1)) = D.ph p (monomial ζ 1) := by
  have hsum : (∑ b, cc (D.pullE j ζ) b • rename (Prod.map (D.eA j) id) (Ψ b)) =
      D.ph p (monomial (eIn (D.outSeg j) ζ) 1) := by
    rw [← D.mapDomain_pullE j ζ, ← MvPolynomial.rename_monomial, substitution_rename_first_embedding,
      hcc _ (D.pullE_deg j ζ hζ), map_sum]
    simp only [map_smul]
  rw [Th_monomial, map_mul, map_sum]
  simp only [map_smul, hPP]
  rw [hsum, ← map_mul, MvPolynomial.monomial_mul, one_mul, eOut_add_eIn]

theorem Th_supp (ζ ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    ∃ b, ∃ ξ ∈ (PP b).support, ζ' = eOut (D.outSeg j) ζ + ξ := by
  rw [Th_monomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial_mul'] at h
  split_ifs at h with hle
  · rw [one_mul, MvPolynomial.coeff_sum] at h
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [MvPolynomial.coeff_smul, smul_eq_mul] at hb
    refine ⟨b, ζ' - eOut (D.outSeg j) ζ, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      exact right_ne_zero_of_mul hb
    · exact (add_tsub_cancel_of_le hle).symm
  · exact absurd rfl h

theorem outSeg_of_not_segL (i : D.ML) (hi : ¬ D.SegL j i) : D.outSeg j i := by
  rintro ⟨k, rfl⟩
  apply hi
  unfold SegL
  cases k using Fin.addCases with
  | left a =>
    rw [first_embedding_castAdd]
    exact Or.inl ⟨D.eB j a, (Finset.mem_filter.mp ((D.LLj j).equivFin.symm a).2).2, rfl⟩
  | right m =>
    rw [first_embedding_natAdd]
    exact Or.inr (Or.inl ⟨Fin.rev m, rfl⟩)

theorem Th_post (hPP : ∀ b, ∀ ξ ∈ (PP b).support, D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (ζ : D.EM) (hζ : D.PreE j ζ) (ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    D.PostE j ζ' ∧ ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a) := by
  obtain ⟨b, ξ, hξ, rfl⟩ := D.Th_supp j cc PP ζ ζ' h
  obtain ⟨hpost, hzero⟩ := hPP b ξ hξ
  have hO : ∀ i, ¬ D.outSeg j i → ∀ a, eOut (D.outSeg j) ζ (i, a) = 0 := by
    intro i hi a
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_neg hi)
  have hmb : ∀ c, D.seg c = j → ¬ D.outSeg j (D.mb c) := by
    intro c hc hout
    obtain ⟨a, rfl⟩ := eB_surj (D := D) (j := j) c hc
    exact hout ⟨Fin.castAdd D.r a, by rw [first_embedding_castAdd]⟩
  have hml : ∀ m, ¬ D.outSeg j (D.mlab (j, m)) := by
    intro m hout
    exact hout ⟨Fin.natAdd (D.nB j) (Fin.rev m), by rw [first_embedding_natAdd, Fin.rev_rev]⟩
  have hmt : ∀ m a, eOut (D.outSeg j) ζ (D.mtp (j, m), a) = 0 := by
    intro m a
    rw [eOut_apply]
    split_ifs
    · exact hζ.2.2 m a
    · rfl
  have hldeg : ∀ i, (∀ a, eOut (D.outSeg j) ζ (i, a) = 0) →
      ldeg (eOut (D.outSeg j) ζ + ξ) i = ldeg ξ i := by
    intro i hi
    simp only [ldeg, Finsupp.add_apply, hi, zero_add]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    rw [hldeg _ (hO _ (hmb c hc))]
    exact hpost.1 c hc
  · intro m
    rw [hldeg _ (hO _ (hml m)), hldeg _ (hmt m)]
    exact hpost.2.1 m
  · intro m
    rw [hldeg _ (hmt m)]
    exact hpost.2.2.1 m
  · intro m hm a
    rw [Finsupp.add_apply, hmt m a, zero_add]
    exact hpost.2.2.2 m hm a
  · intro i hi a
    rw [Finsupp.add_apply, hzero i hi a, add_zero]
    exact (eOut_apply (out := D.outSeg j) ζ (i, a)).trans (if_pos (D.outSeg_of_not_segL j i hi))

theorem Th_away (hPP : ∀ b, ∀ ξ ∈ (PP b).support, ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (S : Finset D.ML) (hS : ∀ i ∈ S, ¬ D.SegL j i) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    valS D.msg S Z ≤ valS D.msg S (D.Th j cc PP Z) := by
  have hIn : ∀ α : D.EM, eIn (fun i => ¬ D.outSeg j i) α = eOut (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hOut : ∀ α : D.EM, eOut (fun i => ¬ D.outSeg j i) α = eIn (D.outSeg j) α := by
    intro α
    ext x
    simp [eIn, eOut, Finsupp.filter_apply]
  have hIn1 : ∀ α : D.EM,
      D.Th j cc PP (monomial (eIn (D.outSeg j) α) 1) = ∑ b, cc (D.pullE j α) b • PP b := by
    intro α
    rw [Th_monomial, eOut_eIn, pullE_eIn, ← C_apply, map_one, one_mul]
  refine valS_outside_linear (fun i => ¬ D.outSeg j i) D.msg S (D.Th j cc PP) ?_ ?_ ?_ Z
  · intro i hi h
    exact h (D.outSeg_of_not_segL j i (hS i hi))
  · intro α
    rw [hIn, hOut, hIn1, Th_monomial]
  · intro α
    rw [hOut, hIn1]
    apply valS_sum_le
    intro b _
    rw [smul_eq_C_mul]
    refine le_trans ?_ (valS_C_mul_le _ _ _ _)
    apply valS_nonneg_of_vecS
    intro ξ hξ i a hne hiS
    exact absurd (hPP b ξ hξ i (hS i hiS) a) hne

end TwistData

end Formalism.MainNotions.PlaneGram
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

theorem coe_untopD_le (x : WithTop ℤ) : ((x.untopD 0 : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n => exact le_rfl

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

def pullL : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K :=
  lsup fun ζ => monomial (D.pullE j ζ) 1

theorem pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.pullL j (coefOut (D.outSeg j) μ Z) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then monomial (D.pullE j α) (Z.coeff α) else 0 := by
  unfold coefOut
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [pullL, lsup_monomial, pullE_eIn, smul_monomial, smul_eq_mul, mul_one]
  · rw [map_zero]

theorem rename_pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    rename (Prod.map (D.e0 j) id) (D.pullL j (coefOut (D.outSeg j) μ Z)) = coefOut (D.outSeg j) μ Z := by
  rw [pullL_coefOut, map_sum]
  unfold coefOut
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [rename_monomial, mapDomain_pullE]
  · rw [map_zero]

variable {ι : Type} [Fintype ι]
  (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem Th_eq (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.Th j cc PP Z = ∑ μ ∈ Z.support.image (eOut (D.outSeg j)),
      monomial μ 1 * D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) := by
  have h : ∀ μ, D.TT j cc PP (D.pullL j (coefOut (D.outSeg j) μ Z)) =
      ∑ α ∈ Z.support, if eOut (D.outSeg j) α = μ then
        Z.coeff α • D.TT j cc PP (monomial (D.pullE j α) 1) else 0 := by
    intro μ
    rw [pullL_coefOut, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs
    · have : monomial (D.pullE j α) (Z.coeff α) = Z.coeff α • monomial (D.pullE j α) (1 : K) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul]
    · rw [map_zero]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm, Th, lsup_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.sum_eq_single (eOut (D.outSeg j) α)]
  · rw [if_pos rfl, mul_smul_comm]
  · intro μ _ hμ
    rw [if_neg (Ne.symm hμ), mul_zero]
  · intro h2
    exact absurd (Finset.mem_image_of_mem _ hα) h2

theorem Th_val [NeZero D.r] {v : AddValuation K (WithTop ℚ)}
    (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (path : ι → Fin (D.nB j + D.r + 1) → Fin D.r → ℤ)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (h7 : ∀ (th : Fin (D.nB j + D.r + 1) → ℤ) (F : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K),
      (F ∈ PolO v D.r (fun k => D.dO (D.eA j k)) ∧ ∀ i : Fin (D.nB j + D.r + 1),
        F ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i)) →
        ∃ c : ι → K, (∀ b, 0 ≤ v (c b)) ∧ (∀ b, c b ≠ 0 → ∀ i, th i ≤ path b i (lastIdx D.r)) ∧
          F = ∑ b, c b • Ψ b)
    (hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : Integral v Z) (hpre : ∀ ζ ∈ Z.support, D.PreE j ζ)
    (m : Fin D.r) (θ : ℝ) (hθ : vala D.msg (D.TLset j m) θ Z) :
    vala D.msg (D.YPset j m) θ (D.Th j cc PP Z) := by
  rw [Th_eq]
  refine vala_sum _ _ fun μ hμ => ?_
  obtain ⟨α0, hα0, rfl⟩ := Finset.mem_image.mp hμ
  refine vala_mul_left_nonneg ?_ ?_
  · apply valS_nonneg_of_free
    intro α hα i hi a
    have h1 := support_monomial_subset hα
    rw [Finset.mem_singleton] at h1
    rw [h1, eOut_apply]
    simp only [YPset, Finset.mem_union, Finset.mem_image] at hi
    rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
    · rw [if_neg]
      exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
    · split_ifs
      · exact (hpre α0 hα0).2.2 m' a
      · rfl
  · set Q := D.pullL j (coefOut (D.outSeg j) (eOut (D.outSeg j) α0) Z) with hQdef
    have hQK : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k)) := by
      rw [hQdef, pullL_coefOut]
      refine Submodule.sum_mem _ fun α hα => ?_
      split_ifs
      · exact monomial_mem_PolK_sg _ _ _ (D.pullE_deg j α (hpre α hα))
      · exact Submodule.zero_mem _
    have hQint : Integral v Q := by
      rw [hQdef, pullL_coefOut]
      refine integral_sum' _ _ fun α _ => ?_
      split_ifs
      · exact integral_monomial' _ (hZ α)
      · exact integral_zero'
    have hout : ∀ i ∈ D.TLset j m, ¬ D.outSeg j i := by
      intro i hi
      simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
      rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inr ⟨m', rfl⟩))
    have hQval : ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤
        valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) Q := by
      have h1 := valS_rename (D.e0 j) (D.index_embedding_injective j) D.msg (D.TLset j m) Q
      rw [hQdef, rename_pullL_coefOut, TL_preimage, ← hQdef] at h1
      rw [← h1]
      exact le_trans ((vala_iff _ _ _ _).mp hθ) (valS_coefOut_le (D.outSeg j) D.msg _ hout _ Z)
    have hlt : D.stg j m < D.nB j + D.r + 1 := by unfold stg; omega
    let i0 : Fin (D.nB j + D.r + 1) := ⟨D.stg j m, hlt⟩
    let th : Fin (D.nB j + D.r + 1) → ℤ := fun i =>
      if i = i0 then ⌈θ⌉ else (valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) Q).untopD 0
    have hmem : ∀ i : Fin (D.nB j + D.r + 1),
        Q ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i) := by
      intro i
      show ((th i : ℤ) : WithTop ℤ) ≤ _
      by_cases hi : i = i0
      · simp only [th, if_pos hi]
        rw [hi]
        exact hQval
      · simp only [th, if_neg hi]
        exact coe_untopD_le _
    obtain ⟨c, -, hc1, hc2⟩ := (h7 th Q) ⟨⟨hQK, hQint⟩, hmem⟩
    rw [D.TT_expand j cc PP Ψ hli hcc Q hQK c hc2]
    refine vala_sum _ _ fun b _ => ?_
    by_cases hcb : c b = 0
    · rw [hcb, zero_smul]; exact vala_zero θ
    · refine vala_smul _ ?_
      rw [vala_iff]
      have h2 := hc1 b hcb i0
      simp only [th, if_true] at h2
      exact le_trans (WithTop.coe_le_coe.mpr h2) (hPPval b m i0 rfl)

end TwistData

theorem segStep_of {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
    (hS : SPAN K v p) : SegStep K v p := by
  classical
  intro hD D hr _ j
  haveI : NeZero D.r := ⟨hr.ne'⟩
  obtain ⟨ι, hι, Ψ, path, ncol, col, cidx, hts, occ, h3, h4, h5, h7, h8, h10, h11,
    h14, h16, h17⟩ := hS hD (D.nB j + D.r) D.r (D.msg ∘ D.e0 j) (fun k => D.dO (D.eA j k))
  have hmon : ∀ lam : Fin (D.nB j + D.r) × Fin D.r →₀ ℕ, (∀ k, ldeg lam k = D.dO (D.eA j k)) →
      monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) := fun lam h =>
    ⟨monomial_mem_PolK_sg _ _ _ h, integral_monomial' _ (by simp)⟩
  let cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K := fun lam =>
    if h : monomial lam (1 : K) ∈ PolO v D.r (fun k => D.dO (D.eA j k)) then (h5 _ h).choose else 0
  have hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) →
      monomial lam (1 : K) = ∑ b, cc lam b • Ψ b := by
    intro lam h
    simp only [cc, dif_pos (hmon lam h)]
    exact (h5 _ (hmon lam h)).choose_spec.2
  have hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b) := by
    intro lam h b
    simp only [cc, dif_pos (hmon lam h)]
    exact (h5 _ (hmon lam h)).choose_spec.1 b
  let PP : ι → MvPolynomial (D.ML × Fin D.r) K := fun b => D.PsiP j (col b) (occ b)
  have hPPint : ∀ b, Integral v (PP b) := fun b =>
    D.PsiP_integral j (col b) (occ b) (h8 b ▸ (h3 b).2)
  have hPPph : ∀ b, D.ph p (PP b) = rename (Prod.map (D.eA j) id) (Ψ b) := by
    intro b
    rw [h8 b]
    exact D.PsiP_ph j p (col b) (occ b)
  have hPPsupp : ∀ b, ∀ ξ ∈ (PP b).support,
      D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := fun b ξ hξ =>
    D.PsiP_support j (col b) (occ b) (h10 b) (h11 b) ξ hξ
  have hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b) := by
    intro b m i0 hi0
    rw [h17 b i0]
    refine D.PsiP_val j (col b) (occ b) (h10 b) (cidx b) (fun k => hts b k i0) m ?_ ?_
    · intro k hk
      have := h14 b k i0 hk
      rwa [hi0] at this
    · intro k
      have := h16 b k i0
      rwa [hi0] at this
  refine ⟨D.Th j cc PP, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ζ hζ => D.Th_integral j cc PP hccint hPPint ζ hζ
  · exact fun ζ hζ => D.Th_ph j cc PP p Ψ hcc hPPph ζ hζ
  · exact fun ζ hζ ζ' hζ' => D.Th_post j cc PP hPPsupp ζ hζ ζ' hζ'
  · exact fun Z hZ hpre m θ _ hθ => D.Th_val j cc PP Ψ path h4 hcc h7 hPPval Z hZ hpre m θ hθ
  · exact fun S hS' Z => D.Th_away j cc PP (fun b ξ hξ => (hPPsupp b ξ hξ).2) S hS' Z

end Formalism.MainNotions.PlaneGram
end
end
