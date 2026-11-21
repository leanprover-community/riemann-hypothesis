import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import BuildAid.ForwardExisting

section
section
set_option autoImplicit false

namespace GlobalTheory.DI

section
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem forms_gen_mem {B : Set K} {L : Set V} {q : ℕ} {b : K} (hb : b ∈ B) (v : Fin q → V)
    (hv : ∀ k, v k ∈ L) : b • ExteriorAlgebra.ιMulti K q v ∈ forms B L q :=
  AddSubgroup.subset_closure ⟨b, hb, v, hv, rfl⟩

theorem forms_le_comap_of_gen {B B' : Set K} {L L' : Set V} {q q' : ℕ}
    (φ : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (h : ∀ b ∈ B, ∀ v : Fin q → V, (∀ k, v k ∈ L) →
      φ (b • ExteriorAlgebra.ιMulti K q v) ∈ forms B' L' q') :
    forms B L q ≤ (forms B' L' q').comap φ := by
  show AddSubgroup.closure _ ≤ _
  rw [AddSubgroup.closure_le]
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact h b hb v hv

theorem ι_mul_ιMulti_eq (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

theorem ιMulti_one_eq (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem forms_mul_smul_mono (A : Subring K) (L : Set V) :
    (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧
    (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q →
      x * y ∈ forms (A : Set K) L (q + 1)) ∧
    (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧
    (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧
    ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := forms_gen_mem (B := (A : Set K)) (L := L) A.one_mem (Fin.elim0 : Fin 0 → V)
      (fun k => k.elim0)
    simpa using h
  · intro q x y hx hy

    have key : ∀ a ∈ (A : Set K), ∀ u : Fin 1 → V, (∀ k, u k ∈ L) →
        a • ExteriorAlgebra.ιMulti K 1 u * y ∈ forms (A : Set K) L (q + 1) := by
      intro a ha u hu
      have := forms_le_comap_of_gen (B := (A : Set K)) (L := L) (B' := (A : Set K)) (L' := L)
        (q := q) (q' := q + 1) (AddMonoidHom.mulLeft (a • ExteriorAlgebra.ιMulti K 1 u)) ?_ hy
      · exact this
      intro b hb w hw
      show a • ExteriorAlgebra.ιMulti K 1 u * (b • ExteriorAlgebra.ιMulti K q w) ∈ _
      rw [smul_mul_smul_comm, ιMulti_one_eq, ι_mul_ιMulti_eq]
      refine forms_gen_mem (A.mul_mem ha hb) _ ?_
      intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hu 0
      · simpa using hw k
    exact forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q + 1)
      (AddMonoidHom.mulRight y) (fun a ha u hu => key a ha u hu) hx
  · intro q c y hc hy
    refine forms_le_comap_of_gen (B' := (A : Set K)) (L' := L) (q' := q)
      (DistribMulAction.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (A.mul_mem hc hb) v hv
  · intro B q c y hy
    refine forms_le_comap_of_gen (B' := (fun b => c * b) '' B) (L' := L) (q' := q)
      (DistribMulAction.toAddMonoidHom _ c) ?_ hy
    intro b hb v hv
    show c • b • ExteriorAlgebra.ιMulti K q v ∈ _
    rw [smul_smul]
    exact forms_gen_mem (B := (fun b => c * b) '' B) (Set.mem_image_of_mem _ hb) v hv
  · intro B B' L' q hB hL
    refine (forms_le_comap_of_gen (B' := B') (L' := L') (q' := q) (AddMonoidHom.id _) ?_)
    intro b hb v hv
    exact forms_gen_mem (hB hb) v (fun k => hL (hv k))

end

end GlobalTheory.DI
end

open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (A : Subring K) (L : Set V), (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧ (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q → x * y ∈ forms (A : Set K) L (q + 1)) ∧ (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧ (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧ ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  atlas_forward_decl GlobalTheory.DI.forms_mul_smul_mono
end

section
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_mem_forms_and_vanish {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {ι : Type} [LinearOrder ι]
    (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι)
    (hf : ∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1)
    (hh : ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) :
    ∀ (vs : List V), (∀ w ∈ vs, w ∈ L) → ∀ t : Finset ι,
      (t ⊆ s → ∀ q, q + t.card = vs.length + 1 → prodL f h vs t ∈ forms (A : Set K) L q) ∧
      (vs.length + 1 < t.card → prodL f h vs t = 0) := by
  obtain ⟨hone, hmul, hsmul, -, -⟩ := GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono A L
  intro vs
  induction vs with
  | nil =>
    intro _ t
    simp only [prodL, List.foldr_nil, oneC, List.length_nil]
    refine ⟨fun _ q hq => ?_, fun ht => ?_⟩
    · split_ifs with h1t
      · have hq0 : q = 0 := by omega
        subst hq0
        exact hone
      · exact zero_mem _
    · rw [if_neg (by omega)]
  | cons w vs ih =>
    intro hvs t
    have hw : w ∈ L := hvs w (List.mem_cons_self ..)
    have hvs' : ∀ u ∈ vs, u ∈ L := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
    have key : prodL f h (w :: vs) t = Lop f h w (prodL f h vs) t := rfl
    rw [key, List.length_cons]
    refine ⟨fun hts q hq => ?_, fun hlt => ?_⟩
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dif_pos ht]
        have hm : t.min' ht ∈ s := hts (t.min'_mem ht)
        refine add_mem ?_ ?_
        · refine zsmul_mem ?_ _
          rcases q with _ | q
          · rw [(ih hvs' t).2 (by omega), mul_zero]
            exact zero_mem _
          · exact hmul q _ _ (hf _ hm w hw) ((ih hvs' t).1 hts q (by omega))
        · split_ifs with h2
          · have hm' : (t.erase (t.min' ht)).min' h2 ∈ s :=
              hts (Finset.mem_of_mem_erase ((t.erase _).min'_mem h2))
            have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
              Finset.card_erase_of_mem (t.min'_mem ht)
            have hpos : 0 < t.card := ht.card_pos
            exact hsmul q _ _ (hh _ hm _ hm' w hw)
              ((ih hvs' _).1 ((Finset.erase_subset _ _).trans hts) q (by omega))
          · exact zero_mem _
      · rw [dif_neg ht]
        exact zero_mem _
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dif_pos ht]
        have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
          Finset.card_erase_of_mem (t.min'_mem ht)
        rw [(ih hvs' t).2 (by omega), mul_zero, smul_zero, zero_add]
        split_ifs with h2
        · rw [(ih hvs' _).2 (by omega), smul_zero]
        · rfl
      · rw [dif_neg ht]

theorem alt_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι),
    (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) →
    ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s →
      ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  intro K _ V _ _ ι _ f h A L s hf hh a v t hv hts q hq
  rw [alt, Finset.sum_apply]
  refine AddSubgroup.sum_mem _ fun σ _ => ?_
  rw [Pi.smul_apply]
  refine zsmul_mem ?_ _
  refine (prodL_mem_forms_and_vanish f h A L s hf hh _ ?_ t).1 hts q (by rw [List.length_ofFn]; exact hq)
  intro w hw
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  exact hv _

end GlobalTheory.DI
end

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.alternating_product_integral : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι), (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s → ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  atlas_forward_decl _root_.GlobalTheory.DI.alt_mem_forms
end
