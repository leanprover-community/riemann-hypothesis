import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory

namespace DerivFaithful

variable {U A ι : Type} [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A]

def wordProd (e : ι → U) (l : List ι) : U := (l.map e).prod

def filt (e : ι → U) (d : ℕ) : Submodule ℂ U :=
  Submodule.span ℂ {u | ∃ l : List ι, l.length ≤ d ∧ wordProd e l = u}

lemma wordProd_cons (e : ι → U) (k : ι) (l : List ι) :
    wordProd e (k :: l) = e k * wordProd e l := by simp [wordProd]

lemma wordProd_append (e : ι → U) (l l' : List ι) :
    wordProd e (l ++ l') = wordProd e l * wordProd e l' := by simp [wordProd, List.prod_append]

lemma wordProd_mem_filt (e : ι → U) (l : List ι) : wordProd e l ∈ filt e l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩

lemma filt_mono (e : ι → U) {d d' : ℕ} (h : d ≤ d') : filt e d ≤ filt e d' := by
  apply Submodule.span_mono
  rintro _ ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

lemma mul_mem_filt (e : ι → U) {i j : ℕ} {x y : U} (hx : x ∈ filt e i) (hy : y ∈ filt e j) :
    x * y ∈ filt e (i + j) := by
  have h : filt e i * filt e j ≤ filt e (i + j) := by
    rw [filt, filt, Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨l, hl, rfl⟩, _, ⟨l', hl', rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨l ++ l', ?_, (wordProd_append e l l')⟩
    simp; omega
  exact h (Submodule.mul_mem_mul hx hy)

lemma span_le_filt_one (e : ι → U) : Submodule.span ℂ (Set.range e) ≤ filt e 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨[k], by simp, by simp [wordProd]⟩

lemma der_pow_mem (D : A →ₗ[ℂ] A) (hD : ∀ x y, D (x * y) = D x * y + x * D y) (I : Ideal A) :
    ∀ m : ℕ, ∀ x ∈ I ^ (m + 1), D x ∈ I ^ m := by
  intro m
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro p hp q hq
      rw [hD]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hp (ih q hq)
    · intro p q hp hq
      rw [map_add]
      exact Ideal.add_mem _ hp hq

lemma word_pow_mem (e : ι → U) (π : U →ₐ[ℂ] Module.End ℂ A)
    (hder : ∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) (I : Ideal A) :
    ∀ (w : List ι) (m : ℕ), ∀ x ∈ I ^ (m + w.length), π (wordProd e w) x ∈ I ^ m := by
  intro w
  induction w with
  | nil => intro m x hx; simpa [wordProd] using hx
  | cons k w ih =>
    intro m x hx
    rw [wordProd_cons, map_mul, Module.End.mul_apply]
    apply der_pow_mem (π (e k)) (hder k) I m
    apply ih (m + 1)
    have : m + (k :: w).length = m + 1 + w.length := by simp; omega
    rw [this] at hx; exact hx

lemma filt_vanish (e : ι → U) (π : U →ₐ[ℂ] Module.End ℂ A)
    (hder : ∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) (χ : A →ₐ[ℂ] ℂ)
    (d : ℕ) : ∀ u ∈ filt e d, ∀ x ∈ (RingHom.ker χ) ^ (d + 1), χ (π u x) = 0 := by
  let S : Submodule ℂ U :=
    { carrier := {u | ∀ x ∈ (RingHom.ker χ) ^ (d + 1), χ (π u x) = 0}
      add_mem' := by
        intro p q hp hq x hx
        simp [hp x hx, hq x hx]
      zero_mem' := by intro x _; simp
      smul_mem' := by
        intro c p hp x hx
        simp [hp x hx] }
  have h : filt e d ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩ x hx
    have hx' : x ∈ (RingHom.ker χ) ^ (1 + l.length) := Ideal.pow_le_pow_right (by omega) hx
    have := word_pow_mem e π hder (RingHom.ker χ) l 1 x hx'
    simpa using this
  intro u hu
  exact h hu

lemma perm_sub_mem (e : ι → U)
    (hcomm : ∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e))
    {l l' : List ι} (h : l.Perm l') :
    ∀ d, l.length ≤ d + 1 → wordProd e l - wordProd e l' ∈ filt e d := by
  induction h with
  | nil => intro d _; simp
  | cons x h ih =>
    rename_i l₁ l₂
    intro d hd
    rw [wordProd_cons, wordProd_cons, ← mul_sub]
    cases d with
    | zero =>
      have h0 : l₁ = [] := by
        cases l₁ with
        | nil => rfl
        | cons _ _ => simp at hd
      subst h0
      have h0' : l₂ = [] := List.nil_perm.mp h
      subst h0'
      simp
    | succ d =>
      have := mul_mem_filt e (span_le_filt_one e (Submodule.subset_span ⟨x, rfl⟩))
        (ih d (by simp at hd; omega))
      rw [add_comm] at this
      exact this
  | swap x y l =>
    intro d hd
    simp only [wordProd_cons]
    rw [← mul_assoc, ← mul_assoc, ← sub_mul]
    have h1 := span_le_filt_one e (hcomm y x)
    exact filt_mono e (by simp at hd; omega) (mul_mem_filt e h1 (wordProd_mem_filt e l))
  | trans h₁ h₂ ih₁ ih₂ =>
    intro d hd
    have a1 := ih₁ d hd
    have a2 := ih₂ d (by rw [← h₁.length_eq]; exact hd)
    have := Submodule.add_mem _ a1 a2
    simpa using this

lemma exists_mem_filt (e : ι → U) (hgen : Algebra.adjoin ℂ (Set.range e) = ⊤) (u : U) :
    ∃ d, u ∈ filt e d := by
  let S : Subalgebra ℂ U :=
    { carrier := {u | ∃ d, u ∈ filt e d}
      mul_mem' := by
        rintro p q ⟨i, hp⟩ ⟨j, hq⟩
        exact ⟨i + j, mul_mem_filt e hp hq⟩
      add_mem' := by
        rintro p q ⟨i, hp⟩ ⟨j, hq⟩
        exact ⟨i + j, Submodule.add_mem _ (filt_mono e (by omega) hp) (filt_mono e (by omega) hq)⟩
      algebraMap_mem' := by
        intro c
        refine ⟨0, ?_⟩
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ c (by simpa [wordProd] using wordProd_mem_filt e []) }
  have h : Algebra.adjoin ℂ (Set.range e) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨k, rfl⟩; exact ⟨1, span_le_filt_one e (Submodule.subset_span ⟨k, rfl⟩)⟩)
  rw [hgen] at h
  exact h Algebra.mem_top

def testProd (a : ι → A) (β : Multiset ι) : A := (β.map a).prod

lemma testProd_mem_pow (χ : A →ₐ[ℂ] ℂ) (a : ι → A) (ha : ∀ k, χ (a k) = 0) (β : Multiset ι) :
    testProd a β ∈ (RingHom.ker χ) ^ (Multiset.card β) := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons b β ih =>
    rw [testProd, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact Ideal.mul_mem_mul (by simpa [RingHom.mem_ker] using ha b) ih

lemma der_testProd [DecidableEq ι] (D : A →ₗ[ℂ] A) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (χ : A →ₐ[ℂ] ℂ) (a : ι → A) (ha : ∀ j, χ (a j) = 0) (k : ι)
    (hδ : ∀ j, χ (D (a j)) = if k = j then 1 else 0) (β : Multiset ι) :
    D (testProd a β) - algebraMap ℂ A (β.count k) * testProd a (β.erase k)
      ∈ (RingHom.ker χ) ^ (Multiset.card β) := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons b β ih =>
    set I := RingHom.ker χ
    set c : ℂ := if k = b then 1 else 0 with hc
    set r := D (a b) - algebraMap ℂ A c with hr
    set s := D (testProd a β) - algebraMap ℂ A (β.count k) * testProd a (β.erase k) with hs
    have hrI : r ∈ I := by simp [I, RingHom.mem_ker, hr, hδ b, c]
    have haI : a b ∈ I := by simpa [I, RingHom.mem_ker] using ha b
    have hxβ := testProd_mem_pow χ a ha β
    have key : D (testProd a (b ::ₘ β)) - algebraMap ℂ A ((b ::ₘ β).count k) * testProd a ((b ::ₘ β).erase k)
        = r * testProd a β + a b * s := by
      have e1 : testProd a (b ::ₘ β) = a b * testProd a β := by simp [testProd]
      rw [e1, hD]
      by_cases hkb : k = b
      · subst hkb
        have hc1 : c = 1 := by simp [c]
        rw [Multiset.count_cons_self, Multiset.erase_cons_head, hr, hs, hc1]
        by_cases hmem : k ∈ β
        · have e2 : testProd a β = a k * testProd a (β.erase k) := by
            conv_lhs => rw [← Multiset.cons_erase hmem]
            simp [testProd]
          rw [e2]; simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
        · rw [Multiset.count_eq_zero.mpr hmem]; simp; ring
      · have hc0 : c = 0 := by simp [c, hkb]
        rw [Multiset.count_cons_of_ne hkb, Multiset.erase_cons_tail _ (Ne.symm hkb), hr, hs, hc0]
        simp [testProd]; ring
    rw [key, Multiset.card_cons, pow_succ']
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hrI hxβ) (Ideal.mul_mem_mul haI ih)

section Pairing

variable [DecidableEq ι] (e : ι → U)
    (hcomm : ∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e))
    (π : U →ₐ[ℂ] Module.End ℂ A)
    (hder : ∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y)
    (χ : A →ₐ[ℂ] ℂ) (a : ι → A) (ha : ∀ k, χ (a k) = 0)
    (hδ : ∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0)
include hcomm hder ha hδ

lemma pair_cons (k : ι) (w : List ι) (β : Multiset ι) (hlen : w.length + 1 = Multiset.card β) :
    χ (π (wordProd e (k :: w)) (testProd a β)) =
      (β.count k : ℂ) * χ (π (wordProd e w) (testProd a (β.erase k))) := by
  have hx : testProd a β ∈ (RingHom.ker χ) ^ (w.length + 1) := hlen ▸ testProd_mem_pow χ a ha β
  have hp : (k :: w).Perm (w ++ [k]) := (List.perm_append_singleton k w).symm
  have h1 := filt_vanish e π hder χ w.length _ (perm_sub_mem e hcomm hp w.length (by simp)) _ hx
  have e1 : wordProd e (k :: w) =
      (wordProd e (k :: w) - wordProd e (w ++ [k])) + wordProd e (w ++ [k]) := by abel
  rw [e1, map_add, LinearMap.add_apply, map_add, h1, zero_add, wordProd_append, map_mul,
    Module.End.mul_apply]
  have hD := der_testProd (π (e k)) (hder k) χ a ha k (fun j => hδ k j) β
  rw [← hlen] at hD
  have e2 : π (wordProd e [k]) (testProd a β) =
      (π (e k) (testProd a β) - algebraMap ℂ A (β.count k) * testProd a (β.erase k)) +
        algebraMap ℂ A (β.count k) * testProd a (β.erase k) := by simp [wordProd]
  rw [e2, map_add, map_add, filt_vanish e π hder χ w.length _ (wordProd_mem_filt e w) _ hD, zero_add,
    ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul]

lemma pair_ne_zero_iff : ∀ (w : List ι) (β : Multiset ι), w.length = Multiset.card β →
    (χ (π (wordProd e w) (testProd a β)) ≠ 0 ↔ (w : Multiset ι) = β) := by
  intro w
  induction w with
  | nil =>
    intro β hβ
    have : β = 0 := Multiset.card_eq_zero.mp hβ.symm
    subst this
    simp [wordProd, testProd]
  | cons k w ih =>
    intro β hβ
    rw [pair_cons e hcomm π hder χ a ha hδ k w β (by simpa using hβ)]
    by_cases hk : k ∈ β
    · have hcard : w.length = Multiset.card (β.erase k) := by
        rw [Multiset.card_erase_of_mem hk, Nat.pred_eq_sub_one]; simp at hβ; omega
      rw [mul_ne_zero_iff, ih _ hcard]
      have hcnt : (β.count k : ℂ) ≠ 0 := by exact_mod_cast (Multiset.count_ne_zero.mpr hk)
      simp only [hcnt, ne_eq, not_false_eq_true, true_and]
      rw [← Multiset.cons_coe]
      constructor
      · intro h; rw [h, Multiset.cons_erase hk]
      · intro h; rw [← h]; simp
    · have hcnt : β.count k = 0 := Multiset.count_eq_zero.mpr hk
      simp only [hcnt, Nat.cast_zero, zero_mul, ne_eq, not_true_eq_false, false_iff]
      intro h; apply hk; rw [← h]; simp

lemma step_down [Fintype ι] (d : ℕ) (u : U)
    (hu : u ∈ filt e (d + 1)) (hz : ∀ x : A, χ (π u x) = 0) : u ∈ filt e d := by
  let W : Sym ι (d + 1) → U := fun s => wordProd e (s : Multiset ι).toList
  let G : Submodule ℂ U := Submodule.span ℂ (Set.range W)
  have hle : filt e (d + 1) ≤ filt e d ⊔ G := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    rcases Nat.lt_or_ge l.length (d + 1) with h | h
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, by omega, rfl⟩)
    · have hl' : l.length = d + 1 := by omega
      let s : Sym ι (d + 1) := ⟨(l : Multiset ι), by simpa using hl'⟩
      have hp : l.Perm (s : Multiset ι).toList := by
        rw [← Multiset.coe_eq_coe, Multiset.coe_toList]; rfl
      have hdiff := perm_sub_mem e hcomm hp d (by omega)
      have e1 : wordProd e l = (wordProd e l - W s) + W s := by abel
      rw [e1]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hdiff)
        (Submodule.mem_sup_right (Submodule.subset_span ⟨s, rfl⟩))
  obtain ⟨v, hv, t, ht, rfl⟩ := Submodule.mem_sup.mp (hle hu)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ht
  have hc : ∀ s0, c s0 = 0 := by
    intro s0
    have hx : testProd a (s0 : Multiset ι) ∈ (RingHom.ker χ) ^ (d + 1) := by
      have := testProd_mem_pow χ a ha (s0 : Multiset ι)
      rwa [show Multiset.card (s0 : Multiset ι) = d + 1 from s0.2] at this
    have h1 := hz (testProd a (s0 : Multiset ι))
    rw [map_add, LinearMap.add_apply, map_add, filt_vanish e π hder χ d v hv _ hx, zero_add] at h1
    rw [map_sum, LinearMap.sum_apply, map_sum] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [Finset.sum_eq_single s0] at h1
    · have hne := (pair_ne_zero_iff e hcomm π hder χ a ha hδ ((s0 : Multiset ι).toList) s0
        (by simp [s0.2])).mpr (by simp)
      exact (mul_eq_zero.mp h1).resolve_right hne
    · intro s _ hs
      have hiff := pair_ne_zero_iff e hcomm π hder χ a ha hδ ((s : Multiset ι).toList) s0
        (by simp [s.2, s0.2])
      have h0 : χ (π (W s) (testProd a s0)) = 0 := by
        by_contra hh
        exact hs (Sym.coe_injective (by simpa using hiff.mp hh))
      rw [h0, mul_zero]
    · simp
  simp [hc, hv]

end Pairing

end DerivFaithful

open DerivFaithful in

theorem faithful_of_derivations_dual_family : ∀ (U A ι : Type) [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι] (e : ι → U), Algebra.adjoin ℂ (Set.range e) = ⊤ → (∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e)) → ∀ (π : U →ₐ[ℂ] Module.End ℂ A), (∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) → ∀ (χ : A →ₐ[ℂ] ℂ) (a : ι → A), (∀ k, χ (a k) = 0) → (∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0) → ∀ u : U, (∀ x : A, χ (π u x) = 0) → u = 0 := by
  intro U A ι _ _ _ _ _ _ e hgen hcomm π hder χ a ha hδ u hu
  obtain ⟨d, hd⟩ := exists_mem_filt e hgen u
  have h0 : u ∈ filt e 0 := by
    induction d with
    | zero => exact hd
    | succ d ih => exact ih (step_down e hcomm π hder χ a ha hδ d u hd hu)
  have hle : filt e 0 ≤ Submodule.span ℂ {(1 : U)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [wordProd]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle h0)
  have := hu 1
  simp at this
  simp [this]

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithful_of_derivations_dualFamily : ∀ (U A ι : Type) [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι] (e : ι → U), Algebra.adjoin ℂ (Set.range e) = ⊤ → (∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e)) → ∀ (π : U →ₐ[ℂ] Module.End ℂ A), (∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) → ∀ (χ : A →ₐ[ℂ] ℂ) (a : ι → A), (∀ k, χ (a k) = 0) → (∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0) → ∀ u : U, (∀ x : A, χ (π u x) = 0) → u = 0 := by
  atlas_forward_decl GlobalTheory.faithful_of_derivations_dual_family
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct ContDiff

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def algEntry (V : HSp D) (τ : D.what₂.Tau) (m j : Fin V.rank) : AlgInf V →ₗ[ℝ] ℂ where
  toFun u := (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ m j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_expEntry (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (τ : D.what₂.Tau) (m j : Fin V.rank) :
    ContDiff ℝ ∞ fun X : LieN V => algEntry V τ m j (NormedSpace.exp (jInf V X)) := by
  haveI : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ (AlgInf V)
  haveI : FiniteDimensional ℝ (LieN V) := FiniteDimensional.of_injective (jInf V) (isLieData R).inj
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : AlgInf V → AlgInf V) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (LinearMap.toContinuousLinearMap (algEntry V τ m j)).contDiff.comp
    (h1.comp (LinearMap.toContinuousLinearMap (jInf V)).contDiff)

theorem realEntries_mul_exp (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (g : GA D V) (X : LieN V) (p : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p =
      ∑ m, infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 m * algEntry V p.1 m p.2.2 (NormedSpace.exp (jInf V X)) := by
  have h2 := (isExpFam_expInf R X).2 p.1
  change infMat D.sp.cm.sig V.gram (θ p.1) (g * expInf θ V X) p.2.1 p.2.2 = _
  rw [R.2.2.2.1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  change infMat D.sp.cm.sig V.gram (θ p.1) (expInf θ V X) m p.2.2 = (NormedSpace.exp (jInf V X) : AlgInf V) p.1 m p.2.2
  rw [exp_algInf, h2]
  rfl

theorem polyFun_mem_smF : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  intro D θ V R P g
  have hc : ∀ p : D.what₂.Tau × Fin V.rank × Fin V.rank,
      ContDiff ℝ ∞ fun X : LieN V => realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p := by
    intro p
    simp only [realEntries_mul_exp θ R]
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expEntry θ R p.1 m p.2.2)
  change ContDiff ℝ ∞ fun X : LieN V => MvPolynomial.eval (realEntries θ V (g * expMap (jInf V) (secInf θ V) X)) P
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p n hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hc n)

end GlobalTheory.CentralOps

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyFun_mem_smooth_vectors : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  first | exact @GlobalTheory.CentralOps.polyFun_mem_smF | exact GlobalTheory.CentralOps.polyFun_mem_smF | (intros; apply GlobalTheory.CentralOps.polyFun_mem_smF <;> assumption)
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct

namespace GlobalTheory.PolyRightDeriv

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem hasDerivAt_eval {σ : Type} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (c : ℝ → σ → ℂ)
    (h : ∀ p, HasDerivAt (fun t => c t p) (MvPolynomial.eval (c 0) (δ (MvPolynomial.X p))) 0) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (c t) P) (MvPolynomial.eval (c 0) (δ P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.derivation_C] using hasDerivAt_const (0 : ℝ) a
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P p hP =>
    have := hP.mul (h p)
    simp only [map_mul, MvPolynomial.eval_X, Derivation.leibniz, smul_eq_mul, map_add]
    exact this.congr_deriv (by ring)

theorem hasDerivAt_entry {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A * NormedSpace.exp (t • X)) i j) ((A * X) i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun B => (A * B) i j
      map_add' := fun B C => by simp [mul_add]
      map_smul' := fun c B => by simp }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  classical
  funext g
  let c : ℝ → D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
    fun t => realEntries θ V (g * expInf θ V (t • atPlace V τ X))
  have hc : ∀ t p, c t p = (infMat D.sp.cm.sig V.gram (θ p.1) g *
      NormedSpace.exp (t • (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) p.2.1 p.2.2 := fun t p => by
    simp only [c, realEntries]
    rw [R.2.2.2.1, (isExpFam_expInf R (t • atPlace V τ X)).2]
    rfl
  have h0 : c 0 = realEntries θ V g := funext fun p => by
    rw [hc, zero_smul, NormedSpace.exp_zero, mul_one]; rfl
  have h := hasDerivAt_eval (matDer τ X.1) c (fun p => by
    simp only [hc]
    convert hasDerivAt_entry (infMat D.sp.cm.sig V.gram (θ p.1) g)
      (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) p.2.1 p.2.2 using 1
    rw [h0, matDer_X]
    obtain ⟨τ', i, j⟩ := p
    by_cases e : τ' = τ
    · subst e
      simp [atPlace, Matrix.mul_apply, realEntries]
    · simp [atPlace, e, Pi.single_eq_of_ne e]) P
  rw [h0] at h
  exact h.deriv

end GlobalTheory.PolyRightDeriv

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V), lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  atlas_forward_decl GlobalTheory.PolyRightDeriv.lieDer_polyFun
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem polyFun_mem (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (P : PolyE V) : polyFun θ V P ∈ SmF θ V := GlobalTheory.T.polyFun_mem_smooth_vectors D θ V R P

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction D θ V R τ X P

open Classical in

theorem aeval_matDer_single {T : Type} {n : ℕ} (τ τ' : T) (a b c d : Fin n) :
    MvPolynomial.aeval (fun p : T × Fin n × Fin n => if p.2.1 = p.2.2 then (1 : ℂ) else 0)
      (matDer τ (Matrix.single a b (1 : ℂ)) (MvPolynomial.X (τ', c, d) -
        MvPolynomial.C (if c = d then (1 : ℂ) else 0))) = if (τ, a, b) = (τ', c, d) then 1 else 0 := by
  rw [map_sub, MvPolynomial.derivation_C, sub_zero, matDer_X]
  by_cases h : τ' = τ
  · subst h
    simp only [if_true, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.single_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Prod.mk.injEq, true_and]
  · simp only [h, if_false, map_zero]
    rw [if_neg]; intro h'; exact h (congrArg Prod.fst h').symm

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem polyFun_add (P Q : PolyE V) : polyFun θ V (P + Q) = polyFun θ V P + polyFun θ V Q := by
  funext g; simp [polyFun]

theorem polyFun_smul (c : ℂ) (P : PolyE V) : polyFun θ V (c • P) = c • polyFun θ V P := by
  funext g; simp [polyFun, MvPolynomial.smul_eval]

open Classical in
theorem envRepAll_ι_of (R : RealPoints θ V) (τ : D.what₂.Tau) (y : ℂ ⊗[ℝ] LieAt V τ) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ y)) =
      envRep R τ (UniversalEnvelopingAlgebra.ι ℂ y) := by
  rw [← envIncl_ι, envRepAll_envIncl]

theorem envRepAll_polyFun (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V) (P : PolyE V) :
    (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P) := by
  classical
  let S : Subalgebra ℂ (GlobalTheory.AutFinLit.Env V) :=
    { carrier := {u | ∀ P, (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P)}
      mul_mem' := fun {u v} hu hv P => by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← hu]
        congr 2
        exact Subtype.ext (hv P)
      add_mem' := fun {u v} hu hv P => by
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hu, hv, polyFun_add]
      algebraMap_mem' := fun c P => by
        rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          Submodule.coe_smul, polyFun_smul] }
  have hι : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x ∈ S := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact S.zero_mem
      | add y y' hy hy' => rw [map_add, map_add]; exact S.add_mem hy hy'
      | tmul c X =>
        intro P
        rw [envRepAll_ι_of, polyRep_ι_of, placeRep_tmul,
          show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
          map_smul, envRep_ι, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, opInf_coe,
          polyFun_smul, lieDer_polyFun D θ V R]
        rfl
  exact GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S hι u P

theorem realEntries_one (R : RealPoints θ V) :
    realEntries θ V 1 = fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0 := by
  funext p
  simp only [realEntries, R.2.2.2.2.1 1 (one_mem _) p.1, Matrix.one_apply]

set_option maxHeartbeats 1000000 in
open Classical in

theorem envRepAll_injective (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (_hθ : IsInfFam θ)
    (V : HSp D) (R : RealPoints θ V) : Function.Injective (envRepAll R) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  let ρ : ∀ τ, LieAt V τ → GlobalTheory.AutFinLit.Env V := fun τ X =>
    UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] X))
  have hadd : ∀ τ (X Y : LieAt V τ), ρ τ (X + Y) = ρ τ X + ρ τ Y := fun τ X Y => by
    simp only [ρ, TensorProduct.tmul_add, map_add]
  have hsmul : ∀ τ (c : ℝ) (X : LieAt V τ), ρ τ (c • X) = (c : ℂ) • ρ τ X := fun τ c X => by
    have e1 : (1 : ℂ) ⊗ₜ[ℝ] (c • X) = (c : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Complex.real_smul, mul_one]
    simp only [ρ]
    rw [e1, ← DirectSum.lof_eq_of ℂ, map_smul, map_smul, DirectSum.lof_eq_of]
  have hbrk : ∀ τ (X Y Z : LieAt V τ), Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ τ Z = ρ τ X * ρ τ Y - ρ τ Y * ρ τ X :=
    fun τ X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      simp only [ρ]
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of_same, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  choose P Q hPQ hrest using fun τ =>
    GlobalTheory.UnitaryLieComplexification.glRel_and_span V.rank (gramAt D V τ) (R.1 τ).1 (R.1 τ).2
  have hgl := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).1
  have hsp := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).2
  let e : D.what₂.Tau × Fin V.rank × Fin V.rank → GlobalTheory.AutFinLit.Env V := fun p =>
    ρ p.1 (P p.1 p.2.1 p.2.2) + Complex.I • ρ p.1 (Q p.1 p.2.1 p.2.2)
  have hρe : ∀ τ X, ρ τ X ∈ Submodule.span ℂ (Set.range e) := fun τ X =>
    Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨(τ, p.1, p.2), rfl⟩) (hsp τ X)

  have hgen : Algebra.adjoin ℂ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 ((GlobalTheory.EnvCentre.adjoin_range_ι_eq_top _).symm.le.trans (Algebra.adjoin_le ?_))
    rintro _ ⟨x, rfl⟩
    refine Algebra.span_le_adjoin ℂ _ ?_
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add y y' hy hy' => rw [map_add, map_add]; exact add_mem hy hy'
      | tmul c X =>
        rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          ← DirectSum.lof_eq_of ℂ, map_smul, map_smul]
        exact Submodule.smul_mem _ c (hρe τ X)

  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ X Y, Commute (ρ τ X) (ρ τ' Y) := fun τ τ' h X Y => by
    have h1 : ρ τ X * ρ τ' Y - ρ τ' Y * ρ τ X = 0 := by
      simp only [ρ]; rw [← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of, dif_neg h, map_zero]
    exact sub_eq_zero.1 h1
  have hbr : ∀ p q, e p * e q - e q * e p ∈ Submodule.span ℂ (Set.range e) := by
    rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩
    by_cases h : τ = τ'
    · subst h
      have := hgl τ a b c d
      simp only at this
      change (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) * (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) -
        (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) * (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) ∈ _
      rw [this]
      refine sub_mem ?_ ?_
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, a, d), rfl⟩
        · exact zero_mem _
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, c, b), rfl⟩
        · exact zero_mem _
    · have hc : Commute (e (τ, a, b)) (e (τ', c, d)) := by
        simp only [e]
        refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
        · exact hcomm τ τ' h _ _
        · exact (hcomm τ τ' h _ _).smul_right _
        · exact (hcomm τ τ' h _ _).smul_left _
        · exact ((hcomm τ τ' h _ _).smul_left _).smul_right _
      rw [hc.eq, sub_self]; exact zero_mem _

  have hπρ : ∀ τ (X : LieAt V τ), polyRep V (ρ τ X) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := fun τ X => by
    simp only [ρ]; rw [polyRep_ι_of, placeRep_ι]
  have hE : ∀ τ a b, (P τ a b).1 + Complex.I • (Q τ a b).1 = Matrix.single a b (1 : ℂ) := fun τ a b => by
    rw [(hPQ τ a b).1, (hPQ τ a b).2, smul_smul]
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this]
    module
  have hπe : ∀ p, polyRep V (e p) = (matDer p.1 (Matrix.single p.2.1 p.2.2 (1 : ℂ)) : Module.End ℂ (PolyE V)) :=
    fun p => by
      simp only [e]
      rw [map_add, map_smul, hπρ, hπρ, ← hE, matDer_add, matDer_smul]
      rfl
  have hder : ∀ p (x y : PolyE V), polyRep V (e p) (x * y) = polyRep V (e p) x * y + x * polyRep V (e p) y :=
    fun p x y => by
      rw [hπe]
      change matDer _ _ (x * y) = matDer _ _ x * y + x * matDer _ _ y
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  let pt : D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ := fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0
  let χ : PolyE V →ₐ[ℂ] ℂ := MvPolynomial.aeval pt
  let a : D.what₂.Tau × Fin V.rank × Fin V.rank → PolyE V := fun p => MvPolynomial.X p - MvPolynomial.C (pt p)
  have ha0 : ∀ k, χ (a k) = 0 := fun k => by simp [χ, a]
  have hδ : ∀ i k, χ (polyRep V (e i) (a k)) = if i = k then 1 else 0 := by
    rintro ⟨τ, a', b'⟩ ⟨τ', c, d⟩
    rw [hπe]
    exact aeval_matDer_single τ τ' a' b' c d
  refine GlobalTheory.T.faithful_of_derivations_dualFamily _ _ _ e hgen hbr (polyRep V) hder χ a ha0 hδ u fun x => ?_
  have h1 := congrFun (envRepAll_polyFun R u x) 1
  rw [hu, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  have h2 : polyFun θ V (polyRep V u x) 1 = χ (polyRep V u x) := by
    rw [polyFun, realEntries_one R, MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]; rfl
  rw [← h2, ← h1]

end GlobalTheory.CentralOps
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_representation_injective : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V), Function.Injective (envRepAll R) := by
  atlas_forward_decl GlobalTheory.CentralOps.envRepAll_injective
end

section
noncomputable section

open scoped ContDiff Topology TensorProduct

namespace GlobalTheory.EnvCommLie

open GlobalTheory.SmoothForms

section Abstract

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

def JointSm (σ : 𝔸 →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (Ψ : ℝ → G → ℂ) : Prop :=
  ∀ (g : G) (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (c : P → 𝔸), ContDiff ℝ ∞ c →
    (∀ p, σ (c p) * c p = 1) → ContDiff ℝ ∞ fun q : ℝ × P => Ψ q.1 (g * s (c q.2))

theorem unit_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) : σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem s_one (H : IsLieData σ j s) : s 1 = 1 := by
  have h := H.mul 1 1 (by rw [H.one, one_mul]) (by rw [H.one, one_mul])
  rw [one_mul] at h
  exact (mul_eq_left.1 h.symm)

theorem expMap_zero (H : IsLieData σ j s) : expMap j s 0 = 1 := by
  simp only [expMap, map_zero, NormedSpace.exp_zero, s_one H]

theorem expMap_add_smul (H : IsLieData σ j s) (X : L) (t h : ℝ) :
    expMap j s ((t + h) • X) = expMap j s (t • X) * expMap j s (h • X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hb : ∀ x : 𝔸, x ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := fun x =>
    (NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
  simp only [expMap]
  rw [← H.mul _ _ (DerLinear.exp_unitary H _) (DerLinear.exp_unitary H _), add_smul, map_add,
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) ?_ (hb _) (hb _)]
  rw [map_smul, map_smul]
  exact ((Commute.refl (j X)).smul_left t).smul_right h

theorem sm_transl (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) {b : 𝔸}
    (hb : σ b * b = 1) : Sm (expMap j s) (fun x => φ (x * s b)) := by
  intro g
  have hc : ContDiff ℝ ∞ fun Z : L => NormedSpace.exp (j Z) * b := (DerLinear.contDiff_exp H).mul contDiff_const
  have := contDiff_family H hl (fun g => (hφ g).contDiffAt) hc (fun Z => unit_mul H (DerLinear.exp_unitary H Z) hb) g
  convert this using 2 with Z
  simp only [expMap]
  rw [H.mul _ _ (DerLinear.exp_unitary H Z) hb, mul_assoc]

theorem jointSm_transl (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    JointSm σ s (fun t x => φ (x * expMap j s (t • X))) := by
  intro g P _ _ c hc hu
  have hc' : ContDiff ℝ ∞ fun q : ℝ × P => c q.2 * NormedSpace.exp (j (q.1 • X)) :=
    (hc.comp contDiff_snd).mul ((DerLinear.contDiff_exp H).comp (contDiff_fst.smul contDiff_const))
  have := contDiff_family H hl (fun g => (hφ g).contDiffAt) hc'
    (fun q => unit_mul H (hu q.2) (DerLinear.exp_unitary H _)) g
  convert this using 2 with q
  simp only [expMap]
  rw [mul_assoc, ← H.mul _ _ (hu q.2) (DerLinear.exp_unitary H _)]

theorem hasDerivAt_transl (H : IsLieData σ j s) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) (t : ℝ) (x : G) :
    HasDerivAt (fun t => φ (x * expMap j s (t • X))) (Der (expMap j s) X φ (x * expMap j s (t • X))) t := by
  have h1 : HasDerivAt (fun h : ℝ => φ (x * expMap j s (t • X) * expMap j s (h • X)))
      (Der (expMap j s) X φ (x * expMap j s (t • X))) (t - t) := by
    rw [sub_self]
    exact (Sm.differentiableAt hφ _ X).hasDerivAt
  have h2 := h1.comp_sub_const t t
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  change φ (x * expMap j s (u • X)) = φ (x * expMap j s (t • X) * expMap j s ((u - t) • X))
  rw [mul_assoc, ← expMap_add_smul H, add_sub_cancel]

omit [FiniteDimensional ℝ 𝔸] in

theorem contDiff_deriv_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : E × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ fun q => deriv (fun r => K (q, r)) 0 := by
  have e : ∀ q, deriv (fun r => K (q, r)) 0 = fderiv ℝ K (q, 0) ((0 : E), (1 : ℝ)) := fun q =>
    ((hK.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) q).prodMk (hasDerivAt_id' (0 : ℝ)))).deriv
  simp_rw [e]
  exact ((hK.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

theorem jointSm_der (H : IsLieData σ j s) (Y : L) {Ψ : ℝ → G → ℂ} (hΨ : JointSm σ s Ψ) :
    JointSm σ s (fun t => Der (expMap j s) Y (Ψ t)) := by
  intro g P _ _ c hc hu
  have hc' : ContDiff ℝ ∞ fun p : P × ℝ => c p.1 * NormedSpace.exp (j (p.2 • Y)) :=
    (hc.comp contDiff_fst).mul ((DerLinear.contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hF := hΨ g (P × ℝ) _ hc' (fun p => unit_mul H (hu p.1) (DerLinear.exp_unitary H _))
  have hK : ContDiff ℝ ∞ fun q : (ℝ × P) × ℝ =>
      Ψ q.1.1 (g * s (c q.1.2 * NormedSpace.exp (j (q.2 • Y)))) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  convert contDiff_deriv_param hK using 1
  funext q
  simp only [Der, expMap]
  congr 1
  funext r
  rw [mul_assoc, H.mul _ _ (hu _) (DerLinear.exp_unitary H _)]

theorem hasDerivAt_der (H : IsLieData σ j s) (Y : L) {Ψ Ψ' : ℝ → G → ℂ} (hΨ : JointSm σ s Ψ)
    (hd : ∀ t x, HasDerivAt (fun t => Ψ t x) (Ψ' t x) t) (t : ℝ) (x : G) :
    HasDerivAt (fun t => Der (expMap j s) Y (Ψ t) x) (Der (expMap j s) Y (Ψ' t) x) t := by
  have hc : ContDiff ℝ ∞ fun r : ℝ => NormedSpace.exp (j (r • Y)) :=
    (DerLinear.contDiff_exp H).comp (contDiff_id.smul contDiff_const)
  set F : ℝ × ℝ → ℂ := fun q => Ψ q.1 (x * s (NormedSpace.exp (j (q.2 • Y)))) with hFdef
  have hF : ContDiff ℝ ∞ F := hΨ x ℝ _ hc (fun r => DerLinear.exp_unitary H _)
  have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hdd : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have e1 : ∀ t', Der (expMap j s) Y (Ψ t') x = fderiv ℝ F (t', 0) ((0 : ℝ), (1 : ℝ)) := fun t' =>
    ((hdiff _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) t').prodMk (hasDerivAt_id' (0 : ℝ)))).deriv
  have e2 : ∀ t' r, Ψ' t' (x * expMap j s (r • Y)) = fderiv ℝ F (t', r) ((1 : ℝ), (0 : ℝ)) := fun t' r =>
    (hd t' _).unique ((hdiff _).hasFDerivAt.comp_hasDerivAt t' ((hasDerivAt_id' t').prodMk (hasDerivAt_const t' r)))
  have e3 : Der (expMap j s) Y (Ψ' t) x = fderiv ℝ (fderiv ℝ F) (t, 0) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
    have : (fun r => Ψ' t (x * expMap j s (r • Y))) = fun r => fderiv ℝ F (t, r) ((1 : ℝ), (0 : ℝ)) := funext (e2 t)
    change deriv (fun r => Ψ' t (x * expMap j s (r • Y))) 0 = _
    rw [this]
    have h := (hdd _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) t).prodMk (hasDerivAt_id' (0 : ℝ)))
    have h2 := h.clm_apply (hasDerivAt_const (0 : ℝ) ((1 : ℝ), (0 : ℝ)))
    simpa using h2.deriv
  have hL : HasDerivAt (fun t' => fderiv ℝ F (t', 0) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ F) (t, 0) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) t := by
    have h := (hdd _).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t (0 : ℝ)))
    simpa using h.clm_apply (hasDerivAt_const t ((0 : ℝ), (1 : ℝ)))
  have hsym := (hF.contDiffAt (x := (t, (0 : ℝ)))).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤))
  rw [e3, ← hsym ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))]
  exact hL.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t' => e1 t')

def GoodOp (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (A : Module.End ℂ (smSub (expMap j s))) : Prop :=
  ∀ Ψ Ψ' : ℝ → smSub (expMap j s), JointSm σ s (fun t => (Ψ t).1) → JointSm σ s (fun t => (Ψ' t).1) →
    (∀ t x, HasDerivAt (fun t => (Ψ t).1 x) ((Ψ' t).1 x) t) →
    JointSm σ s (fun t => (A (Ψ t)).1) ∧ JointSm σ s (fun t => (A (Ψ' t)).1) ∧
      ∀ t x, HasDerivAt (fun t => (A (Ψ t)).1 x) ((A (Ψ' t)).1 x) t

theorem goodOp_derOp (H : IsLieData σ j s) (hl : HasLog σ j) (Y : L) : GoodOp σ j s (derOp H hl Y) :=
  fun _ _ h1 h2 h3 => ⟨jointSm_der H Y h1, jointSm_der H Y h2, hasDerivAt_der H Y h1 h3⟩

theorem goodOp_algebraMap (c : ℂ) : GoodOp σ j s (algebraMap ℂ (Module.End ℂ (smSub (expMap j s))) c) := by
  intro Ψ Ψ' h1 h2 h3
  simp only [Module.algebraMap_end_apply, Submodule.coe_smul]
  exact ⟨fun g P _ _ c' hc hu => (h1 g P c' hc hu).const_smul c, fun g P _ _ c' hc hu => (h2 g P c' hc hu).const_smul c,
    fun t x => (h3 t x).const_smul c⟩

theorem goodOp_add {A B : Module.End ℂ (smSub (expMap j s))} (hA : GoodOp σ j s A) (hB : GoodOp σ j s B) :
    GoodOp σ j s (A + B) := by
  intro Ψ Ψ' h1 h2 h3
  obtain ⟨a1, a2, a3⟩ := hA Ψ Ψ' h1 h2 h3
  obtain ⟨b1, b2, b3⟩ := hB Ψ Ψ' h1 h2 h3
  simp only [LinearMap.add_apply, Submodule.coe_add]
  exact ⟨fun g P _ _ c hc hu => (a1 g P c hc hu).add (b1 g P c hc hu),
    fun g P _ _ c hc hu => (a2 g P c hc hu).add (b2 g P c hc hu), fun t x => (a3 t x).add (b3 t x)⟩

theorem goodOp_mul {A B : Module.End ℂ (smSub (expMap j s))} (hA : GoodOp σ j s A) (hB : GoodOp σ j s B) :
    GoodOp σ j s (A * B) := by
  intro Ψ Ψ' h1 h2 h3
  obtain ⟨b1, b2, b3⟩ := hB Ψ Ψ' h1 h2 h3
  exact hA (fun t => B (Ψ t)) (fun t => B (Ψ' t)) b1 b2 b3

theorem goodOp_of_mem (H : IsLieData σ j s) (hl : HasLog σ j) {A : Module.End ℂ (smSub (expMap j s))}
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (derOp H hl))) : GoodOp σ j s A := by
  induction hA using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨Y, rfl⟩ := hx; exact goodOp_derOp H hl Y
  | algebraMap c => exact goodOp_algebraMap c
  | add x y _ _ hx hy => exact goodOp_add hx hy
  | mul x y _ _ hx hy => exact goodOp_mul hx hy

theorem comm_of_transl (H : IsLieData σ j s) (hl : HasLog σ j) (X : L) {A : Module.End ℂ (smSub (expMap j s))}
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (derOp H hl)))
    (htr : ∀ (t : ℝ) (φ : smSub (expMap j s)) (h : (fun x => φ.1 (x * expMap j s (t • X))) ∈ smSub (expMap j s)),
      (A ⟨_, h⟩).1 = fun x => (A φ).1 (x * expMap j s (t • X))) :
    derOp H hl X * A = A * derOp H hl X := by
  have hG : GoodOp σ j s A := goodOp_of_mem H hl hA
  refine LinearMap.ext fun φ => Subtype.ext (funext fun g => ?_)
  have mem : ∀ (ψ : smSub (expMap j s)) (t : ℝ), (fun x => ψ.1 (x * expMap j s (t • X))) ∈ smSub (expMap j s) :=
    fun ψ t => sm_transl H hl ψ.2 (DerLinear.exp_unitary H (t • X))
  let Ψ : ℝ → smSub (expMap j s) := fun t => ⟨_, mem φ t⟩
  let Ψ' : ℝ → smSub (expMap j s) := fun t => ⟨_, mem (derOp H hl X φ) t⟩
  have hd : ∀ t x, HasDerivAt (fun t => (Ψ t).1 x) ((Ψ' t).1 x) t := fun t x => hasDerivAt_transl H φ.2 X t x
  obtain ⟨-, -, h3⟩ := hG Ψ Ψ' (jointSm_transl H hl φ.2 X) (jointSm_transl H hl (derOp H hl X φ).2 X) hd
  have h4 := h3 0 g
  have e0 : Ψ' 0 = derOp H hl X φ := Subtype.ext (funext fun x => by
    change (derOp H hl X φ).1 (x * expMap j s ((0 : ℝ) • X)) = _
    rw [zero_smul, expMap_zero H, mul_one])
  rw [e0] at h4
  have h5 : (fun t => (A (Ψ t)).1 g) = fun t => (A φ).1 (g * expMap j s (t • X)) :=
    funext fun t => congrFun (htr t φ (mem φ t)) g
  rw [h5] at h4
  have h6 : HasDerivAt (fun t : ℝ => (A φ).1 (g * expMap j s (t • X))) ((derOp H hl X (A φ)).1 g) 0 :=
    (Sm.differentiableAt (A φ).2 g X).hasDerivAt
  exact h6.unique h4

end Abstract

section Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

open Classical in

theorem envRepAll_ι_of_tmul (R : RealPoints θ V) (τ : D.what₂.Tau) (c : ℂ) (X : LieAt V τ) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ (c ⊗ₜ X))) =
      c • opInf R (atPlace V τ X) := by
  rw [← envIncl_ι, envRepAll_envIncl]
  have : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, map_smul, envRep_ι]

open Classical in
theorem envRepAll_ι_mem (R : RealPoints θ V) (x : GlobalTheory.AutFinLit.LieC V) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) ∈ Algebra.adjoin ℂ (Set.range (opInf R)) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | of τ y =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
    | tmul c X => rw [envRepAll_ι_of_tmul]; exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) c
    | add a b ha hb => rw [map_add, map_add, map_add]; exact add_mem ha hb
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

theorem envRepAll_mem (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V) :
    envRepAll R u ∈ Algebra.adjoin ℂ (Set.range (opInf R)) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V)) :=
    by unfold UniversalEnvelopingAlgebra.mkAlgHom; exact RingCon.mkₐ_surjective _
  obtain ⟨w, rfl⟩ := hs u
  induction w using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | ι x => rw [← UniversalEnvelopingAlgebra.ι_apply]; exact envRepAll_ι_mem R x
  | mul a b ha hb => rw [map_mul, map_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

end Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
attribute [local instance 100] LieRing.ofAssociativeRing in

theorem envRepAll_comm_lie : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V), (∀ a ∈ GinfC V, ∀ (f : SmF θ V)
      (hfa : (fun x => f.1 (x * a)) ∈ SmF θ V), (envRepAll R u ⟨_, hfa⟩).1 = fun x => (envRepAll R u f).1 (x * a)) →
    ∀ x : GlobalTheory.AutFinLit.LieC V, envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) * envRepAll R u =
      envRepAll R u * envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) := by
  intro D θ _ V R u hu x
  have hcomm : ∀ τ (X : LieAt V τ),
      opInf R (atPlace V τ X) * envRepAll R u = envRepAll R u * opInf R (atPlace V τ X) := fun τ X =>
    comm_of_transl (isLieData R) (hasLog R) (atPlace V τ X) (envRepAll_mem R u) fun t φ h =>
      hu _ (isExpFam_expInf R (t • atPlace V τ X)).1 φ h
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of τ y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c X => rw [envRepAll_ι_of_tmul, smul_mul_assoc, mul_smul_comm, hcomm]
    | add a b ha hb => rw [map_add, map_add, map_add, add_mul, mul_add, ha, hb]
  | add a b ha hb => rw [map_add, map_add, add_mul, mul_add, ha, hb]

end GlobalTheory.EnvCommLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enveloping_action_commutes_translation : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V), (∀ a ∈ GinfC V, ∀ (f : SmF θ V) (hfa : (fun x => f.1 (x * a)) ∈ SmF θ V), (envRepAll R u ⟨_, hfa⟩).1 = fun x => (envRepAll R u f).1 (x * a)) → ∀ x : GlobalTheory.AutFinLit.LieC V, envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) * envRepAll R u = envRepAll R u * envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) := by
  first | exact @GlobalTheory.EnvCommLie.envRepAll_comm_lie | exact GlobalTheory.EnvCommLie.envRepAll_comm_lie | (intros; apply GlobalTheory.EnvCommLie.envRepAll_comm_lie <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.UAut GlobalTheory.Mem.Th GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSm_of_smF (hθ : IsInfFam θ) (R : RealPoints θ V) (f : SmF θ V) : IsSm D.sp.cm.sig V.gram f.1 := by
  intro k γ hγ g
  choose p hp e using fun i => (hγ i).eq_oneP hθ
  simpa only [e] using (smooth_iff R f.1).2 f.2 k (fun i => (p i).1) (fun i => (p i).2) hp g

theorem exists_word (hθ : IsInfFam θ) (R : RealPoints θ V) (l : List (ℝ → GA D V))
    (hl : ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ w : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, l.foldr lineDer f.1 = (envRepAll R w f).1 := by
  classical
  induction l with
  | nil => exact ⟨1, fun f => by rw [map_one]; rfl⟩
  | cons γ l ih =>
    obtain ⟨w, hw⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    obtain ⟨⟨τ, X⟩, hX, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    refine ⟨UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] ⟨X, hX⟩)) * w,
      fun f => ?_⟩
    rw [map_mul, Module.End.mul_apply, ← envIncl_ι, envRepAll_envIncl, envRep_ι, opInf_coe, ← hw, List.foldr_cons]
    exact Rder_eq R τ ⟨X, hX⟩ _

theorem exists_env (hθ : IsInfFam θ) (R : RealPoints θ V) (z : List (ℝ → GA D V) →₀ ℂ)
    (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) :
    ∃ u : GlobalTheory.AutFinLit.Env V, ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  classical
  choose! w hw using fun l (hl : l ∈ z.support) => exists_word hθ R l (hz l hl)
  refine ⟨∑ l ∈ z.support, z l • w l, fun f => ?_⟩
  rw [map_sum, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  simp only [dop, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← hw l hl]

theorem mem_center_of_comm (u : GlobalTheory.AutFinLit.Env V)
    (h : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x * u = u * UniversalEnvelopingAlgebra.ι ℂ x) :
    u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V)) := by
    unfold UniversalEnvelopingAlgebra.mkAlgHom
    first | exact RingCon.mkₐ_surjective _ _ | exact RingCon.mkₐ_surjective _ | exact fun b => Quotient.inductionOn' b fun t => ⟨t, rfl⟩ | exact Quot.mk_surjective
  obtain ⟨t, rfl⟩ := hs b
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r u
  | ι x => exact h x
  | mul a b ha hb => rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [map_add, add_mul, mul_add, ha, hb]

theorem mem_of_mem_center (R : RealPoints θ V) {W : Submodule ℂ (GA D V → ℂ)}
    (hs : ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) {u : GlobalTheory.AutFinLit.Env V}
    (hu : u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V)) : ∀ f : SmF θ V, f.1 ∈ W → (envRepAll R u f).1 ∈ W := by
  classical
  choose c hc hg using exists_gelf R
  have hloc : ∀ τ, ∀ z ∈ Subalgebra.center ℂ (EnvAt V τ), ∀ f : SmF θ V, f.1 ∈ W → (envRep R τ z f).1 ∈ W := by
    intro τ z hz
    rw [hc τ] at hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; intro f hf; rw [← hg]; exact hs τ k _ hf
    | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
    | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)
  rw [GlobalTheory.EnvCentre.center_directSum D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) (fun τ => envIncl V τ)
    (fun τ x => envIncl_ι τ x)] at hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, z, hz, rfl⟩ := Set.mem_iUnion.1 hx |>.imp fun τ h => h
    intro f hf; rw [envRepAll_envIncl]; exact hloc τ z hz f hf
  | algebraMap r => intro f hf; rw [AlgHom.commutes]; exact W.smul_mem r hf
  | add x y _ _ hx hy => intro f hf; rw [map_add]; exact add_mem (hx f hf) (hy f hf)
  | mul x y _ _ hx hy => intro f hf; rw [map_mul]; exact hx _ (hy f hf)

theorem exists_center (hθ : IsInfFam θ) (R : RealPoints θ V) {z : List (ℝ → GA D V) →₀ ℂ}
    (hz : IsCentral D.sp.cm.sig V.gram z) :
    ∃ u ∈ Subalgebra.center ℂ (GlobalTheory.AutFinLit.Env V), ∀ f : SmF θ V, dop z f.1 = (envRepAll R u f).1 := by
  obtain ⟨u, hu⟩ := exists_env hθ R z hz.1
  refine ⟨u, mem_center_of_comm u fun x => GlobalTheory.T.enveloping_representation_injective _ _ hθ V R ?_, hu⟩
  rw [map_mul, map_mul]
  refine GlobalTheory.T.enveloping_action_commutes_translation _ _ hθ V R u (fun a ha f hfa => ?_) x
  rw [← hu, ← hu]
  funext g
  exact hz.2 f.1 (isSm_of_smF hθ R f) a ha g

end GlobalTheory.CentralOps
end
end
