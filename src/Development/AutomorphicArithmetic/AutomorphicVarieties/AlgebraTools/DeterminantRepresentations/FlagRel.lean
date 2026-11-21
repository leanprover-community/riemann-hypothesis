import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Mathlib

section
open Polynomial Matrix

private theorem UpperTheory.V.AlgebraTools.Det.flag_product_maps_into {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (W : ℕ → Submodule R V) :
    ∀ (n : ℕ) (f : Fin n → Module.End R V),
    (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → ∀ v ∈ W n, (List.ofFn f).prod v ∈ W 0 := by
  intro n
  induction n generalizing W with
  | zero =>
    intro f _ v hv
    simpa using hv
  | succ n ih =>
    intro f hf v hv
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    have h0 := hf 0
    simp only [Fin.val_zero, zero_add] at h0
    apply h0
    have ht := ih (fun k => W (k + 1)) (fun i => f i.succ) (fun j w hw => by
      have hj := hf j.succ w (by simpa [Fin.val_succ] using hw)
      simpa [Fin.val_succ] using hj) v hv
    simpa using ht

theorem UpperTheory.V.AlgebraTools.Det.flagKill :
    ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (n : ℕ) (W : ℕ → Submodule R V) (f : Fin n → Module.End R V),
    W 0 = ⊥ → W n = ⊤ → (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → (List.ofFn f).prod = 0 := by
  intro R V _ _ _ n W f h0 hn hf
  ext v
  have h := UpperTheory.V.AlgebraTools.Det.flag_product_maps_into W n f hf v (by rw [hn]; exact Submodule.mem_top)
  rw [h0, Submodule.mem_bot] at h
  simpa using h
end

section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.flagRel :
    ∀ {k H : Type} [CommRing k] [Group H] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ), HasFlag r κ →
    (∀ s, (mat r s).charpoly = ∏ j, (X - C (κ j s : k))) ∧
    ∀ g : Fin n → H, (List.ofFn fun j => mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)).prod = 0 := by
  intro k H _ _ n r κ ⟨P, hP⟩
  have hm : ∀ s, mat r s = (r s : Matrix (Fin n) (Fin n) k) := fun _ => rfl
  constructor
  · intro s
    have h1 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = (mat r s).charpoly := by
      rw [hm, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
      fun i j hij => (hP s).1 i j hij
    rw [← h1, Matrix.charpoly_of_upperTriangular _ h2]
    exact Finset.prod_congr rfl fun i _ => by rw [← (hP s).2 i]
  · intro g
    let W : ℕ → Submodule k (Fin n → k) := fun j =>
      { carrier := {v | ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0}
        add_mem' := fun {a b} ha hb i hi => by
          rw [Matrix.mulVec_add, Pi.add_apply, ha i hi, hb i hi, add_zero]
        zero_mem' := fun i _ => by simp
        smul_mem' := fun c a ha i hi => by
          rw [Matrix.mulVec_smul, Pi.smul_apply, ha i hi, smul_zero] }
    have hW : ∀ j v, v ∈ W j ↔ ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0 :=
      fun _ _ => Iff.rfl
    have key := UpperTheory.V.AlgebraTools.Det.flagKill n W
      (fun j => Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k))) ?_ ?_ ?_
    · apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective
      rw [map_list_prod, map_zero, List.map_ofFn]
      exact key
    · rw [eq_bot_iff]
      intro v hv
      have h0 : (P : Matrix (Fin n) (Fin n) k) *ᵥ v = 0 := funext fun i => (hW 0 v).1 hv i (Nat.zero_le _)
      have : v = ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Submodule.mem_bot, this, h0, Matrix.mulVec_zero]
    · rw [eq_top_iff]
      intro v _
      exact (hW n v).2 fun i hi => absurd i.2 (not_lt.2 hi)
    · intro j v hv
      rw [hW] at hv ⊢
      intro i hi
      have e : (P : Matrix (Fin n) (Fin n) k) *ᵥ
          (Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)) v) =
          ((P * r (g j) * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v)
            - (κ j (g j) : k) • ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm, Units.val_mul, Units.val_mul,
          Units.inv_mul_cancel_right]
      rw [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      generalize (P : Matrix (Fin n) (Fin n) k) *ᵥ v = w at hv ⊢
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · rcases eq_or_lt_of_le hi with h | h
        · have : j = i := Fin.ext h
          subst this
          rw [← (hP (g j)).2 j]
        · rw [hv i h, mul_zero, mul_zero]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with h | h
        · have := (hP (g j)).1 i b h
          rw [this, zero_mul]
        · rw [hv b (by have : i.val < b.val := h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
end
