import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeContractingHomotopy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyHomotopyFormula

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ.Shuf

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op (SimplexCategory.mk n), op (SimplexCategory.mk m)) ⟶
      (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) from (α.op, β.op))
    (show (op (SimplexCategory.mk p), op (SimplexCategory.mk q)) ⟶
      (op (SimplexCategory.mk r), op (SimplexCategory.mk s)) from (α'.op, β'.op)) 1 1
  simp only [mul_one] at this
  exact this

theorem bop_id (n m : ℕ) : bop (𝟙 (SimplexCategory.mk n)) (𝟙 (SimplexCategory.mk m)) = 𝟙 (bo n m) := rfl

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = ((j : Fin (n + 1)) : ℕ)
  omega

theorem fc_comp_fc (n i j : ℕ) (hji : j < i) (hi : i ≤ n + 2) :
    fc (n + 1) n j ≫ fc (n + 2) (n + 1) i = fc (n + 1) n (i - 1) ≫ fc (n + 2) (n + 1) j := by
  ext k
  have hk : (k : ℕ) < n + 1 := k.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply, OrderHom.coe_mk]
  split_ifs <;> omega

theorem alt_double_sum {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : (SimplexCategory.mk n ⟶ SimplexCategory.mk (n + 2)) → M) :
    ∑ i ∈ Finset.range (n + 3), ∑ j ∈ Finset.range (n + 2),
      ((-1 : ℤ) ^ i * (-1) ^ j) • F (fc (n + 1) n j ≫ fc (n + 2) (n + 1) i) = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    dsimp only
    split_ifs with hji
    · dsimp only
      rw [fc_comp_fc n i j hji (by omega), ← add_smul]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [show i' + 1 - 1 = i' by omega, pow_succ]
      ring_nf
      simp
    · dsimp only
      rw [fc_comp_fc n (j + 1) i (by omega) (by omega), show j + 1 - 1 = j by omega, ← add_smul, pow_succ]
      ring_nf
      simp
  · rintro ⟨i, j⟩ _ _
    dsimp only
    split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    split_ifs <;> simp only <;> omega
  · rintro ⟨i, j⟩ _
    by_cases h : j < i
    · simp only [h, if_true]
      rw [if_neg (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega
    · simp only [h, if_false]
      rw [if_pos (by omega)]
      simp only [Prod.mk.injEq, and_true, true_and]
      omega

theorem dH_comp_dH (a b x y c d : ℕ) : dH a b x y ≫ dH x y c d = 0 := by
  unfold dH
  by_cases h1 : a = x + 1 ∧ b = y
  · by_cases h2 : x = c + 1 ∧ y = d
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum c (fun α => bop α (idc b b ≫ idc b b))
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dV_comp_dV (a b x y c d : ℕ) : dV a b x y ≫ dV x y c d = 0 := by
  unfold dV
  by_cases h1 : a = x ∧ b = y + 1
  · by_cases h2 : x = c ∧ y = d + 1
    · obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, Preadditive.sum_comp]
      simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul]
      have := alt_double_sum d (fun β => bop (idc a a ≫ idc a a) β)
      simpa only [mul_comm] using this
    · rw [if_neg h2, comp_zero]
  · rw [if_neg h1, zero_comp]

theorem dH_comp_dV (c d : ℕ) :
    dH (c + 1) (d + 1) c (d + 1) ≫ dV c (d + 1) c d = dV (c + 1) (d + 1) (c + 1) d ≫ dH (c + 1) d c d := by
  unfold dH dV
  rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩,
    Preadditive.sum_comp, Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul, bop_comp, smul_smul,
    idc_self, Category.id_comp, Category.comp_id]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem dT_comp_dT (a b c d k : ℕ) (hk : c + d = k) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 := by
  subst hk
  have hsplit : ∀ x : ℕ × ℕ, dT a b x.1 x.2 ≫ dT x.1 x.2 c d =
      ((-1 : ℤ) ^ x.1) • (dH a b x.1 x.2 ≫ dV x.1 x.2 c d) +
        ((-1 : ℤ) ^ a) • (dV a b x.1 x.2 ≫ dH x.1 x.2 c d) := by
    intro x
    simp only [dT, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      dH_comp_dH, dV_comp_dV, smul_zero, zero_add, add_zero]
    rw [add_comm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hm1 : (c, d + 1) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  have hm2 : (c + 1, d) ∈ Finset.HasAntidiagonal.antidiagonal (c + d + 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  rw [Finset.sum_eq_single_of_mem (c, d + 1) hm1 ?_, Finset.sum_eq_single_of_mem (c + 1, d) hm2 ?_]
  · dsimp only
    by_cases h : a = c + 1 ∧ b = d + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [dH_comp_dV c d, ← add_smul, pow_succ]
      simp
    · have e1 : dH a b c (d + 1) = 0 := by unfold dH; rw [if_neg h]
      have e2 : dV a b (c + 1) d = 0 := by unfold dV; rw [if_neg h]
      rw [e1, e2, zero_comp, zero_comp, smul_zero, smul_zero, add_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dH x1 x2 c d = 0 := by
      unfold dH; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]
  · rintro ⟨x1, x2⟩ _ hx
    have : dV x1 x2 c d = 0 := by
      unfold dV; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hx rfl
    dsimp only
    rw [this, comp_zero, smul_zero]

noncomputable def shufRec (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n : ℕ) :
    ∀ a b : ℕ, bo a b ⟶ bo n n :=
  Nat.rec (motive := fun n => ∀ a b : ℕ, bo a b ⟶ bo n n) (fun a b => idO a b 0 0)
    (fun n g a b => if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ g x.1 x.2) else 0) n

theorem shufRec_zero (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (a b : ℕ) :
    shufRec cone 0 a b = idO a b 0 0 := rfl

theorem shufRec_succ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) (n a b : ℕ) :
    shufRec cone (n + 1) a b = if a + b = n + 1 then
      cone a b n (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ shufRec cone n x.1 x.2) else 0 := rfl

theorem exists_shuffle : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧
    ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  obtain ⟨cone, ε, hε, h0, hs⟩ := GlobalTheory.T.cone_contracting_homotopy
  have hid : shufRec cone 0 0 0 = 𝟙 (bo 0 0) := by
    rw [shufRec_zero]
    rw [idO, if_pos ⟨rfl, rfl⟩, idc_self]
    exact bop_id 0 0
  refine ⟨fun a b n => shufRec cone n a b, hid, ?_⟩
  intro a b n
  induction n generalizing a b with
  | zero =>
    intro hab
    dsimp only
    rw [shufRec_succ, if_pos hab, h0]
    have hr : ε a b (∑ x ∈ Finset.HasAntidiagonal.antidiagonal 0, dT a b x.1 x.2 ≫ shufRec cone 0 x.1 x.2) = 0 := by
      rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      dsimp only
      rw [hid, Category.comp_id]
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]
      · simp [dT, dH, dV, Finset.sum_range_succ, map_add, map_zsmul, hε]
    rw [hr, zero_smul, sub_zero]
  | succ n ih =>
    intro hab
    dsimp only at ih ⊢
    rw [shufRec_succ, if_pos hab, hs]
    have step : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
        (dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫ dD (n + 1) n =
          ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, (dT a b x.1 x.2 ≫ dT x.1 x.2 y.1 y.2) ≫
            shufRec cone n y.1 y.2 := by
      intro x hx
      rw [Category.assoc, ih x.1 x.2 (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
      simp only [Category.assoc]
    have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), dT a b x.1 x.2 ≫ shufRec cone (n + 1) x.1 x.2) ≫
        dD (n + 1) n = 0 := by
      rw [Preadditive.sum_comp, Finset.sum_congr rfl step, Finset.sum_comm]
      refine Finset.sum_eq_zero fun y hy => ?_
      rw [← Preadditive.sum_comp, dT_comp_dT a b y.1 y.2 n (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), zero_comp]
    rw [hz, map_zero, sub_zero]

end GlobalTheory.EZ.Shuf
end
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bisimplicial_shuffle_operators : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧ ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  first | (exact @GlobalTheory.EZ.Shuf.exists_shuffle) | (exact GlobalTheory.EZ.Shuf.exists_shuffle) | (intros; apply GlobalTheory.EZ.Shuf.exists_shuffle  <;> assumption)
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_succ_eq_δ (n i : ℕ) (hi : i < n + 2) :
    fc (n + 1) n i = SimplexCategory.δ (⟨i, hi⟩ : Fin (n + 2)) := by
  ext j
  simp [fc, clampHom, faceFun, SimplexCategory.δ, Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

def diagOp : SimplicialObject BOp := Functor.diag SimplexCategoryᵒᵖ ⋙ Free.embedding ℤ _

theorem dD_succ_eq_objD (n : ℕ) : dD (n + 1) n = AlternatingFaceMapComplex.objD diagOp n := by
  rw [dD, if_pos rfl, AlternatingFaceMapComplex.objD, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fc_succ_eq_δ n i i.2]
  rfl

theorem dD_comp_dD (n m k : ℕ) : dD n m ≫ dD m k = 0 := by
  by_cases h1 : n = m + 1
  · subst h1
    by_cases h2 : m = k + 1
    · subst h2
      rw [dD_succ_eq_objD, dD_succ_eq_objD]
      exact AlternatingFaceMapComplex.d_squared diagOp k
    · rw [show dD m k = 0 from if_neg h2, Limits.comp_zero]
  · rw [show dD n m = 0 from if_neg h1, Limits.zero_comp]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl]
  have h1 : idc 0 0 = 𝟙 _ := Subsingleton.elim _ _
  have h2 : backc 0 0 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, h2]
  rfl

def awThen (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : bo n n ⟶ bo n n :=
  ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n

def awHtpy (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) :
    ∀ n : ℕ, bo n n ⟶ bo (n + 1) (n + 1) := fun n =>
  Nat.rec (motive := fun n => bo n n ⟶ bo (n + 1) (n + 1)) 0
    (fun k K => cone (k + 1) (k + 1) (k + 1) (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ K)) n

theorem awThen_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b) (n : ℕ) :
    awThen G (n + 1) ≫ dD (n + 1) n = dD (n + 1) n ≫ awThen G n := by
  simp only [awThen, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have e1 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
      awO (n + 1) x.1 x.2 ≫ G x.1 x.2 (n + 1) ≫ dD (n + 1) n =
        ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun x hx => by rw [hG _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
  have e2 : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      dD (n + 1) n ≫ awO n y.1 y.2 ≫ G y.1 y.2 n =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun y hy => by
      rw [← Category.assoc, haw _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), Preadditive.sum_comp]
      simp only [Category.assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

theorem awHtpy_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (hcone : ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n)) :
    ∀ n : ℕ, awThen G (n + 1) = 𝟙 _ + awHtpy G cone (n + 1) ≫ dD (n + 1 + 1) (n + 1) +
      dD (n + 1) n ≫ awHtpy G cone n := by
  have h0 : awThen G 0 = 𝟙 _ := by
    simp [awThen, awO_zero, hG0]
  have key : ∀ k : ℕ,
      (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k) ≫ dD (k + 1) k = 0 →
      awThen G (k + 1) = 𝟙 _ + awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) +
        dD (k + 1) k ≫ awHtpy G cone k := by
    intro k hk
    have h := hcone (k + 1) (k + 1) k (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k)
    rw [hk, map_zero, sub_zero] at h
    have h' : awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) =
        awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k := h
    rw [h']
    abel
  intro n
  induction n with
  | zero =>
    apply key
    have hK : awHtpy G cone 0 = 0 := rfl
    rw [hK, Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw 0, h0]
    simp
  | succ j ih =>
    apply key
    rw [Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw (j + 1), ih,
      Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (dD (j + 1 + 1) (j + 1)) (dD (j + 1) j),
      dD_comp_dD, Limits.zero_comp]
    simp only [Category.comp_id, Category.id_comp, Category.assoc, add_zero]
    abel

theorem awThen_homotopic : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ,
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
        𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  intro G hG0 hG
  obtain ⟨cone, ε, -, -, hcone⟩ := GlobalTheory.T.cone_contracting_homotopy
  have haw := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
  refine ⟨fun n m => if h : m = n + 1 then awHtpy G cone n ≫ eqToHom (by rw [h]) else 0, fun n => ?_⟩
  cases n with
  | zero =>
    have h0 : awThen G 0 = 𝟙 _ := by
      simp [awThen, awO_zero, hG0]
    have hK : awHtpy G cone 0 = 0 := rfl
    change awThen G 0 = _
    simp [h0, hK, dD]
  | succ k =>
    change awThen G (k + 1) = _
    simp only [dif_pos, eqToHom_refl, Category.comp_id, Nat.add_sub_cancel]
    exact awHtpy_spec G hG0 hG haw cone hcone k

end GlobalTheory.EZ
end
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  first | (exact @GlobalTheory.EZ.awThen_homotopic) | (exact GlobalTheory.EZ.awThen_homotopic) | (intros; apply GlobalTheory.EZ.awThen_homotopic <;> assumption)
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

namespace GlobalTheory.EZ

theorem fc_succ_eq_delta (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min (n + 1) (if (j : ℕ) < i then (j : ℕ) else j + 1) = ((Fin.succAbove i j : Fin (n+2)) : ℕ)
  rcases lt_or_ge (j : ℕ) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h] <;> omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)]
    simp [show ¬ (j : ℕ) < i by omega] <;> omega

theorem ev_map_dD_eq_diagCx_d {C : Type u} [Category.{v} C] [Preadditive C]
    (Y : SimplicialObject (SimplicialObject C)) (n : ℕ) :
    (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  refine Eq.trans ?_ (AlternatingFaceMapComplex.obj_d_eq (diag.obj Y) n).symm
  rw [dD, if_pos rfl, Functor.map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Functor.map_zsmul, ev_map_bop, fc_succ_eq_delta]
  rfl

end GlobalTheory.EZ
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  first | (exact @GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (exact GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (intros; apply GlobalTheory.EZ.ev_map_dD_eq_diagCx_d <;> assumption)
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_eq_δ (n : ℕ) (i : Fin (n + 2)) : fc (n + 1) n i = SimplexCategory.δ i := by
  ext j
  simp only [fc, clampHom, faceFun, SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rcases Fin.lt_or_le (Fin.castSucc j) i with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt _ _ hj]
    have : (j : ℕ) < i := hj
    simp only [this, if_true, Fin.coe_castSucc]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega
  · rw [Fin.succAbove_of_le_castSucc _ _ hj]
    have : ¬ (j : ℕ) < i := by simpa [Fin.le_iff_val_le_val] using hj
    simp only [this, if_false, Fin.val_succ]
    have := j.isLt
    simp only [SimplexCategory.len_mk] at this ⊢
    omega

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom, SimplexCategory.mkHom]
  omega

theorem hsum_f {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} {α : Type} (s : Finset α) (f : α → (K ⟶ L)) (i : ι) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i :=
  (HomologicalComplex.eval C c i).map_sum f s

section
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem dbl_d_f (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).d (a + 1) a).f b = (ev Y).map (dH (a + 1) b a b) := by
  simp only [dH, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Finset.sum_range]
  dsimp only [dbl, alternatingFaceMapComplex]
  rw [AlternatingFaceMapComplex.obj_d_eq, hsum_f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [HomologicalComplex.zsmul_f_apply, fc_eq_δ]
  rfl

theorem dbl_X_d (Y : SimplicialObject (SimplicialObject C)) (a b : ℕ) :
    ((dbl Y).X a).d (b + 1) b = (ev Y).map (dV a (b + 1) a b) := by
  simp only [dV, and_self, if_true, Functor.map_sum, Functor.map_zsmul, ev_map_bop,
    idc_self, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [Finset.sum_range]
  change (AlternatingFaceMapComplex.obj (Y.obj (op (SimplexCategory.mk a)))).d (b + 1) b = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [fc_eq_δ]
  rfl

variable [HasFiniteCoproducts C]

theorem ιTotal_D₁ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₁ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dH a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  rw [HomologicalComplex₂.ι_D₁]
  rcases a with _ | a
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (0 = x.1.1 + 1 ∧ b = x.1.2) := by omega
    simp only [dH, hx, if_false, Functor.map_zero]
    exact zero_comp
  · rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (a + 1) a from rfl) b k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_d_f]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a + 1 = x1 + 1 ∧ b = x2) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h2
        have : x1 = a := by omega
        subst this
        rfl
      simp only [dH, this, if_false, Functor.map_zero]
      exact zero_comp
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_D₂ (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (dbl Y).D₂ (ComplexShape.down ℕ) (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, ((-1 : ℤ) ^ a) • ((ev Y).map (dV a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)) := by
  rw [HomologicalComplex₂.ι_D₂]
  rcases b with _ | b
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have hx : ¬ (a = x.1.1 ∧ 0 = x.1.2 + 1) := by omega
    simp only [dV, hx, if_false, Functor.map_zero]
    exact (congrArg _ zero_comp).trans (zsmul_zero _)
  · rw [HomologicalComplex₂.d₂_eq _ _ a (show (ComplexShape.down ℕ).Rel (b + 1) b from rfl) k
      (by simp only [ComplexShape.π_def]; omega)]
    rw [Finset.sum_eq_single ⟨(a, b), by simp; omega⟩]
    · rw [dbl_X_d]
      simp
      rfl
    · rintro ⟨⟨x1, x2⟩, hx⟩ _ hne
      have : ¬ (a = x1 ∧ b + 1 = x2 + 1) := by
        rintro ⟨h1, h2⟩
        apply hne
        subst h1
        have : x2 = b := by omega
        subst this
        rfl
      simp only [dV, this, if_false, Functor.map_zero]
      exact (congrArg _ zero_comp).trans (zsmul_zero _)
    · intro hn
      exact absurd (Finset.mem_attach _ _) hn

theorem ιTotal_tot_d (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ)
    (h : a + b = k + 1) :
    (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫
        (tot Y).d (k + 1) k =
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫
        (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k
          (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  change _ ≫ ((dbl Y).total (ComplexShape.down ℕ)).d (k + 1) k = _
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, ιTotal_D₁ Y a b k h, ιTotal_D₂ Y a b k h]
  refine Eq.trans Finset.sum_add_distrib.symm (Finset.sum_congr rfl (fun x _ => ?_))
  rw [dT, Functor.map_add, Functor.map_zsmul]
  first
    | (rw [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (simp only [Preadditive.add_comp, Preadditive.zsmul_comp])
    | (erw [Preadditive.add_comp, Preadditive.zsmul_comp])
  rfl

end

end GlobalTheory.EZ

example : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := @GlobalTheory.EZ.ιTotal_tot_d
end
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  first | (exact @GlobalTheory.EZ.ιTotal_tot_d) | (exact GlobalTheory.EZ.ιTotal_tot_d) | (intros; apply GlobalTheory.EZ.ιTotal_tot_d <;> assumption)
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

theorem awop' : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
theorem evd' : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := @GlobalTheory.T.diagonal_differential_eval
theorem totd' : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := @GlobalTheory.T.total_differential_eval

abbrev ιz (a b n : ℕ) : ((dbl Y).X a).X b ⟶ (tot Y).X n := (dbl Y).ιTotalOrZero (ComplexShape.down ℕ) a b n

theorem ιz_eq (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n = (dbl Y).ιTotal (ComplexShape.down ℕ) a b n (by simpa only [ComplexShape.π_def] using h) :=
  (dbl Y).ιTotalOrZero_eq _ _ _ _ _

theorem ιz_ne (a b n : ℕ) (h : a + b ≠ n) : ιz Y a b n = 0 :=
  (dbl Y).ιTotalOrZero_eq_zero _ _ _ _ (by simpa only [ComplexShape.π_def] using h)

theorem dT_eq_zero (a b a' b' : ℕ) (h : a + b ≠ a' + b' + 1) : dT a b a' b' = 0 := by
  unfold dT dH dV
  rw [if_neg (by omega), if_neg (by omega), smul_zero, add_zero]

theorem awF_eq (n : ℕ) :
    awF Y n = ∑ x ∈ antidiagonal n, (ev Y).map (awO n x.1 x.2) ≫ ιz Y x.1 x.2 n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
  unfold awF
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ιz_eq Y _ _ _ (by omega)]

theorem ιz_d (a b k : ℕ) :
    ιz Y a b (k + 1) ≫ (tot Y).d (k + 1) k =
      ∑ x ∈ antidiagonal k, (ev Y).map (dT a b x.1 x.2) ≫ ιz Y x.1 x.2 k := by
  by_cases h : a + b = k + 1
  · rw [ιz_eq Y _ _ _ h, totd' Y a b k h, ← Finset.sum_attach (antidiagonal k)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ιz_eq Y _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 x.2)]
  · rw [ιz_ne Y _ _ _ h, zero_comp]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [dT_eq_zero _ _ _ _ (by omega), Functor.map_zero, zero_comp]

def shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : (tot Y).X n ⟶ (diagCx Y).X n :=
  (dbl Y).totalDesc (c₁₂ := ComplexShape.down ℕ) (fun a b _ => (ev Y).map (G a b n))

theorem ιz_shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ shufF Y G n = (ev Y).map (G a b n) := by
  rw [ιz_eq Y _ _ _ h, shufF, ι_totalDesc]

theorem shufF_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) (n : ℕ) :
    (tot Y).d (n + 1) n ≫ shufF Y G n = shufF Y G (n + 1) ≫ (diagCx Y).d (n + 1) n := by
  refine total.hom_ext (K := dbl Y) (c₁₂ := ComplexShape.down ℕ) (fun a b h => ?_)
  simp only [ComplexShape.π_def] at h
  rw [← ιz_eq Y _ _ _ h, ← Category.assoc, ιz_d, Preadditive.sum_comp, ← Category.assoc, ιz_shufF Y G _ _ _ h,
    ← evd', ← Functor.map_comp, hG a b n h, Functor.map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, ιz_shufF Y G _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), Functor.map_comp]

end GlobalTheory.EZ.AWEq

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

theorem awF_comm (n : ℕ) : awF Y (n + 1) ≫ (tot Y).d (n + 1) n = (diagCx Y).d (n + 1) n ≫ awF Y n := by
  rw [awF_eq, awF_eq, Preadditive.sum_comp, Preadditive.comp_sum, ← evd']
  simp_rw [Category.assoc, ιz_d, Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← Functor.map_comp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [awop' n y.1 y.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hy), Functor.map_sum, Preadditive.sum_comp]

theorem awF_shufF (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) :
    awF Y n ≫ shufF Y G n = (ev Y).map (∑ x ∈ antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n) := by
  rw [awF_eq, Preadditive.sum_comp, Functor.map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Category.assoc, ιz_shufF Y G _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hx), Functor.map_comp]

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp [idc, clampHom]
  exact Nat.le_of_lt_succ j.2

theorem ev_idO_self (a b : ℕ) : (ev Y).map (idO a b a b) = 𝟙 _ := by
  rw [idO, if_pos ⟨rfl, rfl⟩, ev_map_bop, idc_self, idc_self]
  simp
  rfl

theorem sum_idO (a b n : ℕ) (h : a + b = n) :
    ∑ y ∈ antidiagonal n, (ev Y).map (idO a b y.1 y.2) ≫ ιz Y y.1 y.2 n = ιz Y a b n := by
  rw [Finset.sum_eq_single (a, b)]
  · rw [ev_idO_self, Category.id_comp]
  · intro y _ hy
    rw [idO, if_neg (fun h' => hy (Prod.ext h'.1.symm h'.2.symm)), Functor.map_zero, zero_comp]
  · intro hy
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hy

def homD (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (i j : ℕ) : (diagCx Y).X i ⟶ (diagCx Y).X j :=
  if i + 1 = j then (ev Y).map (H i j) else 0

def homT (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (i j : ℕ) : (tot Y).X i ⟶ (tot Y).X j :=
  if i + 1 = j then
    (dbl Y).totalDesc (c₁₂ := ComplexShape.down ℕ)
      (fun a b _ => ∑ x ∈ antidiagonal j, (ev Y).map (K a b x.1 x.2) ≫ ιz Y x.1 x.2 j)
  else 0

theorem ιz_homT (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ homT Y K n (n + 1) =
      ∑ x ∈ antidiagonal (n + 1), (ev Y).map (K a b x.1 x.2) ≫ ιz Y x.1 x.2 (n + 1) := by
  rw [homT, if_pos rfl, ιz_eq Y _ _ _ h, ι_totalDesc]

theorem ιz_dNext (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (a b n : ℕ) (h : a + b = n) :
    ιz Y a b n ≫ dNext n (homT Y K) =
      ∑ x ∈ antidiagonal n, ∑ j ∈ antidiagonal (n - 1),
        (ev Y).map (dT a b j.1 j.2 ≫ K j.1 j.2 x.1 x.2) ≫ ιz Y x.1 x.2 n := by
  cases n with
  | zero =>
    rw [Homotopy.dNext_zero_chainComplex, Limits.comp_zero]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun j hj => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj
    rw [dT_eq_zero _ _ _ _ (by omega), Limits.zero_comp, Functor.map_zero, Limits.zero_comp]
  | succ m =>
    rw [Homotopy.dNext_succ_chainComplex, ← Category.assoc, ιz_d, Preadditive.sum_comp, Nat.add_sub_cancel]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Category.assoc, ιz_homT Y K _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.1 hj), Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Category.assoc, ← Functor.map_comp]

end GlobalTheory.EZ.AWEq

noncomputable section
namespace GlobalTheory.EZ.AWEq

open Finset HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  (Y : SimplicialObject (SimplicialObject C))

def awC : diagCx Y ⟶ tot Y where
  f := awF Y
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact awF_comm Y j

def shufC (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) : tot Y ⟶ diagCx Y where
  f := shufF Y G
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact (shufF_comm Y G hG j).symm

def htpyD (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ n m : ℕ, bo n n ⟶ bo m m)
    (hH : ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
      𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) :
    Homotopy (awC Y ≫ shufC Y G hG) (𝟙 (diagCx Y)) where
  hom := homD Y H
  zero i j hij := if_neg hij
  comm n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Homotopy.prevD_chainComplex]
    change awF Y n ≫ shufF Y G n = _
    rw [awF_shufF, hH n]
    simp only [Functor.map_add, Functor.map_id, Functor.map_comp]
    rw [evd', homD, if_pos rfl, show (ev Y).map (𝟙 (bo n n)) = 𝟙 ((diagCx Y).X n) from (ev Y).map_id _]
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex]
      have : dD 0 (0 - 1) = 0 := by simp [dD]
      rw [this, Functor.map_zero, zero_comp, add_zero]
      abel
    | succ m =>
      rw [Homotopy.dNext_succ_chainComplex, Nat.add_sub_cancel, evd', homD, if_pos rfl]
      abel

def htpyT (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b')
    (hK : ∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') :
    Homotopy (shufC Y G hG ≫ awC Y) (𝟙 (tot Y)) where
  hom := homT Y K
  zero i j hij := if_neg hij
  comm n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, Homotopy.prevD_chainComplex]
    change shufF Y G n ≫ awF Y n = _
    refine total.hom_ext (K := dbl Y) (c₁₂ := ComplexShape.down ℕ) (fun a b h => ?_)
    simp only [ComplexShape.π_def] at h
    rw [← ιz_eq Y _ _ _ h]
    subst h

    rw [← Category.assoc, ιz_shufF Y G _ _ _ rfl, awF_eq, Preadditive.comp_sum]
    simp_rw [← Category.assoc, ← Functor.map_comp]
    rw [Finset.sum_congr rfl fun y hy => by
      rw [hK a b y.1 y.2 (Finset.HasAntidiagonal.mem_antidiagonal.1 hy)]]
    simp_rw [Functor.map_add, Preadditive.add_comp, Finset.sum_add_distrib, sum_idO Y a b _ rfl,
      Functor.map_sum, Preadditive.sum_comp]

    simp only [Preadditive.comp_add, Category.comp_id]
    rw [← Category.assoc, ιz_homT Y K a b _ rfl, Preadditive.sum_comp]
    simp_rw [Category.assoc, ιz_d, Preadditive.comp_sum, ← Category.assoc, ← Functor.map_comp]
    rw [Finset.sum_comm (s := antidiagonal (a + b + 1))]
    rw [ιz_dNext Y K a b _ rfl, show ιz Y a b (a + b) ≫ 𝟙 ((tot Y).X (a + b)) = ιz Y a b (a + b) from Category.comp_id _]
    abel

end GlobalTheory.EZ.AWEq

namespace GlobalTheory.EZ

open GlobalTheory.EZ.AWEq

theorem awHomotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  intro C _ _ _ Y G H K _ hG hH hK
  exact ⟨HomotopyEquiv.mk (awC Y) (shufC Y G hG) (htpyD Y G hG H hH) (htpyT Y G hG K hK), fun _ => rfl⟩

end GlobalTheory.EZ
end
end
end
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (H : ∀ n m : ℕ, bo n n ⟶ bo m m) (K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b'), G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → (∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n = 𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n) → (∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b') → ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  first | (exact @GlobalTheory.EZ.awHomotopyEquiv) | (exact GlobalTheory.EZ.awHomotopyEquiv) | (intros; apply GlobalTheory.EZ.awHomotopyEquiv  <;> assumption)
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.Ext
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

abbrev ext1 (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex (CochainComplex C ℤ) (ComplexShape.down ℕ) where
  X a := (K.X a).extend ComplexShape.embeddingDownNat
  d a b := HomologicalComplex.extendMap (K.d a b) ComplexShape.embeddingDownNat
  shape a b h := by rw [K.shape a b h, HomologicalComplex.extendMap_zero]
  d_comp_d' a b c _ _ := by rw [← HomologicalComplex.extendMap_comp, K.d_comp_d, HomologicalComplex.extendMap_zero]

abbrev ext2 (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (ext1 K).extend ComplexShape.embeddingDownNat

lemma fN (a : ℕ) : ComplexShape.embeddingDownNat.f a = -(a : ℤ) := by simp

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

def kX {p q : ℤ} {a b : ℕ}
    (ha : ComplexShape.embeddingDownNat.f a = p) (hb : ComplexShape.embeddingDownNat.f b = q) :
    ((ext2 K).X p).X q ≅ (K.X a).X b :=
  (HomologicalComplex.eval _ _ q).mapIso (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat ha) ≪≫
    HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat hb

lemma isZero_ext_of_pos {p q : ℤ} (h : 0 < p ∨ 0 < q) : IsZero (((ext2 K).X p).X q) := by
  rcases le_or_gt p 0 with hp | hp
  · have hq : 0 < q := by omega
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ q).mapIso
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) (fN a)))
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)
  · exact (HomologicalComplex.eval _ _ q).map_isZero
      (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega))

abbrev kN (a b : ℕ) : ((ext2 K).X (-(a : ℤ))).X (-(b : ℤ)) ≅ (K.X a).X b :=
  kX K (p := -(a : ℤ)) (q := -(b : ℤ)) (a := a) (b := b) (fN a) (fN b)

lemma kN_hom (a b : ℕ) :
    (kN K a b).hom = (HomologicalComplex.extendXIso
      (ext1 K)
      ComplexShape.embeddingDownNat (i := a) (i' := -(a : ℤ)) (fN _)).hom.f (-(b : ℤ)) ≫
      (HomologicalComplex.extendXIso (K.X a) ComplexShape.embeddingDownNat (i := b) (i' := -(b : ℤ)) (fN _)).hom := rfl

lemma kX_d₁ (a b : ℕ) :
    ((ext2 K).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (-(b : ℤ)) ≫ (kN K a b).hom =
      (kN K (a + 1) b).hom ≫ (K.d (a + 1) a).f b := by
  have h := HomologicalComplex.extend_d_eq
    (ext1 K)
    ComplexShape.embeddingDownNat (i := a + 1) (j := a) (i' := -((a + 1 : ℕ) : ℤ)) (j' := -(a : ℤ)) (fN _) (fN _)
  have hh := HomologicalComplex.extendMap_f (K.d (a + 1) a) ComplexShape.embeddingDownNat (i := b) (i' := -(b:ℤ)) (fN _)
  rw [h, kN_hom, kN_hom]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have e1 : ∀ {A B : CochainComplex C ℤ} (φ : A ≅ B) (n : ℤ), φ.inv.f n ≫ φ.hom.f n = 𝟙 _ := fun φ n => by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [reassoc_of% (e1 _ (-(b : ℤ)))]
  rw [hh]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma kX_d₂ (a b : ℕ) :
    ((ext2 K).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) ≫ (kN K a b).hom =
      (kN K a (b + 1)).hom ≫ (K.X a).d (b + 1) b := by
  have := HomologicalComplex.Hom.comm (HomologicalComplex.extendXIso
    (ext1 K)
    ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) (fN _)).hom (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ))
  have h2 := HomologicalComplex.extend_d_eq (K.X a) ComplexShape.embeddingDownNat (i := b + 1) (j := b)
    (i' := -((b + 1 : ℕ) : ℤ)) (j' := -(b : ℤ)) (fN _) (fN _)
  rw [kN_hom, kN_hom]
  have e := this =≫ (HomologicalComplex.extendXIso (K.X a) ComplexShape.embeddingDownNat (i := b) (i' := -(b:ℤ)) (fN _)).hom
  simp only [Category.assoc] at e
  rw [← e, h2]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Tot
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

def cmp {p q n : ℤ} (a b m : ℕ) (ha : ComplexShape.embeddingDownNat.f a = p)
    (hb : ComplexShape.embeddingDownNat.f b = q) (hm : ComplexShape.embeddingDownNat.f m = n)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b) = m) :
    ((ext2 K).X p).X q ⟶ ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n :=
  (kX K ha hb).hom ≫ K.ιTotal (ComplexShape.down ℕ) a b m h ≫
    ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat hm).inv

lemma cmp_congr {p q n : ℤ} (a b m a' b' m' : ℕ) (ha : ComplexShape.embeddingDownNat.f a = p)
    (hb : ComplexShape.embeddingDownNat.f b = q) (hm : ComplexShape.embeddingDownNat.f m = n)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b) = m)
    (ha' : ComplexShape.embeddingDownNat.f a' = p)
    (hb' : ComplexShape.embeddingDownNat.f b' = q) (hm' : ComplexShape.embeddingDownNat.f m' = n)
    (h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a', b') = m') :
    cmp K a b m ha hb hm h = cmp K a' b' m' ha' hb' hm' h' := by
  obtain rfl : a = a' := ComplexShape.embeddingDownNat.injective_f (ha.trans ha'.symm)
  obtain rfl : b = b' := ComplexShape.embeddingDownNat.injective_f (hb.trans hb'.symm)
  obtain rfl : m = m' := ComplexShape.embeddingDownNat.injective_f (hm.trans hm'.symm)
  rfl

def homF (n : ℤ) : ((ext2 K).total (ComplexShape.up ℤ)).X n ⟶
    ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n :=
  (ext2 K).totalDesc (fun p q h =>
    if hpq : p ≤ 0 ∧ q ≤ 0 then
      cmp K (-p).toNat (-q).toNat (-n).toNat (by simp; omega) (by simp; omega)
        (by simp only [ComplexShape.π_def] at h; simp; omega)
        (by simp only [ComplexShape.π_def] at h ⊢; omega)
    else 0)

lemma ι_homF (a b m : ℕ) (h : a + b = m) :
    (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(m : ℤ)) (by simp only [ComplexShape.π_def]; omega) ≫
      homF K (-(m : ℤ)) =
    (kN K a b).hom ≫ K.ιTotal (ComplexShape.down ℕ) a b m h ≫
      ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv := by
  rw [homF, HomologicalComplex₂.ι_totalDesc, dif_pos (by omega)]
  exact cmp_congr K _ _ _ a b m _ _ _ _ (fN a) (fN b) (fN m) h

def invC {n : ℤ} (m : ℕ) (hm : ComplexShape.embeddingDownNat.f m = n) :
    ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n ⟶
      ((ext2 K).total (ComplexShape.up ℤ)).X n :=
  ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat hm).hom ≫
    K.totalDesc (fun a b h => (kN K a b).inv ≫ (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) n
      (by simp only [ComplexShape.π_def] at h ⊢; simp at hm; omega))

lemma invC_congr {n : ℤ} (m m' : ℕ) (hm : ComplexShape.embeddingDownNat.f m = n)
    (hm' : ComplexShape.embeddingDownNat.f m' = n) : invC K m hm = invC K m' hm' := by
  obtain rfl : m = m' := ComplexShape.embeddingDownNat.injective_f (hm.trans hm'.symm)
  rfl

def invF (n : ℤ) : ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).X n ⟶
    ((ext2 K).total (ComplexShape.up ℤ)).X n :=
  if hn : n ≤ 0 then invC K (-n).toNat (by simp; omega) else 0

lemma ι_invF (a b m : ℕ) (h : a + b = m) :
    K.ιTotal (ComplexShape.down ℕ) a b m h ≫
      ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv ≫ invF K (-(m : ℤ)) =
    (kN K a b).inv ≫ (ext2 K).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(m : ℤ))
      (by simp only [ComplexShape.π_def]; omega) := by
  rw [invF, dif_pos (by omega), invC_congr K _ m _ (fN m), invC, Iso.inv_hom_id_assoc,
    HomologicalComplex₂.ι_totalDesc]

end Tot

section Tot2
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

lemma homF_invF (n : ℤ) : homF K n ≫ invF K n = 𝟙 _ := by
  ext p q h
  by_cases hpq : p ≤ 0 ∧ q ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, q = -(b:ℤ) := ⟨(-q).toNat, by omega⟩
    obtain rfl : n = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at h; omega
    rw [reassoc_of% (ι_homF K a b (a + b) rfl), ι_invF K a b (a + b) rfl,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · exact (isZero_ext_of_pos K (by omega)).eq_of_src _ _

lemma invF_homF (n : ℤ) : invF K n ≫ homF K n = 𝟙 _ := by
  by_cases hn : n ≤ 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m:ℤ) := ⟨(-n).toNat, by omega⟩
    rw [← cancel_epi ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN m)).inv]
    ext a b h
    rw [reassoc_of% (ι_invF K a b m h), ι_homF K a b m h, Iso.inv_hom_id_assoc, Category.comp_id]
  · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)).eq_of_src _ _

lemma negOnePow_negNat (a : ℕ) : (-(a : ℤ)).negOnePow = (-1 : ℤˣ) ^ a := by
  rw [Int.negOnePow_neg, Int.negOnePow_def, zpow_natCast]

lemma homF_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    homF K i ≫ ((K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat).d i j =
      ((ext2 K).total (ComplexShape.up ℤ)).d i j ≫ homF K j := by
  change i + 1 = j at hij
  ext p q h
  by_cases hpq : p ≤ 0 ∧ q ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a:ℤ) := ⟨(-p).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, q = -(b:ℤ) := ⟨(-q).toNat, by omega⟩
    obtain rfl : i = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at h; omega
    rcases Nat.eq_zero_or_pos (a + b) with hab | hab
    · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by simp at hi; omega)).eq_of_tgt _ _
    obtain ⟨k, hk⟩ : ∃ k, a + b = k + 1 := ⟨a + b - 1, by omega⟩
    obtain rfl : j = -(k : ℤ) := by omega
    rw [reassoc_of% (ι_homF K a b (a + b) rfl),
      HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat (i := a + b) (j := k) (fN _) (fN _),
      Iso.inv_hom_id_assoc]
    simp only [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
    have hd₁ : (kN K a b).hom ≫ K.d₁ (ComplexShape.down ℕ) a b k ≫
        ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN k)).inv =
        (ext2 K).d₁ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(k : ℤ)) ≫ homF K (-(k : ℤ)) := by
      rcases a with _ | a'
      · rw [K.d₁_eq_zero _ _ _ _ (by intro hr; change _ + 1 = 0 at hr; omega),
          (ext2 K).d₁_eq' _ (i₁' := 1) (by simp only [ComplexShape.up_Rel]; omega) _ _,
          (isZero_ext_of_pos K (p := 1) (q := -(b:ℤ)) (Or.inl one_pos)).eq_of_src
            ((ext2 K).ιTotalOrZero (ComplexShape.up ℤ) 1 (-(b : ℤ)) (-(k : ℤ))) 0]
        simp
      · rw [K.d₁_eq _ (i₁' := a') rfl _ _ (by simp only [ComplexShape.π_def]; omega),
          (ext2 K).d₁_eq _ (i₁' := -(a' : ℤ)) (by simp only [ComplexShape.up_Rel]; omega) _ _
            (by simp only [ComplexShape.π_def]; omega)]
        have e1 : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a' + 1, b) = 1 := rfl
        have e2 : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (-((a' + 1 : ℕ) : ℤ), -(b : ℤ)) = 1 := rfl
        rw [e1, e2, one_smul, one_smul, Category.assoc, Category.assoc, ι_homF K a' b k (by omega),
          reassoc_of% (kX_d₁ K a' b)]
    have hd₂ : (kN K a b).hom ≫ K.d₂ (ComplexShape.down ℕ) a b k ≫
        ((K.total (ComplexShape.down ℕ)).extendXIso ComplexShape.embeddingDownNat (fN k)).inv =
        (ext2 K).d₂ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) (-(k : ℤ)) ≫ homF K (-(k : ℤ)) := by
      rcases b with _ | b'
      · rw [K.d₂_eq_zero _ _ _ _ (by intro hr; change _ + 1 = 0 at hr; omega),
          (ext2 K).d₂_eq' _ _ (i₂' := 1) (by simp only [ComplexShape.up_Rel]; omega) _,
          (isZero_ext_of_pos K (p := -(a : ℤ)) (q := 1) (Or.inr one_pos)).eq_of_src
            ((ext2 K).ιTotalOrZero (ComplexShape.up ℤ) (-(a : ℤ)) 1 (-(k : ℤ))) 0]
        simp
      · rw [K.d₂_eq _ _ (i₂' := b') rfl _ (by simp only [ComplexShape.π_def]; omega),
          (ext2 K).d₂_eq _ _ (i₂' := -(b' : ℤ)) (by simp only [ComplexShape.up_Rel]; omega) _
            (by simp only [ComplexShape.π_def]; omega)]
        have e1 : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (a, b' + 1) =
          (-1 : ℤˣ) ^ a := rfl
        have e2 : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (-(a : ℤ), -((b' + 1 : ℕ) : ℤ)) = (-(a : ℤ)).negOnePow := rfl
        rw [e1, e2, negOnePow_negNat, Linear.units_smul_comp, Linear.units_smul_comp, Linear.comp_units_smul,
          Category.assoc, Category.assoc, ι_homF K a b' k (by omega), reassoc_of% (kX_d₂ K a b')]
    rw [hd₁, hd₂]
  · exact (isZero_ext_of_pos K (by omega)).eq_of_src _ _

end Tot2

section Tot3
variable [K.HasTotal (ComplexShape.down ℕ)] [(ext2 K).HasTotal (ComplexShape.up ℤ)]

def totIso : (ext2 K).total (ComplexShape.up ℤ) ≅ (K.total (ComplexShape.down ℕ)).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (fun n => ⟨homF K n, invF K n, homF_invF K n, invF_homF K n⟩)
    (fun i j h => homF_comm K i j h)

lemma totIso_inv_f (n : ℤ) : (totIso K).inv.f n = invF K n := rfl

end Tot3

def extHE {A B : ChainComplex C ℕ} (e : HomotopyEquiv A B) :
    HomotopyEquiv (A.extend ComplexShape.embeddingDownNat) (B.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat
  inv := HomologicalComplex.extendMap e.inv ComplexShape.embeddingDownNat
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((e.homotopyHomInvId.extend ComplexShape.embeddingDownNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((e.homotopyInvHomId.extend ComplexShape.embeddingDownNat).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

section Sheaves
open GlobalTheory.EtC
variable (R : Type) [CommRing R]

def diagSIso (X : SimplicialObject Spc) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (bidiag.obj X) ≅ GlobalTheory.EZ.diag.obj ((freeBi R).obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact ((free R).map_comp _ _))

def diagIso (X : SimplicialObject Spc) :
    (chains R).obj (bidiag.obj X) ≅ (diagCx ((freeBi R).obj X)).extend ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.extendFunctor _).mapIso ((alternatingFaceMapComplex _).mapIso (diagSIso R X))

set_option backward.isDefEq.respectTransparency false in
lemma diagIso_hom_f (X : SimplicialObject Spc) (n : ℕ) :
    (diagIso R X).hom.f (-(n : ℤ)) = (chainsXIso R (bidiag.obj X) n).hom ≫
      ((diagCx ((freeBi R).obj X)).extendXIso ComplexShape.embeddingDownNat (fN n)).inv := by
  change (HomologicalComplex.extendMap ((alternatingFaceMapComplex _).map (diagSIso R X).hom)
    ComplexShape.embeddingDownNat).f (-(n:ℤ)) = _
  rw [HomologicalComplex.extendMap_f _ _ (fN n)]
  have h1 : ((alternatingFaceMapComplex (Shv R)).map (diagSIso R X).hom).f n = 𝟙 _ := by
    rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]; rfl
  rw [h1, Category.id_comp]
  rfl

lemma ev_awO (X : SimplicialObject Spc) (n a : ℕ) (ha : a ≤ n) :
    (ev ((freeBi R).obj X)).map (awO n a (n - a)) = (free R).map (awP X n a (n - a)) := by
  rw [awO, if_pos (by omega), ev_map_bop, awP]
  exact ((free R).map_comp _ _).symm

end Sheaves

set_option backward.isDefEq.respectTransparency false in

theorem homotopyEquiv_chains_totChains : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  intro R _ X ⟨e, he⟩
  haveI : (ext2 (dbl ((freeBi R).obj X))).HasTotal (ComplexShape.up ℤ) := hasTotal_biChains R X
  refine ⟨(HomotopyEquiv.ofIso (diagIso R X)).trans ((extHE e).trans
    (HomotopyEquiv.ofIso (totIso (dbl ((freeBi R).obj X))).symm)), fun n => ?_⟩
  change (diagIso R X).hom.f (-(n:ℤ)) ≫ (HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat).f (-(n:ℤ)) ≫
    (totIso (dbl ((freeBi R).obj X))).inv.f (-(n:ℤ)) = _
  rw [diagIso_hom_f, HomologicalComplex.extendMap_f _ _ (fN n), he n, totIso_inv_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [awZ, awF]
  congr 1
  simp only [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := ι_invF (dbl ((freeBi R).obj X)) (a : ℕ) (n - a) n (by omega)
  rw [Category.assoc, ev_awO R X n a (by omega)]
  exact (congrArg ((GlobalTheory.EtC.free R).map (awP X n a (n - a)) ≫ ·) h).trans rfl
end Ext
end EZ
end GlobalTheory
end
end

section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eilenberg_zilber_homotopy_equivalence : ∀ (R : Type) [CommRing R] (X : SimplicialObject GlobalTheory.EtC.Spc), (∃ e : HomotopyEquiv (diagCx ((freeBi R).obj X)) (tot ((freeBi R).obj X)), ∀ n : ℕ, e.hom.f n = awF _ n) → ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X), ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n := by
  first | (exact @GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (exact GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains) | (intros; apply GlobalTheory.EZ.Ext.homotopyEquiv_chains_totChains <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ
universe u v

theorem ez_nat {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (Y : SimplicialObject (SimplicialObject C)) :
    ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  obtain ⟨G, h0, hG⟩ := GlobalTheory.T.exists_bisimplicial_shuffle_operators
  obtain ⟨H, hH⟩ := GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id G h0 hG
  obtain ⟨K, hK⟩ := GlobalTheory.T.alexander_whitney_homotopy_formula G h0 hG
  exact GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv Y G H K h0 hG hH hK

variable (R : Type) [CommRing R]

theorem ez (X : SimplicialObject GlobalTheory.EtC.Spc) :
    ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X),
      ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n :=
  GlobalTheory.T.eilenberg_zilber_homotopy_equivalence R X (ez_nat _)

def ezEquiv (X : SimplicialObject GlobalTheory.EtC.Spc) :
    HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X) := (ez R X).choose

def awChains (X : SimplicialObject GlobalTheory.EtC.Spc) : (GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X) ⟶ totChains R X :=
  (ezEquiv R X).hom

theorem awChains_f (X : SimplicialObject GlobalTheory.EtC.Spc) (n : ℕ) : (awChains R X).f (-(n : ℤ)) = awZ R X n :=
  (ez R X).choose_spec n

theorem pull_awChains_bijective (X : SimplicialObject GlobalTheory.EtC.Spc) (I : GlobalTheory.EtC.Cx R) (k : ℤ) :
    Function.Bijective (GlobalTheory.EtC.cpull (awChains R X) I k) :=
  GlobalTheory.EtC.LevelCmp.cpull_bij_of_heq (ezEquiv R X) I k

end GlobalTheory.EZ
end
end
