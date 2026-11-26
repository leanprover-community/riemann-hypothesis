module

public import Lib.Base

/-!
# Few translates span almost everything

The spread condition bounds the dimension of the preimage of a subspace under one
map in a family. A greedy choice then constructs a small subfamily whose images
span almost the whole target. The Hilbert--Schmidt second-moment criterion for the
condition is proved in the sibling module `HilbertSchmidt`.

## Relation to the literature

Greedy covering with a logarithmic loss: Wolsey, Greedy algorithm for the submodular
set covering problem, 1982.
-/

@[expose] public section

open Module LinearMap Finset

namespace New

section Spread

open Submodule

variable {Θ V : Type} [AddCommGroup V] [Module ℂ V]

/-- The maps `B s` spread: for every subspace `F` of `W`, with share `α` of the dimension, the
preimage of `F` under one of them has dimension at most `((1 + α) / 2 + η) dim V`. The share is the
quotient of the two values of `finrank`, so it is `0` if `finrank W = 0`. -/
def IsSpread {W : Type*} [AddCommMonoid W] [Module ℂ W] (B : Θ → V →ₗ[ℂ] W) (η : ℝ) : Prop :=
  ∀ F : Submodule ℂ W, let α : ℝ := finrank ℂ F / finrank ℂ W
  ∃ s : Θ, finrank ℂ (comap (B s) F) ≤ ((1 + α) / 2 + η) * finrank ℂ V

end Spread

section FewTranslates

open Submodule Real

variable {Θ V W : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]

/-- The image of `A` adds `dim V - dim A⁻¹ F` dimensions to `F`. -/
lemma finrank_sup_range_add_finrank_comap (A : V →ₗ[ℂ] W) (F : Submodule ℂ W) :
    finrank ℂ ↥(F ⊔ range A) + finrank ℂ (F.comap A) = finrank ℂ F + finrank ℂ V := by
  have h_comap : finrank ℂ ↥(F ⊓ range A) + finrank ℂ (ker A) = finrank ℂ (F.comap A) := by
    rw [← (A.domRestrict (F.comap A)).finrank_range_add_finrank_ker, range_domRestrict,
      map_comap_eq, inf_comm, ker_domRestrict,
      (comapSubtypeEquivOfLe (ker_le_comap A : ker A ≤ F.comap A)).finrank_eq]
  have h_sup := finrank_sup_add_finrank_inf_eq F (range A)
  linarith [A.finrank_range_add_finrank_ker]

variable {B : Θ → V →ₗ[ℂ] W} {ε : ℝ}

/-- One step of the greedy choice. Let `W` be nonzero and suppose that the maps `B s` spread with
the error `3 ε / 2`. If `F` misses more than a share `16 ε` of the dimensions of `W`, then adding
some image `range (B s)` to `F` multiplies the codimension by at most `1 - 2 dim V / (5 dim W)`. -/
lemma IsSpread.exists_codim_le (h_spread : IsSpread B (3 / 2 * ε)) (F : Submodule ℂ W)
    (hW : 0 < finrank ℂ W) (hF : 16 * ε * finrank ℂ W < (finrank ℂ W - finrank ℂ F : ℝ)) :
    ∃ s : Θ, (finrank ℂ W - finrank ℂ ↥(F ⊔ range (B s)) : ℝ) ≤
      (1 - 2 * finrank ℂ V / (5 * finrank ℂ W)) * (finrank ℂ W - finrank ℂ F) := by
  obtain ⟨s, hs⟩ := h_spread F
  refine ⟨s, ?_⟩
  have hW' : (0 : ℝ) < finrank ℂ W := by exact_mod_cast hW
  set α : ℝ := finrank ℂ F / finrank ℂ W
  have hα : (finrank ℂ F : ℝ) = α * finrank ℂ W := (div_mul_cancel₀ _ hW'.ne').symm
  have hα_le : α ≤ 1 := (div_le_one hW').2 (by exact_mod_cast F.finrank_le)
  have h_share : 16 * ε < 1 - α := lt_of_mul_lt_mul_right (by linarith) hW'.le
  have h_added : (finrank ℂ ↥(F ⊔ range (B s)) : ℝ) + finrank ℂ (F.comap (B s)) =
      finrank ℂ F + finrank ℂ V := by exact_mod_cast finrank_sup_range_add_finrank_comap (B s) F
  -- The image adds at least `(1/2 - 3/32) (1 - α) dim V ≥ (2/5) (1 - α) dim V` dimensions.
  have h_gain : ((1 + α) / 2 + 3 / 2 * ε) * finrank ℂ V ≤ (1 - 2 / 5 * (1 - α)) * finrank ℂ V := by
    gcongr
    linarith
  have h_factor : (1 - 2 * finrank ℂ V / (5 * finrank ℂ W)) * (finrank ℂ W - finrank ℂ F : ℝ) =
      finrank ℂ W - finrank ℂ F - 2 / 5 * (1 - α) * finrank ℂ V := by
    rw [hα]
    field
  rw [h_factor]
  linarith

/-- The greedy choice after `l` steps. Let `W` be nonzero and let the maps `B s : V → W` spread with
the error `3 ε / 2`. Then the span of the images of at most `l` of them misses at most a share
`max (16 ε) (exp (-l rate))` of the dimensions of `W`, where `rate = 2 dim V / (5 dim W)`: each step
removes at least that share of what is missing. -/
lemma IsSpread.exists_codim_le_max (h_spread : IsSpread B (3 / 2 * ε)) (hW : 0 < finrank ℂ W)
    (l : ℕ) :
    ∃ t : Finset Θ, #t ≤ l ∧ (finrank ℂ W - finrank ℂ ↥(⨆ s ∈ t, range (B s)) : ℝ) ≤
      max (16 * ε) (exp (-(l * (2 * finrank ℂ V / (5 * finrank ℂ W))))) * finrank ℂ W := by
  classical
  have hW' : (0 : ℝ) < finrank ℂ W := by exact_mod_cast hW
  set rate : ℝ := 2 * finrank ℂ V / (5 * finrank ℂ W)
  let codim (t : Finset Θ) : ℝ := finrank ℂ W - finrank ℂ ↥(⨆ s ∈ t, range (B s))
  change ∃ t : Finset Θ, #t ≤ l ∧ codim t ≤ max (16 * ε) (exp (-(l * rate))) * finrank ℂ W
  induction l with
  | zero =>
    refine ⟨∅, le_rfl, ?_⟩
    calc codim ∅ ≤ finrank ℂ W := sub_le_self _ (Nat.cast_nonneg _)
      _ ≤ max (16 * ε) (exp (-((0 : ℕ) * rate))) * finrank ℂ W :=
          le_mul_of_one_le_left hW'.le (le_max_of_le_right (by simp))
  | succ l ih =>
    obtain ⟨t, h_card, h_codim⟩ := ih
    obtain h_done | h_more := le_or_gt (codim t) (16 * ε * finrank ℂ W)
    · exact ⟨t, h_card.trans l.le_succ,
        h_done.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW'.le)⟩
    obtain ⟨s, h_step⟩ := h_spread.exists_codim_le _ hW h_more
    have h_exp : codim t ≤ exp (-(l * rate)) * finrank ℂ W := by
      rw [max_mul_of_nonneg _ _ hW'.le, le_max_iff] at h_codim
      exact h_codim.resolve_left h_more.not_ge
    refine ⟨insert s t, (card_insert_le s t).trans (by omega), ?_⟩
    have h_insert : ⨆ i ∈ insert s t, range (B i) = (⨆ i ∈ t, range (B i)) ⊔ range (B s) := by
      rw [Finset.iSup_insert, sup_comm]
    calc codim (insert s t)
        ≤ (1 - rate) * codim t := by rwa [← h_insert] at h_step
      _ ≤ exp (-rate) * (exp (-(l * rate)) * finrank ℂ W) := by
          gcongr
          · exact sub_nonneg.2 (by exact_mod_cast Submodule.finrank_le _)
          · exact one_sub_le_exp_neg rate
      _ = exp (-((l + 1 : ℕ) * rate)) * finrank ℂ W := by
          rw [← mul_assoc, ← exp_add]
          push_cast
          ring_nf
      _ ≤ max (16 * ε) (exp (-((l + 1 : ℕ) * rate))) * finrank ℂ W :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hW'.le

/-- **Few maps span almost everything.** Let `V` and `W` be nonzero finite-dimensional spaces, let
`0 < ε < 1 / 16`, and let the maps `B s : V → W` spread with the error `3 ε / 2`. Then the images of
at most `(5/2) (1 + log (1 / (16 ε))) dim W / dim V` of them span a subspace of dimension at least
`(1 - 16 ε) dim W`. -/
theorem IsSpread.exists_few_le_finrank_iSup_range [Nontrivial V] (h_spread : IsSpread B (3 / 2 * ε))
    (hW : 0 < finrank ℂ W) (hε : 0 < ε) (hε_lt : ε < 1 / 16) :
    ∃ t : Finset Θ,
      #t * finrank ℂ V ≤ 5 / 2 * (1 + log (16 * ε)⁻¹) * finrank ℂ W ∧
      (1 - 16 * ε) * finrank ℂ W ≤ finrank ℂ ↥(⨆ s ∈ t, range (B s)) := by
  -- Choose the maps greedily. While more than a share `16 ε` is missing, each step multiplies the
  -- missing share by at most `1 - rate ≤ exp (-rate)`; about `log (1 / (16 ε)) / rate` steps do.
  have hW' : (0 : ℝ) < finrank ℂ W := by exact_mod_cast hW
  have hV : (0 : ℝ) < finrank ℂ V := by exact_mod_cast finrank_pos
  set rate : ℝ := 2 * finrank ℂ V / (5 * finrank ℂ W) with h_rate
  have h_rate_pos : 0 < rate := by positivity
  -- The first step shows `rate ≤ 1`.
  have h_rate_le : rate ≤ 1 := by
    have h_start : 16 * ε * finrank ℂ W < finrank ℂ W - finrank ℂ (⊥ : Submodule ℂ W) := by
      simpa using mul_lt_of_lt_one_left hW' (by linarith : 16 * ε < 1)
    obtain ⟨s, h_step⟩ := h_spread.exists_codim_le ⊥ hW h_start
    have h_codim_nonneg : (0 : ℝ) ≤ finrank ℂ W - finrank ℂ ↥(⊥ ⊔ range (B s)) :=
      sub_nonneg.2 (by exact_mod_cast Submodule.finrank_le _)
    have h_nonneg : 0 ≤ (1 - rate) * finrank ℂ W := by simpa using h_codim_nonneg.trans h_step
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_left h_nonneg hW')
  -- Stop at the least `l` with `l rate ≥ log (1 / (16 ε))`; then `l rate ≤ 1 + log (1 / (16 ε))`.
  have h_log : 0 ≤ log (16 * ε)⁻¹ :=
    log_nonneg ((one_le_inv₀ (by positivity)).2 (by linarith))
  set l : ℕ := ⌈log (16 * ε)⁻¹ / rate⌉₊
  have hl_ge : log (16 * ε)⁻¹ ≤ l * rate := (div_le_iff₀ h_rate_pos).1 (Nat.le_ceil _)
  have hl_le : l * rate ≤ 1 + log (16 * ε)⁻¹ :=
    calc l * rate ≤ (log (16 * ε)⁻¹ / rate + 1) * rate := by
          gcongr
          exact (Nat.ceil_lt_add_one (by positivity)).le
      _ = rate + log (16 * ε)⁻¹ := by field
      _ ≤ 1 + log (16 * ε)⁻¹ := by gcongr
  obtain ⟨t, h_card, h_codim⟩ : ∃ t : Finset Θ, #t ≤ l ∧
      (finrank ℂ W - finrank ℂ ↥(⨆ s ∈ t, range (B s)) : ℝ) ≤
        max (16 * ε) (exp (-(l * rate))) * finrank ℂ W := h_spread.exists_codim_le_max hW l
  have h_exp : exp (-(l * rate)) ≤ 16 * ε := by
    rwa [← le_log_iff_exp_le (by positivity), _root_.neg_le, ← log_inv]
  rw [max_eq_left h_exp] at h_codim
  refine ⟨t, ?_, by linarith⟩
  calc (#t * finrank ℂ V : ℝ) ≤ l * finrank ℂ V := by gcongr
    _ = 5 / 2 * (l * rate) * finrank ℂ W := by rw [h_rate]; field
    _ ≤ 5 / 2 * (1 + log (16 * ε)⁻¹) * finrank ℂ W := by gcongr

/-- The images of a subspace `C` under `#t` maps span at most `#t dim C` dimensions. -/
lemma finrank_biSup_map_le (B : Θ → V →ₗ[ℂ] W) (t : Finset Θ) (C : Submodule ℂ V) :
    finrank ℂ ↥(⨆ s ∈ t, C.map (B s)) ≤ #t * finrank ℂ C := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert s t hs ih =>
    rw [t.iSup_insert, card_insert_of_notMem hs]
    calc finrank ℂ ↥(C.map (B s) ⊔ ⨆ s ∈ t, C.map (B s))
        ≤ finrank ℂ (C.map (B s)) + finrank ℂ ↥(⨆ s ∈ t, C.map (B s)) :=
          finrank_add_le_finrank_add_finrank _ _
      _ ≤ finrank ℂ C + #t * finrank ℂ C := add_le_add (finrank_map_le (B s) C) ih
      _ = (#t + 1) * finrank ℂ C := by ring

/-- Restricting finitely many maps to a subspace `U` lowers the dimension of the span of their
images by at most the codimension of `U` for each map. -/
lemma finrank_biSup_range_le (B : Θ → V →ₗ[ℂ] W) (t : Finset Θ) (U : Submodule ℂ V) :
    finrank ℂ ↥(⨆ s ∈ t, (B s).range) ≤
      finrank ℂ ↥(⨆ s ∈ t, U.map (B s)) + #t * (finrank ℂ V - finrank ℂ U : ℝ) := by
  obtain ⟨C, hC⟩ : ∃ C : Submodule ℂ V, IsCompl U C := U.exists_isCompl
  have h_dim : (finrank ℂ V - finrank ℂ U : ℝ) = finrank ℂ C := by
    rw [← finrank_add_eq_of_isCompl hC, Nat.cast_add, add_sub_cancel_left]
  have h_split : ⨆ s ∈ t, (B s).range = (⨆ s ∈ t, U.map (B s)) ⊔ ⨆ s ∈ t, C.map (B s) := by
    simp only [← iSup_sup_eq, ← Submodule.map_sup, hC.sup_eq_top, Submodule.map_top]
  rw [h_dim, h_split]
  exact_mod_cast (finrank_add_le_finrank_add_finrank _ _).trans
    (add_le_add_right (finrank_biSup_map_le B t C) _)

end FewTranslates

end New
