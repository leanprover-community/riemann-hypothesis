module

public import TauCeti.Analysis.InnerProductSpace.ArrowTriangle
public import New.UpperBound.Objects.RowChain

/-!
# Orders of block triangular groups and commutation along chains

The group `New.parabolic (New.blockNumber j)` consists of the invertible block upper triangular
matrices whose diagonal blocks are one copy of `N` and `j` copies of `T`. Its order is
`#GL N R * (#GL T R) ^ j` times a power of `#R` whose exponent does not depend on the commutative
ring `R`.

An abstract triangle of spaces `F i n` has arrows `a t i n : F i n → F i (n + 1)` along row `i` and
`d t i n : F i (n + 1) → F (i + 1) n` down to the next row. The map `j i` embeds `V` in `F i 0`. The
arrows depend on a parameter `t : I`. An abstract relation `M c f` between functions `c : I → ℂ` and
`f : I → ℝ`, unital and multiplicative, is read "`c` has modulus `f`". For nonzero weights, weighted
chains along a row are injective on `V`. If the constants of the squares have prescribed moduli
`L r k`, the squares obey an adjoint law and the Gram forms of the first arrows are given, then the
Gram form of a full chain and the modulus of its constant follow from Tau Ceti's arrow triangle
theorems, used directly in `ChainNorms` with group orders as real weights. In the application
`F i n` is attached to the interval `[i + 1, i + n]`, the arrow `a` adds the greatest element,
and `d` stands for the adjoint of the map that adds the least element.

## Main definitions and results

* `New.exists_card_parabolic_blockNumber_eq`: the order of the group of block triangular matrices
  `New.parabolic (New.blockNumber j)`.
* `New.Exchange.exists_modulus_chainCommutes`: square moduli and nonzero weights suffice for
  commutation along a chain, without the remaining triangle axioms.

The triangle, weighted chain and Gram form theorems are in
`TauCeti.Analysis.InnerProductSpace.ArrowTriangle`.

Notions from other files:
* `New.BlockIndex N T j`, `New.blockNumber j`: the disjoint union of `N` and `j` copies of `T`, and
  the number of the block of an index (`0` on `N`, and `l` on the `l`-th copy of `T`).
* `New.compUpTo L j`: for linear maps `L i : M i → M (i + 1)`, the composite
  `L (j - 1) ∘ ⋯ ∘ L 0 : M 0 → M j`.
-/

@[expose] public section

/-! ## Order of a group of block triangular matrices -/

namespace New

open Matrix Fintype

variable {N T : Type}

/-- A matrix indexed by `BlockIndex N T (j + 1) = BlockIndex N T j ⊕ T`, the union of `N` and
`j + 1` copies of `T`, is block upper triangular for the numbering `blockNumber` of the blocks
exactly when its upper left corner is block upper triangular and its lower left corner vanishes. -/
lemma blockTriangular_fromBlocks_blockNumber_succ_iff {R : Type*} [Zero R] {j : ℕ}
    {A : Matrix (BlockIndex N T j) (BlockIndex N T j) R} {B : Matrix (BlockIndex N T j) T R}
    {C : Matrix T (BlockIndex N T j) R} {D : Matrix T T R} :
    (fromBlocks A B C D).BlockTriangular (blockNumber (R := N) (T := T) (j + 1)) ↔
      A.BlockTriangular (blockNumber (R := N) (T := T) j) ∧ C = 0 := by
  refine ⟨fun h ↦ ⟨fun a b hlt ↦ h (i := .inl a) (j := .inl b) (by simpa [blockNumber] using hlt),
    Matrix.ext fun a b ↦ h (i := .inr a) (j := .inl b) (by simp [blockNumber])⟩, ?_⟩
  rintro ⟨hA, rfl⟩ (a | a) (b | b) hlt
  · exact hA (by simpa [blockNumber] using hlt)
  · simp [blockNumber, ← Fin.top_eq_last] at hlt
  · simp
  · simp [blockNumber] at hlt

variable (N T) [Fintype N] [Fintype T] [DecidableEq T] [DecidableEq N]

/-- An invertible block upper triangular matrix with blocks `N` and `j + 1` copies of `T` is a
triple: such a matrix with `j` copies of `T`, an arbitrary upper right block and an invertible last
diagonal block. Hence the orders multiply. -/
lemma card_parabolic_blockNumber_succ (R : Type*) [CommRing R] (j : ℕ) :
    Nat.card (parabolic (R := R) (blockNumber (R := N) (T := T) (j + 1))) =
      Nat.card (parabolic (R := R) (blockNumber (R := N) (T := T) j)) *
        (Nat.card (Matrix (BlockIndex N T j) T R) * Nat.card (GL T R)) := by
  let P (k : ℕ) : Subgroup (GL (BlockIndex N T k) R) := parabolic (blockNumber k)
  let mat (u : P (j + 1)) : Matrix (BlockIndex N T j ⊕ T) (BlockIndex N T j ⊕ T) R :=
    (u : GL (BlockIndex N T (j + 1)) R).val
  have h_corners (u : P (j + 1)) :
      (mat u).toBlocks₁₁.BlockTriangular (blockNumber j) ∧ (mat u).toBlocks₂₁ = 0 := by
    rw [← blockTriangular_fromBlocks_blockNumber_succ_iff, fromBlocks_toBlocks]
    exact u.property
  have h_blocks (u : P (j + 1)) :
      fromBlocks (mat u).toBlocks₁₁ (mat u).toBlocks₁₂ 0 (mat u).toBlocks₂₂ = mat u := by
    rw [← (h_corners u).right, fromBlocks_toBlocks]
  have h_unit (u : P (j + 1)) : IsUnit (mat u).toBlocks₁₁ ∧ IsUnit (mat u).toBlocks₂₂ := by
    rw [← isUnit_fromBlocks_zero₂₁, h_blocks]
    exact Units.isUnit _
  let e : P (j + 1) ≃ P j × Matrix (BlockIndex N T j) T R × GL T R :=
    { toFun u :=
        (⟨(h_unit u).left.unit, (h_corners u).left⟩, (mat u).toBlocks₁₂, (h_unit u).right.unit)
      invFun := fun (x, y, z) ↦
        ⟨(isUnit_fromBlocks_zero₂₁ (B := y).mpr ⟨x.val.isUnit, z.isUnit⟩).unit,
          blockTriangular_fromBlocks_blockNumber_succ_iff.mpr ⟨x.property, rfl⟩⟩
      left_inv u := Subtype.ext (Units.ext (h_blocks u))
      right_inv := fun (x, y, z) ↦
        Prod.ext (Subtype.ext (Units.ext rfl)) (Prod.ext rfl (Units.ext rfl)) }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]

/-- The group `parabolic (blockNumber j)` of invertible block upper triangular matrices with one
diagonal block indexed by `N` and `j` diagonal blocks indexed by `T` has order
`#GL N R * (#GL T R) ^ j * #R ^ k`, with `k` independent of the commutative ring `R`. -/
lemma exists_card_parabolic_blockNumber_eq.{u} (j : ℕ) :
    ∃ k : ℕ, ∀ (R : Type u) [CommRing R],
      Nat.card (parabolic (R := R) (blockNumber (R := N) (T := T) j)) =
        Nat.card (GL N R) * Nat.card (GL T R) ^ j * Nat.card R ^ k := by
  induction j with
  | zero =>
    refine ⟨0, fun R _ ↦ ?_⟩
    have h_top : parabolic (R := R) (blockNumber (R := N) (T := T) 0) = (⊤ : Subgroup (GL N R)) :=
      eq_top_iff.mpr fun g _ a b hlt ↦ by simp [blockNumber] at hlt
    rw [h_top, pow_zero, pow_zero, mul_one, mul_one]
    exact Subgroup.card_top
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + card (BlockIndex N T j) * card T, fun R _ ↦ ?_⟩
    have h_matrix : Nat.card (Matrix (BlockIndex N T j) T R) =
        Nat.card R ^ (card (BlockIndex N T j) * card T) := by
      simp [Matrix, Nat.card_fun, ← pow_mul, mul_comm]
    rw [card_parabolic_blockNumber_succ, hk, h_matrix]
    ring

end New

/-! ## Commutation along chains from square moduli -/

namespace New.Exchange

open Finset TauCeti.ArrowTriangle

variable {I : Type} {F : ℕ → ℕ → Type} [∀ i n, NormedAddCommGroup (F i n)]
  [∀ i n, InnerProductSpace ℂ (F i n)]
  {m : ℕ} {w : I → ℕ → ℝ} {M : (I → ℂ) → (I → ℝ) → Prop}
  {L : ℕ → ℕ → I → ℝ}
  {a : I → ∀ i n, F i n →ₗ[ℂ] F i (n + 1)}
  {d : I → ∀ i n, F i (n + 1) →ₗ[ℂ] F (i + 1) n}

/-- The weighted chain is the composite of the weighted arrows. -/
lemma weightedChain_eq_compUpTo (t : I) (i n : ℕ) :
    weightedChain w a t i n = compUpTo (fun k ↦ (w t k : ℂ) • a t i k) n := by
  induction n with
  | zero => ext y; simp [compUpTo_zero_apply]
  | succ n ih => ext y; simp [compUpTo_succ_apply, ih]

/-- Take weights `w t n ≠ 0`, arrows `a t i n : F i n → F i (n + 1)` and maps
`d t i n : F i (n + 1) → F (i + 1) n`, with a parameter `t : I`. Suppose that the relation `M c f`,
read "`c` has modulus `f`", is unital and multiplicative and that for `i + n + 2 ≤ m` the square
`w n • a ∘ d = (w (n + 2) / conj β') • d ∘ a` on `F i (n + 1)` holds with some `β'` of modulus
`L (i + 1) (i + n + 2)` (part of `HasSquareModuli`). Let `X i n` be the weighted composite of the
first `n` arrows of row `i`. For `i + n < m` some `β` whose modulus is the product of the
`L (i + 1) k` over `i + 1 < k ≤ i + 1 + n` satisfies
`X (i + 1) n ∘ d ∘ a = (w (n + 1) / (w 1 * w 0 * conj β)) • d ∘ X i (n + 1)` (`ChainCommutes`). -/
lemma exists_modulus_chainCommutes (hw : ∀ t n, w t n ≠ 0)
    (h_moduli : HasSquareModuli m w M L a d) (i n : ℕ) (hi : i + n < m) :
    ∃ β : I → ℂ, M β (∏ k ∈ Ioc (i + 1) (i + 1 + n), L (i + 1) k) ∧ ChainCommutes w a d i n β := by
  induction n with
  | zero => exact ⟨1, by simpa [Ioc_self] using h_moduli.modulus_one, chainCommutes_zero hw i⟩
  | succ n ih =>
    obtain ⟨β, hβ, h_chain⟩ := ih (by lia)
    obtain ⟨β', hβ', h_square⟩ := h_moduli.exists_modulus_commutes i n hi
    refine ⟨β * β', ?_, h_chain.succ h_square⟩
    -- The product of the moduli gains the factor of the new square.
    rw [← add_assoc, prod_Ioc_succ_top (by lia)]
    exact h_moduli.modulus_mul hβ hβ'

end New.Exchange
