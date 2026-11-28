module

import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.RingTheory.Length.Determinant
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import TauCeti.RingTheory.DiscreteValuationRing.MatlisDual
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
public import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# Maximal minors and lengths

Let `A` be a matrix over a discrete valuation ring `O` and let `a ≠ 0`. The length of the kernel of
`A` on `(O / a) ^ k` is the least valuation of a maximal minor of the matrix formed by the rows of
`A` and of `a • 1`. The kernel is isomorphic to the module of linear maps to `O / a` from the
quotient of `O ^ k` by these rows, so it has the length of this quotient, which is computed from the
cokernel length-determinant formula and the multilinearity of the determinant.

* `New.Selmer.maximalMinors`, `New.Selmer.matrixKernel`: the minors and the kernel.
* `New.Selmer.isLeast_length_matrixKernel`: the statement for a matrix over a commutative ring `Λ`
  and a ring homomorphism `ev : Λ →+* O` with `ev a ≠ 0`.

Notions from other files:

* `New.QuotSpan a`: the quotient ring `O / a O`.

## Relation to the literature

Known result: Length of a matrix kernel modulo `a` over a discrete valuation ring via maximal
minors. A consequence of the theorem on elementary divisors.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Matrix Module Submodule IsDiscreteValuationRing

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [Fintype k] [DecidableEq k]

/-- The minors of size `card k` of the matrix formed by the rows of `A` and of `a • 1`, where `k`
indexes the columns. The family of rows of `A` may be infinite. A choice of rows with a repetition
is allowed; it contributes the minor `0`. -/
def maximalMinors (A : Matrix r k Λ) (a : Λ) : Set Λ :=
  Set.range fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det

/-- The kernel of `A` on `B ^ k`, for an `O`-module `B`: the vectors `w` such that
`∑ j, A i j • w j = 0` for every row index `i`. -/
def matrixKernel (A : Matrix r k O) (B : Type*) [AddCommGroup B] [Module O B] :
    Submodule O (k → B) :=
  ⨅ i : r, LinearMap.ker (∑ j : k, A i j • LinearMap.proj j : (k → B) →ₗ[O] B)

/-- The submodule of `O ^ k` spanned by the rows of `A` and of `a • 1`. -/
def rowLattice (A : Matrix r k O) (a : O) : Submodule O (k → O) :=
  span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row)

/-- A ring homomorphism `ev` maps the maximal minors of the rows of `A` and `a • 1` onto those of
the rows of `A.map ev` and `ev a • 1`. -/
lemma image_maximalMinors (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) :
    ev '' maximalMinors A a = maximalMinors (A.map ev) (ev a) := by
  have h_map : (A.fromRows (a • (1 : Matrix k k Λ))).map ev = (A.map ev).fromRows (ev a • 1) := by
    ext (i | i) j <;> simp [Matrix.one_apply, apply_ite ev]
  simp [maximalMinors, ← Set.range_comp, Function.comp_def, ev.map_det, ← h_map, submatrix_map]

omit [DecidableEq k] in
/-- A vector lies in `matrixKernel A B` exactly if every row of `A` sends it to `0`. -/
lemma mem_matrixKernel {A : Matrix r k O} {B : Type*} [AddCommGroup B] [Module O B] {w : k → B} :
    w ∈ matrixKernel A B ↔ ∀ i : r, ∑ j : k, A i j • w j = 0 := by
  simp [matrixKernel]

lemma smul_mem_rowLattice (A : Matrix r k O) (a : O) (v : k → O) : a • v ∈ rowLattice A a := by
  refine span_mono ?_ ((range_vecMulLinear (a • (1 : Matrix k k O))).le ⟨v, by simp⟩)
  exact Set.range_subset_iff.2 fun j ↦ ⟨.inr j, rfl⟩

/-- The kernel of `A` on `(O / a) ^ k` (`QuotSpan a` is `O / a`) has the length of the module of
linear maps to `O / a` from the quotient of `O ^ k` by `rowLattice A a`, the span of the rows of
`A` and `a • 1`: a map corresponds to its values at the standard basis. -/
lemma length_matrixKernel_eq_length_linearMap (A : Matrix r k O) (a : O) :
    length O (matrixKernel A (QuotSpan a)) =
      length O (((k → O) ⧸ rowLattice A a) →ₗ[O] QuotSpan a) := by
  let val : (((k → O) ⧸ rowLattice A a) →ₗ[O] QuotSpan a) →ₗ[O] k → QuotSpan a :=
    LinearMap.pi fun j ↦ LinearMap.applyₗ ((rowLattice A a).mkQ (Pi.single j 1))
  have h_inj : Function.Injective val := fun g g' h_val ↦
    linearMap_qext _ ((Pi.basisFun O k).ext fun j ↦ by simpa [val] using congrFun h_val j)
  have h_range : val.range = matrixKernel A (QuotSpan a) := by
    ext w
    rw [mem_matrixKernel]
    refine ⟨?_, fun hw ↦ ?_⟩
    · rintro ⟨g, rfl⟩ i
      have h_row : (rowLattice A a).mkQ (A i) = 0 :=
        (Quotient.mk_eq_zero _).2 (subset_span ⟨.inl i, rfl⟩)
      calc ∑ j, A i j • val g j
        _ = g ((rowLattice A a).mkQ (∑ j, A i j • Pi.single j 1)) := by simp [val]
        _ = 0 := by rw [← pi_eq_sum_univ', h_row, map_zero]
    · have h_kill : rowLattice A a ≤ (Fintype.linearCombination O w).ker := span_le.2 <| by
        rintro _ ⟨i | i, rfl⟩
        · exact hw i
        · change ∑ j : k, (a * (1 : Matrix k k O) i j) • w j = 0
          exact Finset.sum_eq_zero fun j _ ↦ smul_quot_eq_zero_of_dvd (dvd_mul_right a _) (w j)
      exact ⟨liftQ _ _ h_kill, funext fun j : k ↦ by simp [val]⟩
  rw [← h_range, (LinearEquiv.ofInjective val h_inj).length_eq]

variable [DVR O]

/-- In a discrete valuation ring let `d ∣ a ≠ 0`. The module of linear maps `O / d → O / a` has
the length of `O / d` (`QuotSpan x` is `O / x`). -/
lemma length_linearMap_quotSpan_of_dvd {a d : O} (ha : a ≠ 0) (hd : d ∣ a) :
    length O (QuotSpan d →ₗ[O] QuotSpan a) = length O (QuotSpan d) := by
  -- The linear maps `O / d → O / a` are the multiples of multiplication by `a / d`.
  obtain ⟨c, rfl⟩ := hd
  have h_mul_le : Ideal.span {d} ≤ Submodule.comap (LinearMap.lsmul O O c) (Ideal.span {d * c}) :=
    (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 (by simp [mul_comm]))
  let mulC : QuotSpan d →ₗ[O] QuotSpan (d * c) := mapQ _ _ (LinearMap.lsmul O O c) h_mul_le
  let φ : O →ₗ[O] QuotSpan d →ₗ[O] QuotSpan (d * c) := LinearMap.toSpanSingleton O _ mulC
  -- `φ t` is multiplication by `t * c`.
  have hφ (t : O) : φ t 1 = Ideal.Quotient.mk _ (t * c) :=
    congrArg (Ideal.Quotient.mk _) (by simp)
  have h_ext {g g' : QuotSpan d →ₗ[O] QuotSpan (d * c)} (h_one : g 1 = g' 1) : g = g' :=
    linearMap_qext _ (LinearMap.ext_ring h_one)
  have h_ker : φ.ker = Ideal.span {d} := by
    ext t
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← mul_dvd_mul_iff_right
      (right_ne_zero_of_mul ha), ← Ideal.Quotient.eq_zero_iff_dvd, ← hφ]
    exact ⟨fun h ↦ by rw [h, LinearMap.zero_apply], fun h ↦ h_ext h⟩
  have h_surj : Function.Surjective φ := fun g ↦ by
    -- The value `y` of `g` at `1` is killed by `d`, so `d * c ∣ d * y`.
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g 1)
    have h_zero : Ideal.Quotient.mk (Ideal.span {d * c}) (d * y) = 0 := by
      change d • Ideal.Quotient.mk (Ideal.span {d * c}) y = 0
      rw [hy, ← map_smul, smul_quot_eq_zero_of_dvd dvd_rfl, map_zero]
    obtain ⟨t, rfl⟩ : c ∣ y := by
      rwa [Ideal.Quotient.eq_zero_iff_dvd, mul_dvd_mul_iff_left (left_ne_zero_of_mul ha)] at h_zero
    exact ⟨t, h_ext (by rw [hφ, mul_comm t, hy])⟩
  exact ((quotEquivOfEq _ _ h_ker.symm).trans (φ.quotKerEquivOfSurjective h_surj)).length_eq.symm

/-- Over a discrete valuation ring `O`, a finitely generated module `Q` that `a ≠ 0` annihilates
has the same length as the module of its linear maps to `O / a`. Its Matlis dual consists of maps
with values in the `a`-torsion of `Frac(O) / O`, which is isomorphic to `O / a`. -/
lemma length_linearMap_quotSpan {Q : Type*} [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    {a : O} (ha : a ≠ 0) (h_kill : ∀ x : Q, a • x = 0) :
    length O (Q →ₗ[O] QuotSpan a) = length O Q := by
  let E := FractionRing O ⧸ LinearMap.range (Algebra.linearMap O (FractionRing O))
  let S := torsionBySet O E (Ideal.span {a})
  let e : QuotSpan a ≃ₗ[O] S := quotientEquivTorsionBySet (K := FractionRing O) ha
  let incl : (Q →ₗ[O] S) →ₗ[O] (Q →ₗ[O] E) := LinearMap.llcomp O Q S E S.subtype
  have hi : Function.Injective incl := fun f g h ↦
    LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun h x)
  have hs : Function.Surjective incl := by
    intro f
    have hf (x : Q) : f x ∈ S := by
      change f x ∈ torsionBySet O E (Ideal.span {a})
      rw [torsionBySet_span_singleton_eq, mem_torsionBy_iff, ← map_smul, h_kill x, map_zero]
    exact ⟨f.codRestrict S hf, LinearMap.ext fun _ ↦ rfl⟩
  calc length O (Q →ₗ[O] QuotSpan a) = length O (Q →ₗ[O] S) :=
        (LinearEquiv.congrRight (M := Q) e).length_eq
    _ = length O (Q →ₗ[O] E) := (LinearEquiv.ofBijective incl ⟨hi, hs⟩).length_eq
    _ = length O Q := length_linearMap_fractionRing_quotient (K := FractionRing O) Q

/-- Over a discrete valuation ring and for `a ≠ 0` the lattice `rowLattice A a` of the rows of
`A` and `a • 1` is free of full rank, so it is spanned by the rows of a square matrix. -/
lemma exists_span_row_eq_rowLattice (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    ∃ N : Matrix k k O, span O (Set.range N.row) = rowLattice A a := by
  -- Multiplication by `a` embeds `O ^ k` into the lattice, so the lattice has rank `card k`.
  let g : (k → O) →ₗ[O] rowLattice A a :=
    (LinearMap.lsmul O _ a).codRestrict _ (smul_mem_rowLattice A a)
  have h_inj : Function.Injective g := (LinearMap.lsmul_injective ha).codRestrict _
  have h_rank : finrank O (k → O) = finrank O (rowLattice A a) :=
    (g.finrank_le_finrank_of_injective h_inj).antisymm (finrank_le _)
  let b : Basis k O (rowLattice A a) := (Pi.basisFun O k).map (.ofFinrankEq _ _ h_rank)
  refine ⟨of fun i ↦ (b i : k → O), ?_⟩
  change span O (Set.range ((rowLattice A a).subtype ∘ b)) = rowLattice A a
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, map_subtype_top]

/-- Over a discrete valuation ring and for `a ≠ 0`, the quotient of `O ^ k` by `rowLattice A a`,
the span of the rows of `A` and `a • 1`, has as its length the least valuation of a maximal minor
of these rows. -/
lemma isLeast_length_quotient_rowLattice (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    IsLeast (addVal O '' maximalMinors A a) (length O ((k → O) ⧸ rowLattice A a)) := by
  let M : Matrix (r ⊕ k) k O := A.fromRows (a • 1)
  let v (f : k → r ⊕ k) : ℕ∞ := addVal O (M.submatrix f id).det
  have h_len (B : Matrix k k O) (hB : B.det ≠ 0) :
      length O ((k → O) ⧸ span O (Set.range B.row)) = addVal O B.det := by
    rw [← col_transpose, ← Bᵀ.range_mulVecLin,
      Matrix.length_quotient_range_mulVecLin_eq_ord_det Bᵀ (by simpa), det_transpose,
      Ring.ord_eq_addVal]
  -- The rows chosen by `f` span a sublattice, whose quotient is at least as long.
  have h_lower (f : k → r ⊕ k) : length O ((k → O) ⧸ rowLattice A a) ≤ v f := by
    rcases eq_or_ne (M.submatrix f id).det 0 with h0 | h0
    · simp [v, h0]
    have h_le : span O (Set.range (M.submatrix f id).row) ≤ rowLattice A a :=
      span_mono (Set.range_comp_subset_range f M.row)
    simpa only [h_len _ h0] using length_le_of_surjective _ (factor_surjective h_le)
  -- The length is the valuation of `det N`, for a matrix `N` whose rows span the lattice. These
  -- rows are combinations of the rows of `M`, so `det N` is a combination of minors, and the
  -- minor of least valuation `v (Function.argmin v)` divides it.
  obtain ⟨N, hN⟩ := exists_span_row_eq_rowLattice A ha
  have hN_det : N.det ≠ 0 := by
    choose C hC using fun i : k ↦
      (range_vecMulLinear N).ge (hN.symm ▸ smul_mem_rowLattice A a (Pi.single i 1))
    have hCN : of C * N = a • 1 := ext fun i j ↦ by
      simpa [Matrix.mul_apply, vecMul, dotProduct, Matrix.one_apply, Pi.single_apply,
        eq_comm (a := j)] using congrFun (hC i) j
    intro h0
    exact pow_ne_zero (Fintype.card k) ha (by simpa [h0, eq_comm] using congrArg det hCN)
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  let f₀ : k → r ⊕ k := Function.argmin v
  have h_dvd : (M.submatrix f₀ id).det ∣ N.det := Ideal.mem_span_singleton.1 <|
    TauCeti.det_mem_of_mem_span LinearMap.proj (fun i ↦ hN.le (subset_span ⟨i, rfl⟩))
      fun w hw ↦ by
        choose f hf using hw
        obtain rfl : w = M.submatrix f id := (funext hf).symm
        exact Ideal.mem_span_singleton.2 (addVal_le_iff_dvd.1 (Function.argmin_le v f))
  have h_upper : v f₀ ≤ length O ((k → O) ⧸ rowLattice A a) :=
    (addVal_le_iff_dvd.2 h_dvd).trans_eq (by rw [← hN, h_len N hN_det])
  exact ⟨⟨(M.submatrix f₀ id).det, ⟨f₀, rfl⟩, h_upper.antisymm (h_lower f₀)⟩,
    Set.forall_mem_image.2 (Set.forall_mem_range.2 h_lower)⟩

/-- Let `A` be a matrix over `Λ` with columns indexed by `k`, let `ev : Λ →+* O` be a ring
homomorphism to a discrete valuation ring (`[DVR O]`), and let `ev a ≠ 0`. The length of
`matrixKernel (A.map ev) (QuotSpan (ev a))`, the kernel of `A.map ev` on `(O / ev a) ^ k`, is the
least `addVal (ev P)`, where `P` runs over `maximalMinors A a`, the maximal minors of the matrix
formed by the rows of `A` and of `a • 1`. -/
theorem isLeast_length_matrixKernel (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' maximalMinors A a)
      (length O (matrixKernel (A.map ev) (QuotSpan (ev a)))) := by
  have h_kill (x : (k → O) ⧸ rowLattice (A.map ev) (ev a)) : ev a • x = 0 := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    simpa [← Quotient.mk_smul] using smul_mem_rowLattice _ _ v
  rw [length_matrixKernel_eq_length_linearMap, length_linearMap_quotSpan ha h_kill,
    ← Set.image_image (addVal O) ev, image_maximalMinors]
  exact isLeast_length_quotient_rowLattice _ ha

end New.Selmer

end
