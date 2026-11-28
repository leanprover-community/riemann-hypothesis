module

import TauCeti.LinearAlgebra.Determinant.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Module.PID
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
`A` and of `a • 1`. Each selected matrix kills the kernel modulo `a`, so its determinant valuation
bounds the kernel length. Conversely, the lattice bound supplies a square matrix with rows in this
span and determinant valuation at most the kernel length. A minor of least valuation divides that
determinant.

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
has the same length as the module of its linear maps to `QuotSpan a`, that is, `O / a`. This
follows from the structure theorem for such modules. -/
lemma length_linearMap_quotSpan {Q : Type*} [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    {a : O} (ha : a ≠ 0) (h_kill : ∀ x : Q, a • x = 0) :
    length O (Q →ₗ[O] QuotSpan a) = length O Q := by
  classical
  -- `Q` is a product of cyclic modules `O / d i`, and `d i ∣ a` as `a` kills each factor.
  have h_torsion : IsTorsion O Q := fun x ↦ ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, h_kill x⟩
  -- The structure theorem: `e` maps `Q` onto the sum of the modules `O / p i ^ n i`.
  obtain ⟨ι, _, p, -, n, ⟨e⟩⟩ := equiv_directSum_of_isTorsion h_torsion
  let d (i : ι) : O := p i ^ n i
  let e' : Q ≃ₗ[O] ∀ i, QuotSpan (d i) := e.trans DFinsupp.linearEquivFunOnFintype
  have h_dvd (i : ι) : d i ∣ a := by
    have h_one : a • (1 : QuotSpan (d i)) = 0 := by
      simpa using congrFun (congrArg e' (h_kill (e'.symm (Pi.single i 1)))) i
    simpa [← Ideal.Quotient.eq_zero_iff_dvd, Algebra.smul_def] using h_one
  calc length O (Q →ₗ[O] QuotSpan a) = length O (∀ i, QuotSpan (d i) →ₗ[O] QuotSpan a) :=
      ((LinearMap.lsum O _ O).trans (e'.symm.congrLeft _ O)).length_eq.symm
    _ = length O Q := by
      simp [e'.length_eq, length_pi_of_fintype, length_linearMap_quotSpan_of_dvd ha (h_dvd _)]

private lemma isLeast_length_matrixKernel_dvr (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    IsLeast (addVal O '' maximalMinors A a) (length O (matrixKernel A (QuotSpan a))) := by
  let M : Matrix (r ⊕ k) k O := A.fromRows (a • 1)
  let v (f : k → r ⊕ k) := addVal O (M.submatrix f id).det
  -- Every vector in the kernel is killed by every selected row, including the rows of `a • 1`.
  have h_lower (f : k → r ⊕ k) : length O (matrixKernel A (QuotSpan a)) ≤ v f := by
    refine le_trans (length_mono (T := LinearMap.ker (M.submatrix f id • 1 :
      End O (k → QuotSpan a))) ?_) (length_ker_le_addVal_det _ _)
    intro w hw
    ext i
    change ∑ j : k, M (f i) j • w j = 0
    rcases f i with l | l
    · exact mem_matrixKernel.1 hw l
    · exact Finset.sum_eq_zero fun j _ ↦ smul_quot_eq_zero_of_dvd (dvd_mul_right a _) (w j)
  -- The row lattice contains `a • x` for every `x`. The lattice determinant bound gives a
  -- submodule of the kernel because it annihilates every row of `A`.
  have h_smul (x : k → O) : a • x ∈ span O (Set.range M.row) := by
    refine span_mono ?_ ((range_vecMulLinear (a • (1 : Matrix k k O))).le ⟨x, by simp⟩)
    exact Set.range_subset_iff.2 fun j ↦ ⟨.inr j, rfl⟩
  obtain ⟨N, S, hN, horth, hdet⟩ :=
    exists_matrix_addVal_det_le_length _ ha h_smul
  have hS : S ≤ matrixKernel A (QuotSpan a) := fun w hw ↦
    mem_matrixKernel.2 fun i ↦ (horth (A i)).1 (subset_span ⟨.inl i, rfl⟩) w hw
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  let f₀ := Function.argmin v
  have h_dvd : (M.submatrix f₀ id).det ∣ N.det := Ideal.mem_span_singleton.1 <|
    TauCeti.det_mem_of_mem_span LinearMap.proj hN fun B hB ↦ by
      choose f hf using hB
      obtain rfl : B = M.submatrix f id := (funext hf).symm
      exact Ideal.mem_span_singleton.2 (addVal_le_iff_dvd.1 (Function.argmin_le v f))
  have h_upper : v f₀ ≤ length O (matrixKernel A (QuotSpan a)) :=
    (addVal_le_iff_dvd.2 h_dvd).trans (hdet.trans (length_mono hS))
  exact ⟨⟨_, ⟨f₀, rfl⟩, h_upper.antisymm (h_lower f₀)⟩,
    Set.forall_mem_image.2 (Set.forall_mem_range.2 h_lower)⟩

/-- Let `A` be a matrix over `Λ` with columns indexed by `k`, let `ev : Λ →+* O` be a ring
homomorphism to a discrete valuation ring (`[DVR O]`), and let `ev a ≠ 0`. The length of
`matrixKernel (A.map ev) (QuotSpan (ev a))`, the kernel of `A.map ev` on `(O / ev a) ^ k`, is the
least `addVal (ev P)`, where `P` runs over `maximalMinors A a`, the maximal minors of the matrix
formed by the rows of `A` and of `a • 1`. -/
theorem isLeast_length_matrixKernel (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' maximalMinors A a)
      (length O (matrixKernel (A.map ev) (QuotSpan (ev a)))) := by
  rw [← Set.image_image (addVal O) ev, image_maximalMinors]
  exact isLeast_length_matrixKernel_dvr _ ha

end New.Selmer

end
