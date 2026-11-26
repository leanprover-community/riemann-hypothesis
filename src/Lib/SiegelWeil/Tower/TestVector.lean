module

public import Mathlib.LinearAlgebra.AffineSpace.MidpointZero
public import Lib.SiegelWeil.Tower.RealConeIntegral

/-!
# Determinant vectors: the test vectors of the cone integral

Let `W' = W ⊕ H` and `V' = V ⊕ H` with hyperbolic planes `H`, split by adapted splittings `A` and
`X`. At each infinite place `w` a point `u` of `Hom(W, V)` has a positive part `u₊`. For matrices
`F w` the determinant vector is the Fock vector of the polynomial whose value at `u` is the
conjugate of `∏ w, det₊ (u₊ F w) ^ m w * det₋ (u₊ F w) ^ (m w + 2 k)`, where `det₊` and `det₋` are
the principal minors on the basis vectors of `V` of sign `1` and `-1`. If the rank of `W'` is
`2 (k + q')`, with `q'` its number of negative signs, the maximal compact subgroup of `U(V')` fixes
the determinant vectors of `(W', V')` in the Weil representation of weight `k + m`, and the cone
integral, on either side of the summation formula on the line, sends a suitable one to any given
multiple of a determinant vector of `(W, V)`. For `V = 0` the determinant vector is the vacuum.

* `New.Exchange.slice_polyVector_apply`: in the mixed model of an adapted splitting, the slice of
  the Fock vector of a polynomial in the positive coordinates is its value at a point of the frame.
* `New.Exchange.detVector`: the determinant vector.
* `New.Exchange.realPairWeil_detVector`: the maximal compact subgroup of the target group fixes it.
* `New.Exchange.coneIntegrand_detVector`: the cone integrand, in either model, of the determinant
  vector of `liftFrame A X F` is an explicit positive function times the determinant vector of `F`.
* `New.Exchange.exists_integral_coneIntegrand_detVector`: every multiple of a determinant vector is
  a cone integral of a multiple of a determinant vector.

Notions from other files:
* `New.Fock.polyVector`: the Fock vector x ↦ P(ζ(x))·exp(−|x|²/2) of a polynomial P, where ζ(x)_i is
  x̄_i at positive and x_i at negative coordinates.
* `New.Fock.MixedModel`: a decomposition y = La + Iw + Kb of the large space, with a map `slice a`
  from the large Fock space to the small one.
* `Splitting.IsAdapted 1 b`: the adelic frame `D.frameAt 1 b = (l b*⁻¹, k b, ι)` of a splitting
  `D` has orthonormal columns at the infinite places and integral entries at the finite ones.
* `New.Exchange.coneIntegrand`: the integrand of the cone integral, `lineTermReal A X β a` applied
  to the translate of a vector by the compact part, times a character and a power of `|a|`.
* `principalMinor y p`: the determinant of the block of `y` on the indices that satisfy `p`.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

@[expose] public section

noncomputable section

namespace New.Exchange

open Matrix MeasureTheory Complex WeilData Fock Space Splitting MvPolynomial Finset Fintype
  Heisenberg IsVacuum MixedModel Prod

open NumberField (InfinitePlace)

section Frame

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {W : Space E n s} {W' : Space E n' s'} {D : W.Splitting W' r}

variable {b : GL r (𝔸 E)}

omit [WeilData E] in
/-- Let `D` split `W` as `W'` plus hyperbolic planes indexed by `r`, and let it be adapted at `1`
to `b`: at each infinite place `w` the frame `D.frameAt 1 b` of `W` has orthonormal columns (and it
is integral at the finite places). This frame is square, so its rows are orthonormal as well. -/
lemma frameAt_real_mul_conjTranspose (h : D.IsAdapted 1 b) (w : InfinitePlace E) :
    atRealPlace (D.frameAt 1 b) w * (atRealPlace (D.frameAt 1 b) w)ᴴ = 1 := by
  obtain ⟨h_orthonormal, -⟩ : IsOrthoIntegral (D.frameAt 1 b) := h
  exact (mul_eq_one_comm_of_card_eq ((r ⊕ r) ⊕ n') n ℂ (by simp +arith [D.card_eq])).1
    (h_orthonormal w)

omit [WeilData E] in
/-- Let `D` split `W` as `W'` plus hyperbolic planes indexed by `r`, with an adapted frame
`F = D.frameAt 1 b`. At an infinite place `w`, with `S` the diagonal matrix of the signs `s` of
`W`, we have `S F = F T`, where `T` is the block diagonal matrix of the exchange of the two lines of
each plane and of the signs `s'` of `W'`. -/
lemma signMatrix_mul_frameAt_real (h : D.IsAdapted 1 b) (w : InfinitePlace E) :
    signMatrix s * atRealPlace (D.frameAt 1 b) w = atRealPlace (D.frameAt 1 b) w *
      fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s') := by
  have h_gram : (atRealPlace (D.frameAt 1 b) w)ᴴ * signMatrix s * atRealPlace (D.frameAt 1 b) w =
      fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s') := by
    rw [gram_atRealPlace, gram_frameAt]
    simp [stdForm, signMatrix, fromBlocks_map]
  simp [← h_gram, ← Matrix.mul_assoc, frameAt_real_mul_conjTranspose h]

omit [Fintype n] in
/-- The projection `posProj s` on the coordinates of sign `1` is `(1 + signMatrix s) / 2`, where
`signMatrix s` is the diagonal matrix of the signs. -/
lemma posProj_eq : posProj s = (2⁻¹ : ℂ) • (1 + signMatrix s) := by
  rw [signMatrix_eq_posProj_sub]
  module

/-- The vector `L a + I z + K c` with coordinates `a`, `z`, `c` in the directions `L`, `I`, `K` of
the real mixed model of a splitting `D` adapted at `1` to `b`. -/
def framePoint (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ) (z : InfinitePlace E × n' → ℂ)
    (c : InfinitePlace E × r → ℂ) : InfinitePlace E × n → ℂ :=
  h.mixedModel.L *ᵥ a + h.mixedModel.I *ᵥ z + h.mixedModel.K *ᵥ c

/-- Let `D.frameAt 1 b` be an adapted frame. The point `framePoint h a z c`, which is
`L a + I z + K c`, is the image under the infinite components `realMatrix` of this frame of its
three blocks of coordinates, put side by side at each place in the order `a`, `c`, `z`. -/
lemma framePoint_eq_mulVec (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) (c : InfinitePlace E × r → ℂ) :
    framePoint h a z c = realMatrix (D.frameAt 1 b) *ᵥ
      fun ((w, i) : InfinitePlace E × ((r ⊕ r) ⊕ n')) ↦
        (vecToMatrix a w ⊕ᵥ vecToMatrix c w ⊕ᵥ vecToMatrix z w) i := by
  ext ⟨w, i⟩
  simpa [vecToMatrix, framePoint, IsAdapted.mixedModel, mulVec, dotProduct, sum_prod_type,
    Splitting.frameAt, realMatrix, blockDiagonal, G.adeleMatrix_one] using add_right_comm ..

/-- At the infinite place `w`, the point `framePoint h a z c`, which is `L a + I z + K c`, is the
image under the component at `w` of the adapted frame `D.frameAt 1 b` of the three blocks of
coordinates at `w`. -/
lemma framePoint_apply (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) (c : InfinitePlace E × r → ℂ) (w : InfinitePlace E) (l : n) :
    framePoint h a z c (w, l) =
      (atRealPlace (D.frameAt 1 b) w *ᵥ (vecToMatrix a w ⊕ᵥ vecToMatrix c w ⊕ᵥ vecToMatrix z w))
        l := by
  rw [framePoint_eq_mulVec h]
  simp [realMatrix, mulVec, dotProduct, blockDiagonal, sum_prod_type]

/-- The projection `posProj` on the positive coordinates sends the point `L a + I z + K c`
(`framePoint h a z c`) to the point with `a` and `c` replaced by their midpoint and `z` by its
positive projection, because the matrix of signs exchanges `L` and `K`. -/
lemma posProj_mulVec_framePoint (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) (c : InfinitePlace E × r → ℂ) :
    posProj (realSigns E s) *ᵥ framePoint h a z c =
      framePoint h (midpoint ℂ a c) (posProj (realSigns E s') *ᵥ z) (midpoint ℂ a c) := by
  ext ⟨w, l⟩
  let T : Matrix ((r ⊕ r) ⊕ n') ((r ⊕ r) ⊕ n') ℂ :=
    fromBlocks (n := r ⊕ r) (fromBlocks 0 1 1 0) 0 0 (signMatrix s')
  let x : (r ⊕ r) ⊕ n' → ℂ := vecToMatrix a w ⊕ᵥ vecToMatrix c w ⊕ᵥ vecToMatrix z w
  -- At the place `w` the projection `(1 + signMatrix s) / 2` is `(1 + T) / 2` in the frame.
  have h_mul : posProj s * atRealPlace (D.frameAt 1 b) w =
      atRealPlace (D.frameAt 1 b) w * (2⁻¹ : ℂ) • (1 + T) := by
    simp [posProj_eq, T, Matrix.add_mul, Matrix.mul_add, signMatrix_mul_frameAt_real h]
  have h_half : ((2⁻¹ : ℂ) • (1 + T)) *ᵥ x =
      (vecToMatrix (midpoint ℂ a c) w ⊕ᵥ vecToMatrix (midpoint ℂ a c) w) ⊕ᵥ
        vecToMatrix (posProj (realSigns E s') *ᵥ z) w := by
    ext ((i | i) | i) <;> simp [T, x, vecToMatrix, midpoint_eq_smul_add, posProj_eq, signMatrix,
      smul_mulVec, add_mulVec, fromBlocks_mulVec, mulVec_diagonal, mul_add, add_comm]
  calc (posProj (realSigns E s) *ᵥ framePoint h a z c) (w, l)
      = ((posProj s * atRealPlace (D.frameAt 1 b) w) *ᵥ x) l := by
        rw [← mulVec_mulVec, posProj, posProj, mulVec_diagonal, mulVec_diagonal, framePoint_apply h]
    _ = framePoint h (midpoint ℂ a c) (posProj (realSigns E s') *ᵥ z) (midpoint ℂ a c) (w, l) := by
        rw [h_mul, ← mulVec_mulVec, h_half, framePoint_apply h]

/-- The matrix of signs exchanges `L` and `K`, so on a point `L a + I z + K a`
(`framePoint h a z a`) it acts through the middle coordinate `z` only. -/
lemma signMatrix_mulVec_framePoint (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (z : InfinitePlace E × n' → ℂ) :
    signMatrix (realSigns E s) *ᵥ framePoint h a z a =
      framePoint h a (signMatrix (realSigns E s') *ᵥ z) a := by
  simp only [signMatrix_eq_posProj_sub, sub_mulVec, one_mulVec, posProj_mulVec_framePoint h,
    midpoint_self]
  simp only [framePoint, mulVec_sub]
  abel

/-- The difference of two points `L a + I z + K c` (`framePoint h a z c`) is the point of the
differences of their coordinates. -/
lemma framePoint_sub (h : D.IsAdapted 1 b) (a a' c c' : InfinitePlace E × r → ℂ)
    (z z' : InfinitePlace E × n' → ℂ) :
    framePoint h a z c - framePoint h a' z' c' = framePoint h (a - a') (z - z') (c - c') := by
  simp only [framePoint, mulVec_sub]
  abel

/-- The columns of `L`, `K` and `I` of an adapted splitting are orthonormal, so the inner product of
the points `L a + I u + K a` and `L c + I z + K c` (both `framePoint`) is `2 ⟨a, c⟩ + ⟨u, z⟩`. -/
lemma star_framePoint_dotProduct (h : D.IsAdapted 1 b) (a c : InfinitePlace E × r → ℂ)
    (u z : InfinitePlace E × n' → ℂ) :
    star (framePoint h a u a) ⬝ᵥ framePoint h c z c = 2 * star a ⬝ᵥ c + star u ⬝ᵥ z := by
  rw [framePoint_eq_mulVec h, framePoint_eq_mulVec h, star_mulVec_dotProduct, mulVec_mulVec,
    conjTranspose_realMatrix_mul_self _ h, one_mulVec]
  -- It remains to split the sum over the three blocks of coordinates.
  simp [vecToMatrix, sum_prod_type, sum_add_distrib, two_mul, dotProduct]

/-- A vector `y` in the positive coordinates (fixed by `posProj`) is a point `L c + I z + K c`
(`framePoint`) whose middle coordinate `z` is positive. -/
lemma exists_framePoint_eq_of_posProj_eq (h : D.IsAdapted 1 b) {y : InfinitePlace E × n → ℂ}
    (hy : posProj (realSigns E s) *ᵥ y = y) :
    ∃ (c : InfinitePlace E × r → ℂ) (z : InfinitePlace E × n' → ℂ),
      framePoint h c (posProj (realSigns E s') *ᵥ z) c = y := by
  obtain ⟨A, Z, C, h_span⟩ := h.mixedModel.exists_decomp
  -- In the coordinates of `y` in the frame, projecting takes the midpoint of those on `L` and `K`.
  have h_decomp : framePoint h (A *ᵥ y) (Z *ᵥ y) (C *ᵥ y) = y := h_span y
  exact ⟨midpoint ℂ (A *ᵥ y) (C *ᵥ y), Z *ᵥ y, by rw [← posProj_mulVec_framePoint h, h_decomp, hy]⟩

/-- Let `y` be a vector in the positive coordinates, and translate the vacuum (the Gaussian) by it
with the Heisenberg operator `realHeisenbergOp y`. The value at `u` of the slice at `a` of this
translate, in the mixed model of the adapted splitting, is the value of the translate at the point
`framePoint h (-a) u (-a)`, that is `-L a + I u - K a`. -/
lemma slice_realHeisenbergOp_vacElem_apply (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (u : InfinitePlace E × n' → ℂ) {y : InfinitePlace E × n → ℂ}
    (hy : posProj (realSigns E s) *ᵥ y = y) :
    h.mixedModel.slice a (realHeisenbergOp y vacElem) u =
      (realHeisenbergOp y vacElem : fockSpace (realSigns E s)) (framePoint h (-a) u (-a)) := by
  obtain ⟨c, z₀, rfl⟩ := exists_framePoint_eq_of_posProj_eq h hy
  set z : InfinitePlace E × n' → ℂ := posProj (realSigns E s') *ᵥ z₀
  have h_slice : h.mixedModel.slice a (realHeisenbergOp (framePoint h c z c) vacElem) u =
      (realHeisenberg 1).β (a + (a + c)) c * cexp (-(star (a + c) ⬝ᵥ (a + c))) *
        ((realHeisenberg (realSigns E s')).β z u * realVac (u - z)) := by
    rw [framePoint, slice_realHeisenbergOp, two_nsmul, add_assoc a a c]
    simp [slice_vac, IsVacuum.smul_apply, heisenbergOp_apply, vacElem_apply, mul_assoc]
  -- Both sides are exponentials. It remains to compare the exponents.
  rw [h_slice, heisenbergOp_apply, vacElem_apply, framePoint_sub]
  simp only [realHeisenberg, realVac, signMatrix_mulVec_framePoint h, star_framePoint_dotProduct h,
    signMatrix_one, one_mulVec, ← exp_add]
  congr 1
  simp only [star_add, star_sub, star_neg, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, neg_dotProduct, dotProduct_neg]
  ring

/-- Let `e` split the coordinates `ι`, with signs `ε`, into `ι₁` and `ι₂`. The external product
`realBoxProd` of the translate of the vacuum by `y` with the vacuum is the translate of the vacuum
by the vector `(y, 0)`. -/
lemma realBoxProd_realHeisenbergOp_vacVector {ι ι₁ ι₂ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {ε : ι → ℤˣ} {ε₁ : ι₁ → ℤˣ}
    {ε₂ : ι₂ → ℤˣ} {e : ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) (y : ι₁ → ℂ) :
    realBoxProd he (realHeisenbergOp y vacVector) vacVector =
      realHeisenbergOp ((realCoordSum he).equiv (y, 0)) vacVector := by
  change (realCoordSum he).tmul (heisenbergOp y vacElem) vacElem =
    heisenbergOp ((realCoordSum he).equiv (y, 0)) vacElem
  simp [← OrthogonalSum.tmul_vacElem (realCoordSum he), OrthogonalSum.heisenbergOp_tmul]

/-- Let `P` be a polynomial in the positive coordinates and `polyVector` its Fock vector
`P(ζ) exp(-|·|² / 2)`. In the mixed model of an adapted splitting, the value at `u` of the slice at
`a` of this vector is its value at the point `framePoint h (-a) u (-a)`, that is
`-L a + I u - K a`. -/
lemma slice_polyVector_apply (h : D.IsAdapted 1 b) (a : InfinitePlace E × r → ℂ)
    (u : InfinitePlace E × n' → ℂ)
    (P : MvPolynomial {i : InfinitePlace E × n // realSigns E s i = 1} ℂ) :
    h.mixedModel.slice a (polyVector (realSigns E s) (rename Subtype.val P)) u =
      polyVector (realSigns E s) (rename Subtype.val P) (framePoint h (-a) u (-a)) := by
  -- Both sides are bounded functionals on the Fock space of the positive coordinates, tensored
  -- with the vacuum. So it is enough to treat the translates of the vacuum by positive vectors.
  have h_signs : realSigns E s ∘ Equiv.sumCompl (fun i ↦ realSigns E s i = 1) =
      (realSigns E s ∘ Subtype.val) ⊕ᵥ (realSigns E s ∘ Subtype.val) :=
    Sum.comp_elim (realSigns E s) Subtype.val Subtype.val
  let Φ : fockSpace (fun i : {i // realSigns E s i = 1} ↦ realSigns E s i) →L[ℂ] ℂ :=
    (valueAt u ∘L h.mixedModel.slice a - valueAt (framePoint h (-a) u (-a))) ∘L
      (realBoxProd h_signs).flip Fock.vacVector
  have h_functional : Φ = 0 := by
    refine hom_ext fun y ↦ ?_
    have h_positive : posProj (realSigns E s) *ᵥ (realCoordSum h_signs).equiv (y, 0) =
        (realCoordSum h_signs).equiv (y, 0) := by
      ext i
      by_cases hi : realSigns E s i = 1 <;> simp [realCoordSum, posProj, mulVec_diagonal, hi]
    simp [Φ, valueAt_apply, realBoxProd_realHeisenbergOp_vacVector,
      slice_realHeisenbergOp_vacElem_apply h a u h_positive]
  have h_box : realBoxProd h_signs
      (polyVector (fun i : {i // realSigns E s i = 1} ↦ realSigns E s i) P) vacVector =
      polyVector (realSigns E s) (rename Subtype.val P) := by
    simp [← polyVector_one, realBoxProd_polyVector, Function.comp_def]
  simpa [Φ, h_box, sub_eq_zero, valueAt_apply] using DFunLike.congr_fun h_functional
    (polyVector (fun i : {i // realSigns E s i = 1} ↦ realSigns E s i) P)

end Frame

section LinearAlgebra

variable {r r' : Type} [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r'] {t : r → ℤˣ}
  {t' : r' → ℤˣ}

/-- The determinant of a matrix with rows and columns indexed by `Unit ⊕ Unit`. -/
lemma det_unit_sum_unit (N : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) :
    N.det = N (.inl ()) (.inl ()) * N (.inr ()) (.inr ()) -
      N (.inl ()) (.inr ()) * N (.inr ()) (.inl ()) := by
  let e : Fin 2 ≃ Unit ⊕ Unit := finTwoEquiv.trans Equiv.boolEquivPUnitSumPUnit
  rw [← det_submatrix_equiv_self e, det_fin_two]
  rfl

/-- Two signs have product `1` exactly when they are equal. -/
lemma units_int_mul_eq_one_iff (a b : ℤˣ) : a * b = 1 ↔ a = b := by
  revert a b
  decide

omit [Fintype r] in
/-- The diagonal projection on the indices of sign `σ` is `(1 + σ S) / 2`, with `S` the matrix of
signs. -/
lemma diagonal_sign_eq (t : r → ℤˣ) (σ : ℤˣ) :
    (diagonal fun i : r ↦ if t i = σ then (1 : ℂ) else 0) =
      (2⁻¹ : ℂ) • (1 + (σ : ℂ) • signMatrix t) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    obtain rfl | rfl := Int.units_eq_one_or σ <;> obtain h | h := Int.units_eq_one_or (t i) <;>
      simp [signMatrix, h] <;> norm_num
  · simp [signMatrix, hij]

/-- Let `P` be unitary and carry the signs `t'` to the exchange of the two lines of a hyperbolic
plane and the signs `t`. The principal minor on the indices of sign `σ` of the conjugate by `P` of
the block matrix of the scalar `a` on the plane and `M` is `a` times that of `M`. -/
lemma principalMinor_conj_fromBlocks {P : Matrix r' ((Unit ⊕ Unit) ⊕ r) ℂ}
    (hP : P * Pᴴ = 1) (hP' : Pᴴ * P = 1)
    (h_sign : signMatrix t' * P =
      P * fromBlocks (n := Unit ⊕ Unit) (fromBlocks 0 1 1 0) 0 0 (signMatrix t))
    (a : ℂ) (M : Matrix r r ℂ) (σ : ℤˣ) :
    principalMinor (P * fromBlocks (a • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ)) 0 0 M * Pᴴ)
      (t' · = σ) = a * principalMinor M (t · = σ) := by
  set e : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
    (2⁻¹ : ℂ) • (1 + (σ : ℂ) • fromBlocks 0 1 1 0) with he
  set Δ : Matrix r r ℂ := diagonal fun i : r ↦ if t i = σ then (1 : ℂ) else 0 with hΔ
  set D : Matrix ((Unit ⊕ Unit) ⊕ r) ((Unit ⊕ Unit) ⊕ r) ℂ := fromBlocks (a • 1) 0 0 M with hD
  set Θ : Matrix ((Unit ⊕ Unit) ⊕ r) ((Unit ⊕ Unit) ⊕ r) ℂ := fromBlocks e 0 0 Δ with hΘ
  have h_one : (1 : Matrix ((Unit ⊕ Unit) ⊕ r) ((Unit ⊕ Unit) ⊕ r) ℂ) = fromBlocks 1 0 0 1 :=
    fromBlocks_one.symm
  -- In the frame `P` the projection on the indices of sign `σ` is block diagonal.
  have h_proj : (diagonal fun i : r' ↦ if t' i = σ then (1 : ℂ) else 0) * P = P * Θ := by
    have h_block : Θ = (2⁻¹ : ℂ) • (1 + (σ : ℂ) •
        fromBlocks (n := Unit ⊕ Unit) (fromBlocks 0 1 1 0) 0 0 (signMatrix t)) := by
      rw [hΘ, hΔ, diagonal_sign_eq, he]
      ext (i | i) (j | j) <;> simp [Matrix.one_apply, mul_add]
    rw [diagonal_sign_eq, h_block]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, h_sign]
  have h_conj : 1 - (diagonal fun i : r' ↦ if t' i = σ then (1 : ℂ) else 0) * (1 - P * D * Pᴴ) =
      P * fromBlocks (1 - e * (1 - a • 1)) 0 0 (1 - Δ * (1 - M)) * Pᴴ := by
    have h_blocks : fromBlocks (1 - e * (1 - a • 1)) 0 0 (1 - Δ * (1 - M)) = 1 - Θ * (1 - D) := by
      simp only [hΘ, hD, h_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_multiply]
      simp
    have h_sub : 1 - P * D * Pᴴ = P * (1 - D) * Pᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
    rw [h_blocks, h_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h_proj]
    nth_rw 1 [← hP]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  have h_plane : (1 - e * (1 - a • 1)).det = a := by
    rw [det_unit_sum_unit]
    obtain rfl | rfl := Int.units_eq_one_or σ <;>
      simp [he, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type] <;> ring
  rw [principalMinor_eq_det, h_conj, det_conj_of_mul_eq_one hP hP', det_fromBlocks_zero₂₁,
    h_plane, principalMinor_eq_det]

end LinearAlgebra

section DetVector

variable {E : Type} [Field E] [CMType E] [WeilData E] {n r : Type} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

/-- The square matrix `u₊ F` at the infinite place `w`: the positive part of the point `u` of
`Hom(W, V)`, an `r × n` matrix at each place, times the `n × r` matrix `F w`. -/
def posCoordMatrix (s : n → ℤˣ) (t : r → ℤˣ) (F : InfinitePlace E → Matrix n r ℂ)
    (u : InfinitePlace E × r × n → ℂ) (w : InfinitePlace E) : Matrix r r ℂ :=
  (of fun i j ↦ (posProj (realSigns E (homSigns s t)) *ᵥ u) (w, i, j)) * F w

/-- The matrix of linear forms in the positive variables, with rows and columns indexed by the
basis vectors of sign `σ` of `V`, whose value at a point `u` is the block of sign `σ` of the
conjugate transpose of `posCoordMatrix s t F u w`. -/
def detPolyMatrix (s : n → ℤˣ) (t : r → ℤˣ) (F : InfinitePlace E → Matrix n r ℂ)
    (w : InfinitePlace E) (σ : ℤˣ) : Matrix {i : r // t i = σ} {i : r // t i = σ}
      (MvPolynomial {c : InfinitePlace E × r × n // realSigns E (homSigns s t) c = 1} ℂ) :=
  of fun l i ↦ ∑ j : {j : n // s j = σ},
    C (star (F w j l)) * X ⟨(w, i, j), by simp [pairSign, i.2, j.2]⟩

/-- The determinant polynomial: the product over the infinite places `w` of the `m w`-th power of
the determinant of `detPolyMatrix` on the positive block and the `(m w + 2 k)`-th power of that on
the negative block. -/
def detPoly (s : n → ℤˣ) (t : r → ℤˣ) (k : ℕ) (m : InfinitePlace E → ℕ)
    (F : InfinitePlace E → Matrix n r ℂ) :
    MvPolynomial {c : InfinitePlace E × r × n // realSigns E (homSigns s t) c = 1} ℂ :=
  ∏ w : InfinitePlace E, (detPolyMatrix s t F w 1).det ^ m w *
    (detPolyMatrix s t F w (-1)).det ^ (m w + 2 * k)

/-- The determinant vector: the Fock vector of the determinant polynomial. -/
def detVector (s : n → ℤˣ) (t : r → ℤˣ) (k : ℕ) (m : InfinitePlace E → ℕ)
    (F : InfinitePlace E → Matrix n r ℂ) : PairFock E s t :=
  polyVector (realSigns E (homSigns s t)) (rename Subtype.val (detPoly s t k m F))

variable {s : n → ℤˣ} {t : r → ℤˣ}

omit [WeilData E] in
/-- The value of the determinant vector at `u`: `realVac u` times the conjugate of the product of
the powers of the principal minors of `posCoordMatrix s t F u w` on the two blocks of signs. -/
lemma detVector_apply (k : ℕ) (m : InfinitePlace E → ℕ) (F : InfinitePlace E → Matrix n r ℂ)
    (u : InfinitePlace E × r × n → ℂ) :
    detVector s t k m F u =
      star (∏ w : InfinitePlace E, principalMinor (posCoordMatrix s t F u w) (t · = 1) ^ m w *
        principalMinor (posCoordMatrix s t F u w) (t · = -1) ^ (m w + 2 * k)) * realVac u := by
  have h_block (w : InfinitePlace E) (σ : ℤˣ) :
      (eval (holomorphicCoord (realSigns E (homSigns s t)) u ∘ Subtype.val)).mapMatrix
        (detPolyMatrix s t F w σ) =
        toSquareBlockProp (posCoordMatrix s t F u w)ᴴ (t · = σ) := by
    ext l i
    have h_split := Fintype.sum_subtype_add_sum_subtype (fun j : n ↦ s j = σ) fun j : n ↦
      (starRingEnd ℂ) (F w j l) * (starRingEnd ℂ) (if σ * s j = 1 then u (w, i, j) else 0)
    have h_zero : ∑ j : {j : n // ¬s j = σ},
        (starRingEnd ℂ) (F w j l) * (starRingEnd ℂ) (if σ * s j = 1 then u (w, i, j) else 0) = 0 :=
      Fintype.sum_eq_zero _ fun j ↦ by simp [units_int_mul_eq_one_iff, Ne.symm j.2]
    rw [h_zero, add_zero] at h_split
    simp [detPolyMatrix, posCoordMatrix, toSquareBlockProp, Matrix.mul_apply, holomorphicCoord_eq,
      posProj, mulVec_diagonal, pairSign, i.2, mul_comm, ← h_split, fun j : {j // s j = σ} ↦ j.2]
  have h_minor (w : InfinitePlace E) (σ : ℤˣ) :
      eval (holomorphicCoord (realSigns E (homSigns s t)) u ∘ Subtype.val)
        (detPolyMatrix s t F w σ).det =
        star (principalMinor (posCoordMatrix s t F u w) (t · = σ)) := by
    rw [RingHom.map_det, h_block, ← principalMinor, principalMinor_conjTranspose]
    rfl
  simp [detVector, detPoly, polyVector_apply, eval_rename, h_minor]

omit [WeilData E] [CMType E] [DecidableEq n] in
/-- A substitution that multiplies the rows of the positive variables by a block diagonal matrix
`g w` at each place multiplies the determinant of `detPolyMatrix` on the block of sign `σ` by the
principal minor of `g w` on that block. -/
lemma aeval_det_detPolyMatrix (F : InfinitePlace E → Matrix n r ℂ) {g : GInf E t}
    (hg : ∀ w : InfinitePlace E, (g w : Matrix r r ℂ) ∈ blockDiagAlg t)
    {sub : InfinitePlace E × r × n → MvPolynomial (InfinitePlace E × r × n) ℂ}
    (h_sub : ∀ (w : InfinitePlace E) (a : r) (b : n), t a = s b →
      sub (w, a, b) = ∑ i : r, (g w : Matrix r r ℂ) i a • X (w, i, b))
    (w : InfinitePlace E) (σ : ℤˣ) :
    aeval sub (rename Subtype.val (detPolyMatrix s t F w σ).det) =
      C (principalMinor (g w) (t · = σ)) * rename Subtype.val (detPolyMatrix s t F w σ).det := by
  have h_matrix : (aeval (sub ∘ Subtype.val)).mapMatrix (detPolyMatrix s t F w σ) =
      (rename Subtype.val).mapMatrix (detPolyMatrix s t F w σ) *
        (toSquareBlockProp (g w : Matrix r r ℂ) (t · = σ)).map C := by
    refine Matrix.ext fun l a ↦ ?_
    have h_var (j : {j : n // s j = σ}) : sub (w, a, j) =
        ∑ i : {i : r // t i = σ}, C ((g w : Matrix r r ℂ) i a) * X (w, (i : r), (j : n)) := by
      have h_split := Fintype.sum_subtype_add_sum_subtype (fun i : r ↦ t i = σ) fun i : r ↦
        (g w : Matrix r r ℂ) i a • (X (w, i, (j : n)) : MvPolynomial (InfinitePlace E × r × n) ℂ)
      have h_zero : ∑ i : {i : r // ¬t i = σ}, (g w : Matrix r r ℂ) i a •
          (X (w, (i : r), (j : n)) : MvPolynomial (InfinitePlace E × r × n) ℂ) = 0 :=
        Fintype.sum_eq_zero _ fun i ↦ by
          rw [mem_blockDiagAlg.1 (hg w) i a (fun h ↦ i.2 (h.trans a.2)), zero_smul]
      rw [h_sub w a j (a.2.trans j.2.symm), ← h_split, h_zero, add_zero]
      simp [smul_eq_C_mul]
    simp [detPolyMatrix, Matrix.mul_apply, toSquareBlockProp, h_var, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Fintype.sum_congr _ _ fun i ↦ Fintype.sum_congr _ _ fun j ↦ by ring
  rw [aeval_rename, AlgHom.map_det, h_matrix, det_mul, ← AlgHom.map_det, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, mul_comm]
  rfl

omit [WeilData E] in
/-- Let `card n = 2 (k + q)`, with `q` the number of negative signs of `s`. A point `g` of the
archimedean unitary group of `V` whose components are block diagonal for the signs `t`, acting in
the real Weil representation of weight `targetWeight n μ` on the target and `0` on the source, with
`μ w = k + m w`, fixes the determinant vector. -/
lemma realPairWeil_detVector {k : ℕ} (hn : card n = 2 * (k + negCount s))
    (m : InfinitePlace E → ℕ) {μ : InfinitePlace E → ℤ} (hμ : ∀ w : InfinitePlace E, μ w = k + m w)
    (F : InfinitePlace E → Matrix n r ℂ) {g : GInf E t}
    (hg : ∀ w : InfinitePlace E, (g w : Matrix r r ℂ) ∈ blockDiagAlg t) :
    realPairWeil (targetWeight n μ) 0 (1, g) (detVector s t k m F) = detVector s t k m F := by
  have h_card_pos : card {i : n // s i = 1} = 2 * k + negCount s := by
    have h_sum := negCount_neg_add (a := s)
    have h_eq : negCount (-s) = card {i : n // s i = 1} := by simp [negCount]
    omega
  have h_exp_pos (w : InfinitePlace E) :
      targetWeight n μ w - Nat.card {i : n // s i = -1} = -(m w : ℤ) := by
    have h_half : card n / 2 = k + negCount s := by omega
    simp [targetWeight, h_half, hμ w, negCount]
    ring
  have h_exp_neg (w : InfinitePlace E) :
      targetWeight n μ w - Nat.card {i : n // s i = - -1} = -((m w + 2 * k : ℕ) : ℤ) := by
    have h_half : card n / 2 = k + negCount s := by omega
    simp [targetWeight, h_half, hμ w, h_card_pos]
    ring
  have h_ne (w : InfinitePlace E) (σ : ℤˣ) : principalMinor (g w) (t · = σ) ≠ 0 := by
    intro h_zero
    have h_det := det_eq_prod_principalMinor (hg w)
    rw [Finset.prod_eq_zero (Finset.mem_univ σ) h_zero] at h_det
    exact (g w : GL r ℂ).det_ne_zero h_det
  have h_poly (sub : InfinitePlace E × r × n → MvPolynomial (InfinitePlace E × r × n) ℂ)
      (h_sub : ∀ (w : InfinitePlace E) (a : r) (b : n), t a = s b →
        sub (w, a, b) = ∑ i : r, (g w : Matrix r r ℂ) i a • X (w, i, b)) :
      aeval sub (rename Subtype.val (detPoly s t k m F)) =
        C (∏ w : InfinitePlace E, principalMinor (g w) (t · = 1) ^ m w *
          principalMinor (g w) (t · = -1) ^ (m w + 2 * k)) *
          rename Subtype.val (detPoly s t k m F) := by
    simp only [detPoly, map_prod, map_mul, map_pow, aeval_det_detPolyMatrix F hg h_sub, mul_pow,
      Finset.prod_mul_distrib]
    ring
  rw [detVector, realPairWeil_polyVector _ _ (fun w ↦ by simp) hg, h_poly]
  swap
  · intro w a b hab
    simp [hab, Matrix.one_apply]
  rw [← smul_eq_C_mul, map_smul, smul_smul]
  have h_one : ((1 : ℤˣ) : ℤˣ) ≠ -1 := by decide
  simp only [Pi.one_apply, OneMemClass.coe_one, Units.val_one, principalMinor_one, _root_.one_zpow,
    mul_one, Finset.prod_pair h_one, h_exp_pos, h_exp_neg, _root_.zpow_neg, zpow_natCast]
  rw [← Finset.prod_mul_distrib]
  have h_factor (w : InfinitePlace E) :
      (principalMinor (g w) (t · = 1) ^ m w)⁻¹ *
        (principalMinor (g w) (t · = -1) ^ (m w + 2 * k))⁻¹ *
        (principalMinor (g w) (t · = 1) ^ m w *
          principalMinor (g w) (t · = -1) ^ (m w + 2 * k)) = 1 := by
    have h₁ := pow_ne_zero (m w) (h_ne w 1)
    have h₂ := pow_ne_zero (m w + 2 * k) (h_ne w (-1))
    field_simp
  simp [h_factor]

end DetVector

section ConeIntegral

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r']
  [DecidableEq r'] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s}
  {W' : Space E n' s'} {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit)
  (X : V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X]

omit [WeilData E] in
/-- The component at an infinite place of a product of adelic matrices is the product of the
components. -/
lemma atRealPlace_mul {a b c : Type} [Fintype b] (M : Matrix a b (𝔸 E)) (N : Matrix b c (𝔸 E))
    (w : InfinitePlace E) : atRealPlace (M * N) w = atRealPlace M w * atRealPlace N w := by
  ext i j
  simp [Matrix.mul_apply, Prod.fst_sum]

/-- The point of the real mixed model of `lineTermSplitting` with coordinate `a w` on the line at
each infinite place `w` and `0` elsewhere. -/
def lineCoord (n r : Type) (a : InfinitePlace E → ℂ) : InfinitePlace E × LineIndex n r → ℂ :=
  fun p ↦ a p.1 * p.2.isRight.toNat

/-- The entries at the infinite place `w` of the point `framePoint h (-x) u (-x)`, for the adapted
frame `h` of `lineTermSplitting A X β` and `x` equal to `a` on the line and `0` elsewhere. -/
lemma framePoint_lineTermSplitting_apply (β : Bool) (a : InfinitePlace E → ℂ)
    (u : InfinitePlace E × r × n → ℂ) (w : InfinitePlace E) (i : r') (j : n') :
    framePoint (isAdapted_lineTermSplitting A X β) (-lineCoord n r a) u (-lineCoord n r a)
        (w, i, j) =
      -(a w * ((X.lAdelic i ()).1 w * (A.lCoord () j).1 w +
        (X.kAdelic i ()).1 w * (A.kCoord () j).1 w)) +
      ∑ i₀ : r, ∑ j₀ : n, (X.iAdelic i i₀).1 w * u (w, i₀, j₀) * (A.iCoord j₀ j).1 w := by
  have h_sum : ∑ i₀ : r, ∑ j₀ : n, (X.iAdelic i i₀).1 w * (A.iCoord j₀ j).1 w * u (w, i₀, j₀) =
      ∑ i₀ : r, ∑ j₀ : n, (X.iAdelic i i₀).1 w * u (w, i₀, j₀) * (A.iCoord j₀ j).1 w :=
    Fintype.sum_congr _ _ fun _ ↦ Fintype.sum_congr _ _ fun _ ↦ by ring
  rw [framePoint_eq_mulVec, frameAt_lineTermSplitting, ← h_sum]
  cases β <;> simp [lineCoord, realMatrix, mulVec, dotProduct, blockDiagonal, sum_prod_type,
    vecToMatrix, add_comm] <;> ring

/-- The matrices `G w` of the determinant vector one floor up: minus the identification of the two
hyperbolic planes, plus `F w` between the images of `W` and `V`. -/
def liftFrame (F : InfinitePlace E → Matrix n r ℂ) (w : InfinitePlace E) : Matrix n' r' ℂ :=
  -(atRealPlace (A.lAdelic.fromCols A.kAdelic) w *
      (atRealPlace (X.lAdelic.fromCols X.kAdelic) w)ᴴ) +
    atRealPlace A.iAdelic w * F w * (atRealPlace X.iAdelic w)ᴴ

/-- At the point `-L x + I u - K x` of the mixed model of `lineTermSplitting A X β`, with `x` equal
to `a` on the line, the matrix `posCoordMatrix` of `liftFrame A X F` is, in the adapted frame of
`X`, the block matrix of the scalar `a w` on the hyperbolic plane and the matrix `posCoordMatrix`
of `F` at `u`. -/
lemma posCoordMatrix_liftFrame (β : Bool) (a : InfinitePlace E → ℂ)
    (F : InfinitePlace E → Matrix n r ℂ) (u : InfinitePlace E × r × n → ℂ) (w : InfinitePlace E) :
    posCoordMatrix s' t' (liftFrame A X F)
        (framePoint (isAdapted_lineTermSplitting A X β) (-lineCoord n r a) u (-lineCoord n r a))
        w =
      atRealPlace (X.frameAt 1 1) w *
        fromBlocks (a w • (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ)) 0 0
          (posCoordMatrix s t F u w) * (atRealPlace (X.frameAt 1 1) w)ᴴ := by
  set U : Matrix r n ℂ :=
    of fun i j ↦ (posProj (realSigns E (homSigns s t)) *ᵥ u) (w, i, j) with hU
  set xp : Matrix r' (Unit ⊕ Unit) ℂ := atRealPlace (X.lAdelic.fromCols X.kAdelic) w with hxp
  set xi : Matrix r' r ℂ := atRealPlace X.iAdelic w with hxi
  set cp : Matrix (Unit ⊕ Unit) n' ℂ := atRealPlace (A.lCoord.fromRows A.kCoord) w with hcp
  set ci : Matrix n n' ℂ := atRealPlace A.iCoord w with hci
  set ap : Matrix n' (Unit ⊕ Unit) ℂ := atRealPlace (A.lAdelic.fromCols A.kAdelic) w with hap
  set ai : Matrix n' n ℂ := atRealPlace A.iAdelic w with hai
  -- The positive part of the point, as a matrix at the place `w`.
  have h_point : (of fun i j ↦ (posProj (realSigns E (homSigns s' t')) *ᵥ
      framePoint (isAdapted_lineTermSplitting A X β) (-lineCoord n r a) u (-lineCoord n r a))
        (w, i, j)) = -(a w • (xp * cp)) + xi * U * ci := by
    rw [posProj_mulVec_framePoint, midpoint_self]
    ext i j
    simpa [framePoint_lineTermSplitting_apply, Matrix.mul_apply, Fintype.sum_sum_type, hxp, hcp,
      hxi, hci, hU, Finset.sum_mul] using Finset.sum_comm
  -- The coordinates of `A` are dual to its frames.
  obtain ⟨⟨h_kk, h_kl, h_ki⟩, ⟨h_lk, h_ll, h_li⟩, h_ik, h_il, h_ii⟩ := A.coord_mul_frame
  have h_pp : cp * ap = 1 := by
    rw [hcp, hap, ← atRealPlace_mul, fromRows_mul_fromCols, h_ll, h_lk, h_kl, h_kk, fromBlocks_one]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h_pi : cp * ai = 0 := by
    rw [hcp, hai, ← atRealPlace_mul, fromRows_mul, h_li, h_ki]
    ext (i | i) j <;> simp
  have h_ip : ci * ap = 0 := by
    rw [hci, hap, ← atRealPlace_mul, Matrix.mul_fromCols, h_il, h_ik]
    ext i (j | j) <;> simp
  have h_one : ci * ai = 1 := by
    rw [hci, hai, ← atRealPlace_mul, h_ii]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h₁ : xp * cp * (ap * xpᴴ) = xp * xpᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc cp, h_pp, Matrix.one_mul]
  have h₂ : xp * cp * (ai * F w * xiᴴ) = 0 := by
    rw [Matrix.mul_assoc xp, ← Matrix.mul_assoc cp, ← Matrix.mul_assoc cp, h_pi]
    simp
  have h₃ : xi * U * ci * (ap * xpᴴ) = 0 := by
    rw [Matrix.mul_assoc _ ci, ← Matrix.mul_assoc ci, h_ip]
    simp
  have h₄ : xi * U * ci * (ai * F w * xiᴴ) = xi * (U * F w) * xiᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ci ai, h_one, Matrix.one_mul]
  have h_frame : atRealPlace (X.frameAt 1 1) w = fromCols xp xi := by
    simp [Splitting.frameAt, G.adeleMatrix_one, fromCols_map, hxp, hxi]
  rw [posCoordMatrix, h_point, liftFrame, ← hap, ← hxp, ← hai, ← hxi, h_frame,
    fromCols_mul_fromBlocks,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows, posCoordMatrix]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul,
    h₁, h₂, h₃, h₄]
  simp
  rfl

/-- The real line term `lineTermReal A X β a`, in either model `β`, sends the determinant vector of
`liftFrame A X F` to that of `F`, times `exp (-∑ |a w|²) ∏ conj (a w) ^ (2 (k + m w))`. -/
lemma lineTermReal_detVector (β : Bool) (a : InfinitePlace E → ℂ) (k : ℕ)
    (m : InfinitePlace E → ℕ) (F : InfinitePlace E → Matrix n r ℂ) :
    lineTermReal A X β a (detVector s' t' k m (liftFrame A X F)) =
      (Real.exp (-∑ w : InfinitePlace E, ‖a w‖ ^ 2) *
        ∏ w : InfinitePlace E, star (a w) ^ (2 * (k + m w)) : ℂ) • detVector s t k m F := by
  ext u
  let y : InfinitePlace E × r' × n' → ℂ :=
    framePoint (isAdapted_lineTermSplitting A X β) (-lineCoord n r a) u (-lineCoord n r a)
  -- The line term is the slice at `lineCoord n r a`, so on polynomial vectors it evaluates at `y`.
  have h_eval (P : MvPolynomial
      {i : InfinitePlace E × r' × n' // realSigns E (homSigns s' t') i = 1} ℂ) :
      lineTermReal A X β a (polyVector _ (rename Subtype.val P)) u =
        (polyVector _ (rename Subtype.val P) : PairFock E s' t') y := by
    rw [lineTermReal]
    exact slice_polyVector_apply (isAdapted_lineTermSplitting A X β) (lineCoord n r a) u P
  have h_vac : realVac y = Real.exp (-∑ w : InfinitePlace E, ‖a w‖ ^ 2) * realVac u := by
    simpa [lineTermReal, star_dotProduct_self_eq_sum, slice_vac, lineCoord, sum_prod_type, mul_pow,
      vacElem_apply, IsVacuum.smul_apply] using (h_eval 1).symm
  have hX : X.IsAdapted 1 1 := by
    simp [IsAdapted, Splitting.frameAt, G.adeleMatrix_one, IsBaseAdapted.isOrthoIntegral]
  have h_minor (w : InfinitePlace E) (σ : ℤˣ) :
      principalMinor (posCoordMatrix s' t' (liftFrame A X F) y w) (t' · = σ) =
        a w * principalMinor (posCoordMatrix s t F u w) (t · = σ) := by
    rw [show posCoordMatrix s' t' (liftFrame A X F) y w = _ from
      posCoordMatrix_liftFrame A X β a F u w]
    exact principalMinor_conj_fromBlocks (frameAt_real_mul_conjTranspose hX w) (hX.1 w)
      (signMatrix_mul_frameAt_real hX w) (a w) _ σ
  have h_prod : ∏ w : InfinitePlace E,
      (a w * principalMinor (posCoordMatrix s t F u w) (t · = 1)) ^ m w *
        (a w * principalMinor (posCoordMatrix s t F u w) (t · = -1)) ^ (m w + 2 * k) =
      (∏ w : InfinitePlace E, a w ^ (2 * (k + m w))) *
        ∏ w : InfinitePlace E, principalMinor (posCoordMatrix s t F u w) (t · = 1) ^ m w *
          principalMinor (posCoordMatrix s t F u w) (t · = -1) ^ (m w + 2 * k) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ ↦ by ring
  calc lineTermReal A X β a (detVector s' t' k m (liftFrame A X F)) u
      = detVector s' t' k m (liftFrame A X F) y := h_eval _
    _ = ((Real.exp (-∑ w : InfinitePlace E, ‖a w‖ ^ 2) *
          ∏ w : InfinitePlace E, star (a w) ^ (2 * (k + m w)) : ℂ) • detVector s t k m F) u := by
      rw [IsVacuum.smul_apply, detVector_apply, detVector_apply]
      simp only [h_minor, h_prod, h_vac, star_mul', star_prod, star_pow]
      ring

/-- Let `card n' = 2 (k + q')`, with `q'` the number of negative signs of `s'`, and `μ w = k + m w`.
The cone integrand at `p = (κ, a)` of the determinant vector of `liftFrame A X F`, in either model
`β` and for every real exponent `z`, is the determinant vector of `F` times the positive number
`exp (-∑ |a w|²) |a| ^ z ∏ |a w| ^ (2 (k + m w))`. -/
theorem coneIntegrand_detVector (β : Bool) (z : ℝ) {k : ℕ}
    (hn : card n' = 2 * (k + negCount s')) (m : InfinitePlace E → ℕ) {μ : InfinitePlace E → ℤ}
    (hμ : ∀ w : InfinitePlace E, μ w = k + m w) (F : InfinitePlace E → Matrix n r ℂ)
    (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) :
    coneIntegrand A X μ β z (detVector s' t' k m (liftFrame A X F)) p =
      (Real.exp (-∑ w : InfinitePlace E, ‖p.2.val w‖ ^ 2) * ideleAbs (realIdele p.2) ^ z *
        ∏ w : InfinitePlace E, normSq (p.2.val w) ^ (k + m w)) • detVector s t k m F := by
  obtain ⟨κ, a⟩ := p
  have h_phase (w : InfinitePlace E) :
      (a.val w / ‖a.val w‖) ^ (2 * μ w) * star (a.val w) ^ (2 * (k + m w)) =
        (normSq (a.val w) ^ (k + m w) : ℝ) := by
    have h_sq : (a.val w / ‖a.val w‖) ^ 2 * star (a.val w) ^ 2 = normSq (a.val w) := by
      rw [← mul_pow, div_mul_eq_mul_div, star_def, mul_conj', normSq_eq_norm_sq, ofReal_pow]
      field_simp [piUnits_val_apply_ne_zero]
    rw [hμ w, ofReal_pow, ← h_sq, mul_pow, ← pow_mul, ← pow_mul]
    norm_cast
  rw [coneIntegrand,
    realPairWeil_detVector hn m hμ _ fun w ↦ mem_maxCompactU.1 (κ.prop.1 w trivial),
    lineTermReal_detVector, smul_smul, ← Complex.coe_smul]
  congr 1
  simp only [ofReal_mul, ofReal_prod, ← h_phase, prod_mul_distrib]
  ring

omit [WeilData E] in
/-- All weighted norms of a multiple of a determinant vector are finite. -/
lemma isSchwartzVector_smul_detVector (c : ℂ) (k : ℕ) (m : InfinitePlace E → ℕ)
    (F : InfinitePlace E → Matrix n r ℂ) : IsSchwartzVector (c • detVector s t k m F) := fun N ↦ by
  rw [detVector]
  simpa only [fockMoment_smul] using
    ENNReal.mul_ne_top eNorm_ne_top (fockMoment_polyVector_ne_top N _)

omit [WeilData E] in
/-- For a space `V` of rank zero the determinant vector is the vacuum. -/
lemma detVector_of_isEmpty [IsEmpty r] (k : ℕ) (m : InfinitePlace E → ℕ)
    (F : InfinitePlace E → Matrix n r ℂ) : detVector s t k m F = vacVector := by
  simp [detVector, detPoly]

/-- Determinant vectors are cone integrals of determinant vectors one floor up. Let
`card n' = 2 (k + q')`, with `q'` the number of negative signs of `s'`, let `μ w = k + m w` and
`0 < z`. In either model `β` of the summation formula on the line, every multiple of a determinant
vector of `(W, V)` is the integral of the cone integrand of a multiple of a determinant vector of
`(W', V')`. -/
theorem exists_integral_coneIntegrand_detVector (β : Bool) {z : ℝ} (hz : 0 < z) {k : ℕ}
    (hn : card n' = 2 * (k + negCount s')) (m : InfinitePlace E → ℕ) {μ : InfinitePlace E → ℤ}
    (hμ : ∀ w : InfinitePlace E, μ w = k + m w) (F : InfinitePlace E → Matrix n r ℂ) (c : ℂ) :
    ∃ c' : ℂ, ∫ p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ,
      coneIntegrand A X μ β z (c' • detVector s' t' k m (liftFrame A X F)) p
        ∂Measure.haar.prod Measure.haar = c • detVector s t k m F := by
  have h_smul (c' : ℂ) (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) :
      coneIntegrand A X μ β z (c' • detVector s' t' k m (liftFrame A X F)) p =
        c' • coneIntegrand A X μ β z (detVector s' t' k m (liftFrame A X F)) p := by
    simp only [coneIntegrand, map_smul]
    rw [smul_comm]
  by_cases h_zero : detVector s t k m F = 0
  · exact ⟨0, by simp_rw [h_smul, zero_smul, integral_zero, h_zero, smul_zero]⟩
  -- The cone integrand is a positive function `ρ` times the determinant vector of `F`.
  let ρ (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) : ℝ :=
    Real.exp (-∑ w : InfinitePlace E, ‖p.2.val w‖ ^ 2) * ideleAbs (realIdele p.2) ^ z *
      ∏ w : InfinitePlace E, normSq (p.2.val w) ^ (k + m w)
  have hρ_pos (p : maxCompact E t' × (InfinitePlace E → ℂ)ˣ) : 0 < ρ p :=
    mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ideleAbs_pos _))
      (Finset.prod_pos fun w _ ↦ pow_pos (normSq_pos.2 (piUnits_val_apply_ne_zero _ _)) _)
  have h_integrand : coneIntegrand A X μ β z (detVector s' t' k m (liftFrame A X F)) =
      fun p ↦ ρ p • detVector s t k m F :=
    funext fun p ↦ coneIntegrand_detVector A X β z hn m hμ F p
  have h_integrable : Integrable ρ (Measure.haar.prod Measure.haar) := by
    have h_schwartz : IsSchwartzVector (detVector s' t' k m (liftFrame A X F)) :=
      fun N ↦ fockMoment_polyVector_ne_top N _
    have h_cone := (integrable_coneIntegrand A X μ β hz h_schwartz).1
    rw [h_integrand] at h_cone
    exact (integrable_smul_const h_zero).1 h_cone
  have h_pos : 0 < ∫ p, ρ p ∂Measure.haar.prod Measure.haar := by
    have h_exp : ρ = fun p ↦ Real.exp (Real.log (ρ p)) :=
      funext fun p ↦ (Real.exp_log (hρ_pos p)).symm
    rw [h_exp]
    exact integral_exp_pos (by rwa [← h_exp])
  refine ⟨c * ((∫ p, ρ p ∂Measure.haar.prod Measure.haar : ℝ) : ℂ)⁻¹, ?_⟩
  simp only [h_smul, h_integrand]
  rw [integral_smul, integral_smul_const, ← Complex.coe_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 h_pos.ne'), mul_one]

end ConeIntegral

end New.Exchange

end
