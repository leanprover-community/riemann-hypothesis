module

import Mathlib.Data.Finset.Slice
public import New.OneLift.ComparisonOperator.GluedLattices
import Lib.General.LinearAlgebra.MatrixNormBounds

/-!
# Gluing: the descent of product forms and the denominators

This file treats forms on the definite space `V = V″ ⊕ V°` glued, in
`New.OneLift.ComparisonOperator.GluedLattices`, from a vector for `V″` and a vector for `V°`
across a change of lattice at the chosen places.

The data are a descent pair `O` (`New.DescentPair`), with the space `W = O.W` of rank `r`, and a
splitting `V : New.Rows.DividedSplitting N m a O z`. Here `N` indexes `V″`, `m` indexes `V°`,
`z : r ↪ m` marks `r` basis vectors of `V°`, and `a` indexes the rows of a matrix `s` modulo `ϖ²`,
the linear forms on `V″` on which a finer congruence is imposed. The idele `ϖ = O.genIdele`
generates the product of the chosen places `O.chosenPlace i`, and `Q` is the product of the places
`O.twistPlace i`. We write `(1; 0)` for an inclusion matrix `New.inclMatrix` with `r` columns.

The datum of the theta lift from `W` to `V` asks for `x ≡ (1; 0)` modulo `ϖ`. A product datum asks
for conditions modulo `ϖ²` on the two blocks of `x`. The lattice that connects them is spanned by
the columns of the matrix that is `(1; 0)` on both summands, by `L″_s = {u | s u ≡ 0 modulo ϖ}` in
`V″` and by `ϖ` times the standard lattice of `V°`. The matrix of a basis is called `γ`, and it is
handled through the integral matrix `ϖ γ⁻¹`.

This file computes the descent to `W` of product forms on a glued lattice, from which the slices
of a lift are read off. It also bounds the p-adic gauge of the Cartan product at the point
`(h, h') γ`.

## Main definitions and results

* Slices of lifts. `New.Rows.DividedSplitting.normalizedDescent_productForm`: if `V.IsGlued s L` and
  `b * b' = O.charV`, the descent to `W` of a product form is the complex conjugate of the product
  of `L.weilScalar` with a sum over the congruence group, whose terms are products of a kernel on
  `V″` and one on `V°`. `New.Rows.DividedSplitting.normalizedDescent_stdClassSum_productForm`: the
  same for the sum of product forms over the classes, with `New.Rows.kernelClassSum` on `V″`.
* The denominators. `New.Rows.DividedSplitting.weylGauge_cartanProduct_le`: for a glued lattice, a
  natural number `M ≠ 0` divisible by `ϖ` and points `h`, `h'` on the two summands, the gauge of
  the product of two vectors at the point `(h, h') γ` (with `(h, h')` made block diagonal along
  `V.ε : N ⊕ m ≃ n`) is at most `‖M‖⁻¹ ^ V.denominatorExponent` times their gauges.

Notions from other files:
* `New.DescentPair`: A descent pair: chosen places and twist places, a space W of rank r with
  numbered basis vectors, an embedding of indices into n > r, two diagrams given by their numbers of
  columns of each height, and a character μ whose tame part, a character `O.tamePart w` of the
  residue field at each place w, is trivial off these places.
* `New.LevelPlaces.levelModulus`, `New.Rows.liftMod`: `levelModulus c` is the modulus ϖ^c·Q, and
  `levelModulus c false` is ϖ^c. `liftMod` is a chosen lift of an invertible matrix modulo an
  ideal to an integral point of G_f that is 1 outside the places dividing the ideal and their
  conjugates.
* `New.inclMatrix`: For a map u: m → n of index sets, the n×m matrix whose j-th column is the
  standard basis vector e_{u(j)}.
* `New.modKernel`: The theta kernel at (g, h) of the datum given by a function on matrices modulo an
  ideal and the Fock vector of a polynomial.
* `New.WeylIndex`: `WeylIndex n κ` indexes the standard basis of the vectors of weight κ in n
  letters. Here `κ τ h` is the number of columns of height h at the infinite place τ.

## Relation to the literature

See `New.OneLift.ComparisonOperator.GluingMaps` and
`New.OneLift.ComparisonOperator.FirstFactors` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Rows

/-!
## The descent of product forms

The descent `O.normalizedDescent` pairs a form on `V` with the theta kernel; it is adjoint to the
lift from `W`. So the slices of a lift are read off from the descents of product forms.

* `New.Rows.DividedSplitting.normalizedDescent_classForm_mul`: the descent of the form supported on
  the class of `h * L.point` is the complex conjugate of the product of `L.weilScalar` with a kernel
  at `h`. The datum of the kernel at `S` is nonzero only when `(ϖ γ⁻¹) S ≡ ϖ (1; 0)` modulo `ϖ²`.
  There it is a product of values of `O.tamePart` on determinants at the places of `Q`.
* `New.Rows.fockPoly_cartanProduct`: the Fock polynomial of the product of a vector on `V″` and a
  vector on `V°` is the product of their polynomials.
-/

section GluedFormTheta

open Matrix ComplexConjugate Finset Modulus MvPolynomial Sum

variable {E r n N m a : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] [Fintype N] [DecidableEq N] [Fintype m]
  {O : DescentPair E r n} {z : r ↪ m} (V : DividedSplitting N m a O z) {L : DividedLattice O}

omit [DecidableEq n] in
/-- The kernel `kernelClassSum` of `c • y` is `c` times that of `y`. It is the sum, over classes `h`
of the level fixing the rows `w` and the columns off `e`, of the theta kernel of W (signs `O.signs`)
and the standard space on `m`, with character `b` on the latter and the polynomial of `y h`. -/
lemma kernelClassSum_smul [DecidableEq m] [WeilData E]
    (b : AutChar E) (w : Matrix a m O.chosenModulusSq.ResidueRing) (e : r ↪ m)
    (c : ℂ) (y : Gf E m → WeylIndex m O.colsPlus → ℂ) (g : G E O.signs) :
    kernelClassSum O b w e (fun h : Gf E m ↦ c • y h) g = c * kernelClassSum O b w e y g := by
  simp [kernelClassSum, mul_classSum, ← modKernelBilin_apply]

omit [DecidableEq r] in
/-- Let `f : N → n` map the letters `N` to the letters `n`, and let `κ` satisfy
`HasColumnsBelow n N κ`: `#N ≤ #n`, and `κ` has no column of a height `h` with `#N ≤ h < #n`. The
polynomial `letterPoly` of the image of `y` under the Schur matrix of the inclusion matrix of `f` is
the polynomial of `y` with the rows of its variables renamed along `f`. -/
lemma letterPoly_schur_inclMatrix_mulVec {Φ : Type} [Fintype Φ] [DecidableEq Φ] {κ : Φ → ℕ → ℕ}
    (hκ : HasColumnsBelow n N κ) (s : r → ℤˣ) (ord : r → ℕ) (c : ℤˣ) (f : N → n)
    (y : WeylIndex N κ → ℂ) :
    letterPoly s ord c κ (schur κ (fun _ : Φ ↦ inclMatrix ℂ f) *ᵥ y) =
      renameRowsCols f id (letterPoly s ord c κ y) := by
  -- The Schur matrix acts on polynomials by substituting the transpose, with no determinant factor.
  have h_toPoly : toPoly (fun _ : Φ ↦ n) κ (schur κ (fun _ : Φ ↦ inclMatrix ℂ f) *ᵥ y) =
      rowSubst (fun _ : Φ ↦ (inclMatrix ℂ f)ᵀ) (toPoly (fun _ : Φ ↦ N) κ y) := by
    rw [toPoly_schur hκ.fitsRanks, hκ.schurDetExp_eq_zero, detPow_zero, mul_one]
  -- This substitution sends the variable in row `i` to that in row `f i`.
  rw [letterPoly, letterPoly, LinearMap.comp_apply, LinearMap.comp_apply, h_toPoly]
  simp [rowSubst, fockLetters, inclMatrix, comp_aeval_apply, Matrix.one_apply]

/-- Let `ε : N ⊕ m ≃ n` split the indices of `V = V″ ⊕ V°`, and let `O.colsPlus` and `O.colsMinus`
satisfy `HasColumnsBelow`: each column of height below the rank of `V` has height below the rank of
`V″`, respectively of `V°`. For `y` of weight `O.colsPlus` on `V″` and `η` of weight `O.colsMinus`
on `V°`, the polynomial `O.fockPoly` of `cartanProduct ε 1 y η` is the polynomial `letterPoly` of
`y` in the variables of the basis vectors of `O.W` of sign `1` on the rows of `V″`, times that of
`η` in the variables of sign `-1` on the rows of `V°`. -/
lemma fockPoly_cartanProduct [DecidableEq m] (h_plus : HasColumnsBelow n N O.colsPlus)
    (h_minus : HasColumnsBelow n m O.colsMinus) (ε : N ⊕ m ≃ n)
    (y : WeylIndex N O.colsPlus → ℂ) (η : WeylIndex m O.colsMinus → ℂ) :
    O.fockPoly (cartanProduct ε 1 y η) =
      renameRowsCols (ε ∘ inl) id (letterPoly O.signs O.numbering 1 O.colsPlus y) *
        renameRowsCols (ε ∘ inr) id (letterPoly O.signs O.numbering (-1) O.colsMinus η) := by
  -- The polynomial is read on the image under `mixedCartan`, the tensor of the included vectors.
  calc O.fockPoly (cartanProduct ε 1 y η)
    _ = O.tensorPoly ((mixedCartan n O.colsPlus O.colsMinus).matrix.map (↑) *ᵥ
          cartanProduct ε 1 y η) := rfl
    _ = letterPoly O.signs O.numbering 1 O.colsPlus
            (schur O.colsPlus (fun _ ↦ inclMatrix ℂ (ε ∘ inl)) *ᵥ y) *
          letterPoly O.signs O.numbering (-1) O.colsMinus
            (schur O.colsMinus (fun _ ↦ inclMatrix ℂ (ε ∘ inr)) *ᵥ η) := by
      rw [mixedCartan_mulVec_cartanProduct h_plus h_minus, transpose_vecMulVec,
        DescentPair.tensorPoly_vecMulVec]
    _ = _ := by
      rw [letterPoly_schur_inclMatrix_mulVec h_plus, letterPoly_schur_inclMatrix_mulVec h_minus]

namespace DividedSplitting

/-- Let `ϖ` generate the product of the chosen places of `O`, let `Q` be the product of its twist
places, and let `idem` be the adele that is `1` at the places dividing `ϖ² Q = O.levelModulus 2` and
`0` elsewhere. Let `γ = L.point` be a unitary point at the chosen places with `ϖ γ⁻¹` integral. If
`idem * (γ⁻¹ x)` has integral entries, then so has `idem * x`. -/
lemma idem_mul_mem_of_inv_mul_mem (x : Matrix n r (𝔸f E))
    (hx : ∀ (k : n) (j : r),
      idem (O.levelModulus 2).places * (L.point⁻¹.val.val * x) k j ∈ Ô E) (i : n) (j : r) :
    idem (O.levelModulus 2).places * x i j ∈ Ô E := by
  -- By unitarity the conjugate of `ϖ γ⁻¹` is `conj ϖ • γᵀ`, which is integral. Here `conj ϖ` is
  -- `1` at a place `w` of the level, as `star w` is not a chosen place.
  refine idem_mul_mem_Ô.2 fun w hw ↦ ?_
  have hπ : O.genIdele.val (star w) = 1 :=
    genIdele_apply_of_notMem fun ⟨t, ht⟩ ↦
      (isConjDisjoint_places _).le_bot ⟨hw, places_levelModulus.ge ⟨inl t, ht⟩⟩
  have h_int (k : n) : star (O.genIdele * L.point.val.valᴴ k i) ∈ Ô E := by
    rw [← U.inv_val_eq_conjTranspose]
    exact star_mem_Ô (L.mul_inv_mem k i)
  have h_sum : ∑ k : n, star (O.genIdele * L.point.val.valᴴ k i) *
      (idem (O.levelModulus 2).places * (L.point⁻¹.val.val * x) k j) ∈ Ô E :=
    sum_mem fun k _ ↦ mul_mem (h_int k) (hx k j)
  simpa [mul_assoc, mul_left_comm _ (idem _), ← mul_sum, ← Matrix.mul_apply,
    ← Matrix.mul_assoc, hw, hπ] using mem_Ô.1 h_sum w

omit [DecidableEq N] in
/-- Let `ϖ` generate the product of the chosen places, with class `V.genResidue` modulo `ϖ²`, let
`Q` be the product of the twist places, and let `ι` be the inclusion matrix of `O.incl : r ↪ n`. The
map `liftFn` extends a function on matrices modulo `ϖ² Q` to adelic vectors `x`, by `0` where `x` is
not integral at the places of `ϖ² Q`. Consider two functions of `T`, supported on `ϖ T ≡ ϖ ι` and on
`(ϖ γ⁻¹) T ≡ ϖ ι` modulo `ϖ²`, where `γ = L.point` and `L.reducedInverse` is `ϖ γ⁻¹` modulo `ϖ²`. On
its support each is the product over the twist places of the residue characters `O.tamePart` at the
determinant of the rows `O.incl` of `T`. Then the extension of the first at `γ⁻¹ x` equals that of
the second at `x`. -/
lemma liftFn_datum_point_inv_mul (x : n × r → 𝔸f E) :
    (O.levelModulus 2).liftFn
        ((fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if V.genResidue • T.map reduceToChosenModulusSq =
              V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
            ∏ i : O.TwistIndex, O.tamePart (O.placeAt (inr i))
              ((T.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0) ∘ vecToMatrix)
        (matrixToVec (L.point⁻¹.val.val * vecToMatrix x)) =
      (O.levelModulus 2).liftFn
        ((fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if L.reducedInverse * T.map reduceToChosenModulusSq =
              V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
            ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
              ((T.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0) ∘ vecToMatrix) x := by
  classical
  -- Each side is `0` unless its vector, `γ⁻¹ x` or `x`, is integral on the level.
  simp only [liftFn_apply, Function.comp_apply, Prod.forall]
  have h_entry (hx : ∀ (i : n) (j : r), idem (O.levelModulus 2).places * x (i, j) ∈ Ô E)
      (i : n) (j : r) :
      (L.reducedInverse *
          (vecToMatrix fun p ↦ (O.levelModulus 2).reduction
            ⟨idem (O.levelModulus 2).places * x p, hx p.1 p.2⟩).map reduceToChosenModulusSq) i j =
        O.chosenModulusSq.reduction
          (∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
            ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩) := by
    rw [Matrix.mul_apply]
    change _ = O.chosenModulusSq.reduction.toAddMonoidHom _
    rw [map_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [DividedLattice.reducedInverse, of_apply, Matrix.map_apply, vecToMatrix, of_apply,
      factor_reduction]
    exact (RingHom.map_mul ..).symm
  have h_sum_val (hx : ∀ (i : n) (j : r), idem (O.levelModulus 2).places * x (i, j) ∈ Ô E)
      (i : n) (j : r) :
      ((∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
          ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩ : Ô E) : 𝔸f E) =
        O.genIdele.val *
          (idem (O.levelModulus 2).places * (L.point⁻¹.val.val * vecToMatrix x) i j) := by
    change (Ô E).subtype.toAddMonoidHom _ = _
    rw [map_sum, Matrix.mul_apply, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    change (O.genIdele.val * L.point⁻¹.val.val i k) * (idem (O.levelModulus 2).places * x (k, j)) =
      O.genIdele.val * (idem (O.levelModulus 2).places * (L.point⁻¹.val.val i k * x (k, j)))
    rw [mul_mul_mul_comm, mul_assoc]
  split
  next h_inv_mul =>
    have hx : ∀ (i : n) (j : r), idem (O.levelModulus 2).places * x (i, j) ∈ Ô E :=
      idem_mul_mem_of_inv_mul_mem (vecToMatrix x) h_inv_mul
    rw [dite_eq_left hx]
    refine ite_congr (propext ?_) (fun _ ↦ prod_congr rfl fun l _ ↦ ?_) fun _ ↦ rfl
    · -- The two conditions agree, as `genIdele γ⁻¹ x = (genIdele γ⁻¹) x` entrywise.
      rw [← ext_iff, ← ext_iff]
      refine forall₂_congr fun i j ↦ ?_
      rw [Matrix.smul_apply, Matrix.map_apply, vecToMatrix, of_apply, factor_reduction,
        smul_eq_mul, ← RingHom.map_mul, h_entry hx i j]
      have h_eq : (O.genIntAdele * ⟨idem (O.levelModulus 2).places *
          matrixToVec (L.point⁻¹.val.val * vecToMatrix x) (i, j), h_inv_mul i j⟩ : Ô E) =
          ∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
            ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩ :=
        Subtype.ext (h_sum_val hx i j).symm
      rw [h_eq]
    · -- At a place of `Q` the matrix `γ⁻¹` is `1`, so `γ⁻¹ x` and `x` have the same component.
      congr 3 with i j
      simp only [Matrix.map_apply, vecToMatrix, of_apply, modulusResidue_reduction, matrixToVec]
      congrm ⟦⟨_ * ?_, _⟩⟧
      have h_one : L.point⁻¹.val.val.map (evalAt (O.twistPlace l)) = 1 :=
        congrArg Units.val (atPlace_twistPlace_eq_one (inv_mem L.mem_supportedOn) l)
      have h_comp : (L.point⁻¹.val.val * vecToMatrix x).map (evalAt (O.twistPlace l)) =
          (vecToMatrix x).map (evalAt (O.twistPlace l)) := by
        rw [Matrix.map_mul, h_one, Matrix.one_mul]
      exact congrFun₂ h_comp i j
  next h_inv_mul =>
    split_ifs with hx h_cond
    · -- If `x` is integral and satisfies the condition, multiply the condition by `genResidue`:
      -- as `genResidue ^ 2 = 0`, the entries of `genIdele ^ 2 γ⁻¹ x` vanish modulo `ϖ²`, so
      -- `γ⁻¹ x` is integral (`reduction_levelModulus_eq_zero_iff`), against `h_inv_mul`.
      have h_gen_sq : V.genResidue * V.genResidue = 0 := by
        rw [← RingHom.map_mul, reduction_levelModulus_eq_zero_iff]
        change O.genIdele⁻¹.val ^ 2 * (O.genIdele.val * O.genIdele.val) ∈ Ô E
        rw [sq, mul_mul_mul_comm, Units.inv_mul, mul_one]
        exact one_mem _
      refine (h_inv_mul fun i j ↦ ?_).elim
      have h_mul : O.chosenModulusSq.reduction (O.genIntAdele *
          ∑ k : n, ⟨O.genIdele * L.point⁻¹.val.val i k, L.mul_inv_mem i k⟩ *
            ⟨idem (O.levelModulus 2).places * x (k, j), hx k j⟩) = 0 := by
        rw [RingHom.map_mul, ← h_entry hx i j, congrFun₂ h_cond i j, Matrix.smul_apply, smul_eq_mul,
          ← mul_assoc, h_gen_sq, zero_mul]
      have h_mem := reduction_levelModulus_eq_zero_iff.1 h_mul
      change O.genIdele⁻¹.val ^ 2 * (O.genIdele.val * _) ∈ Ô E at h_mem
      rw [h_sum_val hx i j, sq, mul_assoc O.genIdele⁻¹.val,
        ← mul_assoc O.genIdele⁻¹.val O.genIdele.val, Units.inv_mul, one_mul,
        ← mul_assoc, Units.inv_mul, one_mul] at h_mem
      exact h_mem
    all_goals rfl

omit [DecidableEq N] in
/-- Let `v` be a vector of the weight whose columns are counted by `O.columnCount`, and let
`γ = L.point`, so that `L.reducedInverse` is `ϖ γ⁻¹` modulo `ϖ²`, with `ϖ` generating the product of
the chosen places. The form `classForm O (h γ) v` on the standard definite space of rank `n` is
supported on the class of `h γ`. Its descent `O.normalizedDescent` to the space `O.W` is, at `g`,
the complex conjugate of a product of two factors. One is `L.weilScalar = χ(δ) / √|δ| ^ #r`, with
`δ` the determinant of `γ` at the chosen places and `χ` the character attached to `O.charW`. The
other is the theta kernel `modKernelStdSpace` of `O.W` and the standard space at `(g, h)`, for the
characters `O.charW`, `O.charV` of the two spaces, the Fock polynomial `O.fockPoly (star v)` of the
conjugate vector, and the following function of `S` modulo `ϖ² Q`. It is `0` unless
`(ϖ γ⁻¹) S ≡ ϖ • inclMatrix _ O.incl` modulo `ϖ²`, and it is then the product over the twist places,
those of `Q`, of the residue characters `O.tamePart` at the determinant of the rows `O.incl` of
`S`. -/
lemma normalizedDescent_classForm_mul [WeilData E]
    (v : WeylIndex n O.columnCount → ℂ) (g : G E O.signs) (h : Gf E n) :
    O.normalizedDescent (classForm O (h * L.point) v) g =
      conj (L.weilScalar * modKernelStdSpace O.W O.charW O.charV (O.levelModulus 2)
        (fun S : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if L.reducedInverse * S.map reduceToChosenModulusSq =
            V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
          ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
            ((S.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0)
        (O.fockPoly (star v)) g h) := by
  -- Split off `L.point` from the point `(g, h γ)`. By `pairWeil_schrodingerOp_of_mem_supportedOn`
  -- it acts on the finite datum by the scalar `L.weilScalar` and the substitution `y ↦ γ⁻¹ y`, and
  -- `liftFn_datum_point_inv_mul` compares the data.
  have h_supp_level : L.point ∈ Gf.supportedOn n (O.levelModulus 2).places :=
    Gf.supportedOn_mono (places_levelModulus.ge.trans' (by
      rintro _ ⟨i, rfl⟩; exact ⟨inl i, rfl⟩)) L.mem_supportedOn
  -- `γ` lies at the places of the level and is `1` at those of `Q`, which do not change `det γ`.
  have h_det : detOn (O.levelModulus 2).places L.point.val =
      detOn (Set.range O.chosenPlace) L.point.val := by
    ext w
    · simp
    · simp only [detOn_apply, places_levelModulus, Set.Sum.elim_range]
      by_cases hw : w ∈ Set.range O.chosenPlace
      · simp [hw]
      · by_cases htw : w ∈ Set.range O.twistPlace
        · rcases htw with ⟨i, rfl⟩
          simp [hw, atPlace_twistPlace_eq_one L.mem_supportedOn i]
        · simp [hw, htw]
  rw [normalizedDescent_classForm]
  refine congrArg conj ?_
  -- Write the point as `(g, h) * (1, γ)`, so that `γ` acts on the datum.
  have h_pt : (g, ((1 : GInf E (fun _ : n ↦ 1)), h * L.point)) =
      (g, (1, h)) * (((1 : GInf E O.signs), (1 : Gf E r)), (1, L.point)) := by
    simp only [Prod.mk_mul_mk, mul_one, Prod.mk_one_one]
  have h_scalar :
      ((O.charW.spaceChar (Fintype.card r)).val (detOn (O.levelModulus 2).places L.point.val) /
          (O.charV.spaceChar (Fintype.card n)).val
            (detOn (O.levelModulus 2).places (1 : Gf E r).val) *
          √(ideleAbs (detOn (O.levelModulus 2).places (1 : Gf E r).val)) ^ Fintype.card n /
          √(ideleAbs (detOn (O.levelModulus 2).places L.point.val)) ^ Fintype.card r : ℂ) =
        L.weilScalar := by
    simp [h_det, DividedLattice.weilScalar]
  have h_fn :
      (fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
        O.residueBlockDatum fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ T.map (levelResidueAt i)) =
      (fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
        if V.genResidue • T.map reduceToChosenModulusSq =
            V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
          ∏ i : O.TwistIndex, O.tamePart (O.placeAt (inr i))
            ((T.map (levelResidueAt (inr i))).submatrix O.incl id).det
        else 0) := by
    funext T
    simp only [DescentPair.residueBlockDatum, ← V.genResidue_smul_eq_inclMatrix_iff]
  have h_lift :
      (fun x : n × r → 𝔸f E ↦
        (O.levelModulus 2).liftFn
          ((fun T : Matrix n r (O.levelModulus 2).ResidueRing ↦
            O.residueBlockDatum fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ T.map (levelResidueAt i)) ∘
            vecToMatrix)
          (matrixToVec (L.point⁻¹.val.val * vecToMatrix x * (1 : Gf E r).val.val))) =
      (O.levelModulus 2).liftFn
        ((fun S : Matrix n r (O.levelModulus 2).ResidueRing ↦
          if L.reducedInverse * S.map reduceToChosenModulusSq =
              V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing O.incl then
            ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
              ((S.map (levelResidueAt (inr i))).submatrix O.incl id).det
          else 0) ∘ vecToMatrix) := by
    funext x
    rw [OneMemClass.coe_one, Units.val_one, Matrix.mul_one, h_fn]
    exact V.liftFn_datum_point_inv_mul x
  rw [modKernel, modDatum, h_pt, pairTheta_mul, pairWeil_integrated_fin,
    pairWeil_schrodingerOp_of_mem_supportedOn (isConjDisjoint_places _) (one_mem _) h_supp_level,
    h_scalar, h_lift, map_smul, pairTheta, map_smul, map_smul, smul_eq_mul]
  rfl

omit [DecidableEq n] in
/-- Let `Y` be invertible modulo `ϖ²` and `1` modulo `ϖ`, let `k = liftMod Y` be its chosen lift to
an integral unitary point, reduced at a place by `stdLevel.reduceAt`, and let `x` be a matrix modulo
`ϖ² Q`. Suppose that the rows `S` of `x Y` in `N` satisfy `w S = w ι` modulo `ϖ²`, where
`w = V.stackOverGenScalar s` is `s` stacked above `ϖ • 1` and `ι` is the inclusion matrix of
`V.fixedEmb`. Then the product over the twist places of the residue characters `O.tamePart` at the
determinant of the rows `O.incl` of `x` is `χ` of the determinant of the same rows of `x k`, divided
by the product of `O.tamePart (det k)` over the twist places. Here `χ = charOfTamePart` is the
product of the `O.tamePart` over all places dividing `ϖ² Q`. -/
lemma prod_twist_det_eq_inv_mul_charOfTamePart {s : Matrix a N O.chosenModulusSq.ResidueRing}
    (x : Matrix n r (O.levelModulus 2).ResidueRing) (Y : V.congruenceGroup)
    (h_stack_mul_eq : V.stackOverGenScalar s *
        (x.map reduceToChosenModulusSq * Y.val.val).submatrix (V.ε ∘ inl) id =
      V.stackOverGenScalar s * inclMatrix O.chosenModulusSq.ResidueRing V.fixedEmb) :
    ∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
        ((x.map (levelResidueAt (inr i))).submatrix O.incl id).det =
      (∏ i : O.TwistIndex, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i))
          (stdLevel.reduceAt ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i)) (liftMod Y.val)).val.det)⁻¹ *
        charOfTamePart (O.levelModulus 2) O.tamePart
          ((x * ((O.levelModulus 2).reductionGL (liftMod Y.val)).val).submatrix
            ((V.ε ∘ inl) ∘ V.fixedEmb) id).det := by
  -- The character modulo `ϖ² Q` is the product of the `O.tamePart` over the places of the level.
  have h_char (t : (O.levelModulus 2).ResidueRing) :
      charOfTamePart (O.levelModulus 2) O.tamePart t =
        ∏ᶠ j, O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) j) (levelResidueAt j t) :=
    (finprod_comp_equiv (.trans (.ofInjective _ O.apart.injective)
      (.subtypeEquivRight fun _ ↦ by rw [places_levelModulus]))).symm
  -- The rows `V.genResidue • 1` in `V.stackOverGenScalar s` give `S ≡ inclMatrix V.fixedEmb`
  -- modulo `ϖ` for the rows `S` of `x Y` in `N`.
  let S : Matrix N r (O.levelModulus 2).ResidueRing :=
    (x * ((O.levelModulus 2).reductionGL (liftMod Y.val)).val).submatrix (V.ε ∘ inl) id
  have hS : V.genResidue • S.map reduceToChosenModulusSq =
      V.genResidue • inclMatrix O.chosenModulusSq.ResidueRing V.fixedEmb := by
    have h_eq : S.map reduceToChosenModulusSq =
        (x.map reduceToChosenModulusSq * Y.val.val).submatrix (V.ε ∘ inl) id := by
      simp only [S, ← submatrix_map, Matrix.map_mul, factor_reductionGL, reductionGL_liftMod]
    rw [h_eq]
    simpa only [stackOverGenScalar, fromRows_mul, toRows₂_fromRows, Matrix.smul_mul, Matrix.one_mul]
      using congrArg toRows₂ h_stack_mul_eq
  -- So at the chosen places the rows `V.fixedEmb` of `S` have determinant `1`.
  have h_tame (i : O.ChosenIndex) :
      O.tamePart ((O.chosenPlace ⊕ᵥ O.twistPlace) (inl i))
        (levelResidueAt (inl i) (S.submatrix V.fixedEmb id).det) = 1 := by
    simp [RingHom.map_det, ← submatrix_map, (V.genResidue_smul_eq_inclMatrix_iff S V.fixedEmb).1 hS,
      inclMatrix, -elim_inl]
  -- At the places of `Q` the lift of `Y` reduces to `1`.
  have h_lift (i : O.TwistIndex) :
    stdLevel.reduceAt ((O.chosenPlace ⊕ᵥ O.twistPlace) (inr i)) (liftMod Y.val) = 1 :=
    stdLevel.reduceAt_eq_one_of_atPlace (atPlace_twistPlace_eq_one (liftMod_mem_supportedOn Y.val)
      i)
  change _ = _ * charOfTamePart (O.levelModulus 2) O.tamePart (S.submatrix V.fixedEmb id).det
  rw [h_char, finprod_eq_prod_of_fintype, Fintype.prod_sum_type, prod_eq_one fun i _ ↦ h_tame i]
  simp [S, RingHom.map_det, ← submatrix_map, h_lift, Function.comp_def, V.equiv_inl_fixedEmb,
    -elim_inr]

variable {s : Matrix a N O.chosenModulusSq.ResidueRing} {b b' : AutChar E}

open scoped Classical in
/-- Let `V.ε : N ⊕ m ≃ n` split the standard definite space on `n` as `V″ ⊕ V°`, with indices `N`
and `m`. Let `ϖ` generate the product of the chosen places, let the lattice `L` with point `γ` be
glued for `s` (`IsGlued`), and let the characters `b`, `b'` have product `O.charV`. The product form
is the form supported on the class of `diag(h, h') γ` built from the Cartan product of `y` and `η`.
Its descent to `O.W` is, at `g`, the complex conjugate of `L.weilScalar = χ(δ) / √|δ| ^ #r` (`δ` the
determinant of `γ` at the chosen places, `χ` attached to `O.charW`) times a sum over `Y` in
`V.congruenceGroup`, the invertible matrices modulo `ϖ²` that are `1` modulo `ϖ`. The term of `Y` is
a product of two theta kernels `modKernelStdSpace` of `O.W` with a standard space, at `g` times the
integral lift `liftMod Y`.
* On `V″`, at `h`: the finite datum `columnDatum` at `σ` is the character `charOfTamePart` of the
determinant of the rows `e = V.fixedEmb` of `σ` if `w σ ≡ w * inclMatrix _ e` modulo `ϖ²`, where
`w = V.stackOverGenScalar s` is `s` above `ϖ • 1`, and `0` otherwise. The polynomial is that of
`star y` in the basis vectors of `O.W` of sign `1`.
* On `V°`, at `h'`: the datum is the indicator of the inclusion matrix of `z : r ↪ m`, and the
polynomial is that of `star η` in the basis vectors of sign `-1`. -/
lemma normalizedDescent_productForm [DecidableEq m] [Fintype a] [WeilData E]
    (hL : V.IsGlued s L) (hb : b * b' = O.charV) (h : Gf E N)
    (h' : Gf E m) (y : WeylIndex N O.colsPlus → ℂ) (η : WeylIndex m O.colsMinus → ℂ)
    (g : G E O.signs) :
    O.normalizedDescent (V.productForm L (h, h') y η) g =
      conj (L.weilScalar * ∑ Y : V.congruenceGroup,
        modKernelStdSpace O.W O.charW b (O.levelModulus 2)
            (columnDatum (charOfTamePart (O.levelModulus 2) O.tamePart) reduceToChosenModulusSq
              (V.stackOverGenScalar s) V.fixedEmb)
            (letterPoly O.signs O.numbering 1 O.colsPlus (star y)) (g * (liftMod Y.val).val) h *
          modKernelStdSpace O.W O.charW b' O.chosenModulusSq
            (Pi.single (inclMatrix O.chosenModulusSq.ResidueRing z) 1)
            (letterPoly O.signs O.numbering (-1) O.colsMinus (star η))
            (g * (liftMod Y.val).val) h') := by
  -- Apply `normalizedDescent_classForm_mul` on the left. On the right, join the two kernels by the
  -- rule for sums `modKernelStdSpace_block` and move the lift of `Y` into the finite datum. Both
  -- sides are then values of the bilinear form `modKernelBilin`, and it remains to compare the
  -- finite data and the polynomials.
  change O.normalizedDescent (classForm O (U.block V.ε (h, h') * L.point) (cartanProduct V.ε 1 y η))
    g =
    _
  rw [V.normalizedDescent_classForm_mul]
  simp_rw [← modKernel_factor levelModulus_ideal_le, ← modKernelStdSpace_block V.ε, hb,
    modKernel_mul_stdLevel_left, ← modKernelBilin_apply, ← LinearMap.sum_apply, ← map_sum]
  refine congrArg conj (congrArg (L.weilScalar * ·)
    (congrArg₂ (fun Ψ P ↦ modKernelBilin _ _ _ _ _ _ _ Ψ P) ?_ ?_))
  · -- The finite data at a matrix `x`. By `hL.indicator_eq_sum` the left datum is a sum over `Y`
    -- with the same support conditions as on the right; compare the values on the support.
    ext x
    simp [← ite_and, ← submatrix_map, columnDatum, reduceAt_liftMod_congruenceGroup,
      hL.indicator_eq_sum, IsBlockNormalized,
      O.hasWeight.hasWeight_rankTwist.apply_det_eq_prod O.apart.injective O.tame_eq_one,
      Pi.single_apply, -elim_inl, -elim_inr]
    refine sum_congr rfl fun Y _ ↦ ite_congr rfl (fun h_supp ↦ ?_) fun _ ↦ rfl
    exact V.prod_twist_det_eq_inv_mul_charOfTamePart x Y h_supp.2
  · -- Conjugation commutes with the product `cartanProduct`, and the polynomial of a product is the
    -- product of the polynomials.
    have h_star : star (cartanProduct V.ε 1 y η) = cartanProduct V.ε 1 (star y) (star η) :=
      map_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2 _ _ _ conj
    rw [h_star, fockPoly_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2]

open scoped Classical in
/-- Let the lattice `L` with point `γ` be glued for `s`, and let `b * b' = O.charV`. Fix a point
`h'` of `Gf E m` on `V°`. Sum (`stdClassSum`) the forms supported on the class of `diag(h, h') γ`
and built from `φ h` and `η` (`productForm`) over the classes `h` of level `rowFixingLevel`. The
descent `O.normalizedDescent` of this sum to `O.W` is, at `g`, the complex conjugate of
`L.weilScalar` times a sum over the invertible matrices `Y` modulo `ϖ²` that are `1` modulo `ϖ`. The
term of `Y` is `kernelClassSum`, the theta kernel of `O.W` and `V″` summed over those classes, times
the theta kernel `modKernelStdSpace` of `O.W` and `V°` at `h'`. Both are taken at `g` times
`liftMod Y`, an integral lift of `Y`. -/
lemma normalizedDescent_stdClassSum_productForm [DecidableEq m] [Fintype a] [WeilData E]
    (hL : V.IsGlued s L) (hb : b * b' = O.charV)
    (h' : Gf E m) (φ : Gf E N → WeylIndex N O.colsPlus → ℂ) (η : WeylIndex m O.colsMinus → ℂ)
    (g : G E O.signs) :
    O.normalizedDescent
        (stdClassSum (rowFixingLevel O.toLevelPlaces (V.stackOverGenScalar s) V.fixedEmb)
          fun h : Gf E N ↦ V.productForm L (h, h') (φ h) η) g =
      conj (L.weilScalar * ∑ Y : V.congruenceGroup,
        kernelClassSum O b (V.stackOverGenScalar s) V.fixedEmb (fun h : Gf E N ↦ star (φ h))
            (g * (liftMod Y.val).val) *
          modKernelStdSpace O.W O.charW b' O.chosenModulusSq
            (Pi.single (inclMatrix O.chosenModulusSq.ResidueRing z) 1)
            (letterPoly O.signs O.numbering (-1) O.colsMinus (star η))
            (g * (liftMod Y.val).val) h') := by
  -- Apply `normalizedDescent_productForm` to each class; `O.normalizedDescent` and evaluation at
  -- `g` are linear.
  change (.proj g ∘ₗ O.normalizedDescent) _ = _
  simp [kernelClassSum, map_classSum, ← classSum_sum, mul_classSum,
    ↓V.normalizedDescent_productForm hL hb,
    mul_sum]

end DividedSplitting

end GluedFormTheta

end New.Rows

/-!
## A p-adic gauge bound for the Cartan product

In this section `V` is a divided splitting of the descent pair `O` along `z`, `p` is a prime, `ι` is
a p-adic place (an embedding of ℂ in ℂ_p) and `M` is a nonzero natural number. The bounds assume
that `M` is divisible by `ϖ`.

* `New.Rows.DividedSplitting.denominatorExponent`: the exponent of `M` that the change of lattice
  costs. On `V″`, where the columns of the diagram are long, it costs `card a` for each column,
  whatever the height.

The gauge `New.weylGauge κ e g ξ` is the largest `p`-adic absolute value of a coordinate of `g⁻¹`
applied to `ι ∘ ξ` in the weight `(κ, e)`. The place `ι` is not a positional argument. It comes from
the `PadicPlace p` instance, or it is given by name as `(ι := …)`.
-/

namespace New.Rows.DividedSplitting

open Matrix ComplexConjugate Finset Fintype IsUltrametricDist Ideal Modulus

variable {E r n N m a : Type} {l : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r]
  [Fintype n] [DecidableEq n] [Fintype N] [Fintype m] [Fintype a] [Fintype l]
  {O : DescentPair E r n} {z : r ↪ m} (V : DividedSplitting N m a O z)
  {p : ℕ} [Fact p.Prime] [ι : PadicPlace p] {M : ℕ} [NeZero M]

/-- The exponent of `M` in the denominator: at each infinite place `τ`, `card a` times the number of
columns of `O.colsPlus` of height below `card N` (a column has distinct entries, so at most `card a`
of them lie in the range of `V.dividedEmb`, the copy of `a` in `N`), plus `card m` times the number
of columns of `O.colsMinus` of height below `card m`, a bound for the number of their boxes. In both
diagrams the entry at `τ h` counts the columns of height `h`. -/
noncomputable def denominatorExponent : ℕ :=
  ∑ τ : NumberField.InfinitePlace E,
    (#(univ.map V.dividedEmb) * ∑ h ∈ range (Fintype.card N), O.colsPlus τ h +
      Fintype.card m * ∑ h ∈ range (Fintype.card m), O.colsMinus τ h)

omit [PadicPlace p] in
/-- For a prime `p`, a natural number `M ≠ 0` and a set `S` of indices, the Schur matrix of weight
`κ` over `ℂ_[p]` of the diagonal matrix that is `M⁻¹` on `S` and `1` elsewhere has entries of p-adic
norm at most `‖M‖⁻¹ ^ (Σ_τ #S · c_τ)`, with c_τ the number of columns of `κ τ` of height below
`card l` (`κ τ h` counts those of height `h`). -/
lemma norm_schur_diagonal_piecewise_inv_le [DecidableEq l] (S : Finset l)
    (κ : NumberField.InfinitePlace E → ℕ → ℕ) (i j : WeylIndex l κ) :
    ‖schur κ (fun _ : NumberField.InfinitePlace E ↦
        diagonal (S.piecewise (M : l → ℂ_[p])⁻¹ 1)) i j‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^
        (∑ τ : NumberField.InfinitePlace E, #S * (range (card l)).sum (κ τ)) := by
  -- The diagonal entry at a filling `i` is `M⁻¹` to the number of entries of `i` in `S`. These
  -- number at most the boxes in the first `#S` rows, and a row has one box at most in each column.
  simp only [schur_diagonal, diagonal_apply]
  split_ifs with hij
  swap
  · simp
  have h_entry : ∏ τ : NumberField.InfinitePlace E, ∏ b : l,
      S.piecewise (M : l → ℂ_[p])⁻¹ 1 b ^ tableauWeight i τ b =
        (M : ℂ_[p])⁻¹ ^ ∑ τ : NumberField.InfinitePlace E, ∑ b ∈ S, tableauWeight i τ b := by
    simp [piecewise, prod_pow_eq_pow_sum, Finset.univ_inter]
  rw [h_entry, norm_pow, norm_inv] -- the exponent is the number of entries in `S`
  gcongr with τ
  · simp [one_le_inv₀, NeZero.ne, norm_natCast_le_one]
  · calc
      _ ≤ ∑ k ∈ range #S, diagramWeight _ κ (τ, k) := (sum_tableauWeight_le i τ S).1
      _ ≤ ∑ _k ∈ range #S, (range (Fintype.card l)).sum (κ τ) := sum_le_sum fun k _ ↦ by
        simpa only [diagramWeight_apply] using sum_le_sum_of_subset fun h hh ↦ by simp_all
      _ = _ := by simp

omit [Fintype a] in
/-- The bound for one block of columns `f : l → n`. Let `ι` be a p-adic place, with map
`ιₚ : ℂ → ℂ_[p]`, and let `M ≠ 0` lie in the ideal `(ϖ) = O.levelModulus 1 false`, the product of
the chosen places of `O`. Let `κ` have no column of height in `[card l, card n)`. Let `γ = L.point`
be a point of the finite adelic unitary group `Gf E n` at the chosen places with `ϖ γ⁻¹` integral,
and `L.reducedInverse` the matrix `ϖ γ⁻¹` modulo `ϖ²`. After an invertible change of its
`f`-columns, let those with index `j ∉ S` be killed by `V.genResidue`, the class of `ϖ`. Let the
`f`-columns of `g⁻¹` be those of `h⁻¹` placed along `f`. Read the `f`-columns of `(g γ)⁻¹` in
`ℂ_[p]` at each `τ` by the extension (`adeleExtension`) of the embedding `weightEmbedding ιₚ τ` of
`E` to the finite adeles. Then their Schur matrix sends `ιₚ ∘ v` to a vector of norm at most
`‖M‖⁻¹ ^ (Σ_τ #S · c_τ)` times `weylGauge κ 0 h v`, the sup norm of `h⁻¹` applied to `ιₚ ∘ v` in
weight `κ` twisted by the power `0` of the determinant. Here c_τ is the number of columns of `κ τ`
of height below `card l`. -/
lemma norm_schur_inv_cols_le_weylGauge [DecidableEq l]
    (hM : (M : NumberField.RingOfIntegers E) ∈ (O.levelModulus 1 false).ideal)
    (L : DividedLattice O) {κ : NumberField.InfinitePlace E → ℕ → ℕ} {h : Gf E l}
    {v : WeylIndex l κ → ℂ} {g : Gf E n} {S : Finset l} {f : l → n}
    (hκ_cols : HasColumnsBelow n l κ)
    (hS : ∃ K : GL l O.chosenModulusSq.ResidueRing, ∀ i : n, ∀ j : l, j ∉ S →
      V.genResidue * (L.reducedInverse.submatrix id f * K.val) i j = 0)
    (h_cols : g⁻¹.val.val.submatrix id f = inclMatrix (𝔸f E) f * h⁻¹.val.val) :
    ‖schur κ (fun τ : NumberField.InfinitePlace E ↦
        ((g * L.point)⁻¹.val.val.submatrix id f).map
          (adeleExtension (weightEmbedding ιₚ τ))) *ᵥ ιₚ ∘ v‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^
          (∑ τ : NumberField.InfinitePlace E, #S * (range (Fintype.card l)).sum (κ τ)) *
        weylGauge κ 0 h v := by
  -- Lift `K` to an integral `k` and write `h = h' k⁻¹`; the gauges at `h` and `h'` agree. With
  -- `h'` again called `h`, the `f`-columns of `(g γ)⁻¹` factor as `A * Δ * h⁻¹`, with `A` integral
  -- at all places and `Δ` diagonal (`M⁻¹` on `S`, `1` elsewhere). The Schur matrix of `A` does not
  -- increase norms; that of `Δ` is diagonal.
  obtain ⟨k, hk⟩ : ∃ k : stdLevel E l, ∀ i : n, ∀ j : l, j ∉ S →
      V.genResidue *
        (L.reducedInverse.submatrix id f * (O.chosenModulusSq.reductionGL k).val) i j = 0 :=
    reductionGL_surjective.exists.1 hS
  obtain ⟨h, rfl⟩ := mul_right_surjective k⁻¹.val h
  rw [weylGauge_mul_of_mem_integralAbove h (stdLevel_le_localLevel k⁻¹.property)]
  let A : Matrix n l (𝔸f E) := of fun (i : n) (j : l) ↦
    (L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j * if j ∈ S then (M : 𝔸f E) else 1
  let Δ : Matrix l l ℂ_[p] := diagonal (S.piecewise (M : l → ℂ_[p])⁻¹ 1)
  have hM_red : (O.levelModulus 1 false).reduction (M : Ô E) = 0 := by
    rw [← map_natCast (algebraMap (NumberField.RingOfIntegers E) (Ô E)), reduction_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hM
  -- `A` is integral because `ϖ A` vanishes modulo `ϖ` (on `S`, via `M`) and `ϖ² A` vanishes
  -- modulo `ϖ²` (off `S`, via `hk`).
  have hA (i : n) (j : l) : A i j ∈ Ô E := by
    let X : Ô E := ∑ c : l, ⟨O.genIdele * L.point⁻¹.val.val i (f c), L.mul_inv_mem i (f c)⟩ *
      ⟨k.val.val.val c j, k.property.isIntMatrix c j⟩
    have hX_val : (X : 𝔸f E) =
        O.genIdele.val * (L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j := by
      change (Ô E).subtype.toAddMonoidHom _ = _
      rw [map_sum, Matrix.mul_apply, mul_sum]
      refine sum_congr rfl fun c _ ↦ ?_
      change (O.genIdele.val * L.point⁻¹.val.val i (f c)) * k.val.val.val c j =
        O.genIdele.val * (L.point⁻¹.val.val i (f c) * k.val.val.val c j)
      rw [mul_assoc]
    by_cases hj : j ∈ S
    · have h_red : (O.levelModulus 1 false).reduction (X * (M : Ô E)) = 0 := by
        rw [RingHom.map_mul, hM_red, mul_zero]
      have h_mem := reduction_levelModulus_eq_zero_iff.1 h_red
      rw [pow_one, Subring.coe_mul, Subring.coe_natCast, hX_val, ← mul_assoc, ← mul_assoc,
        Units.inv_mul, one_mul] at h_mem
      simpa only [A, of_apply, hj, ↓reduceIte] using h_mem
    · have hX_red : O.chosenModulusSq.reduction X =
          (L.reducedInverse.submatrix id f * (O.chosenModulusSq.reductionGL k).val) i j := by
        rw [Matrix.mul_apply]
        change O.chosenModulusSq.reduction.toAddMonoidHom _ = _
        rw [map_sum]
        refine sum_congr rfl fun c _ ↦ ?_
        exact RingHom.map_mul ..
      have h_red : O.chosenModulusSq.reduction (O.genIntAdele * X) = 0 := by
        rw [RingHom.map_mul, hX_red]
        exact hk i j hj
      have h_mem := reduction_levelModulus_eq_zero_iff.1 h_red
      change O.genIdele⁻¹.val ^ 2 * (O.genIdele.val * (X : 𝔸f E)) ∈ Ô E at h_mem
      rw [hX_val, sq, mul_assoc O.genIdele⁻¹.val, ← mul_assoc O.genIdele⁻¹.val O.genIdele.val,
        Units.inv_mul, one_mul, ← mul_assoc, Units.inv_mul, one_mul] at h_mem
      simpa only [A, of_apply, hj, ↓reduceIte, mul_one] using h_mem
  let φ (τ : NumberField.InfinitePlace E) := adeleExtension (E := E) (weightEmbedding ιₚ τ)
  have h_inv : (g * L.point)⁻¹.val.val.submatrix id f =
      L.point⁻¹.val.val.submatrix id f * k.val.val.val * h⁻¹.val.val := by
    rw [_root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul,
      submatrix_mul _ _ id id f Function.bijective_id, submatrix_id_id, h_cols,
      ← Matrix.mul_assoc, mul_inclMatrix, _root_.mul_inv_rev, Subgroup.coe_inv _ k, inv_inv,
      Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  have h_factor (τ : NumberField.InfinitePlace E) :
      ((g * L.point)⁻¹.val.val.submatrix id f).map (φ τ) =
        A.map (φ τ) * Δ * h⁻¹.val.val.map (φ τ) := by
    rw [h_inv, Matrix.map_mul]
    congr 1 with i j
    rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.map_apply]
    change φ τ ((L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j) =
      φ τ ((L.point⁻¹.val.val.submatrix id f * k.val.val.val) i j *
        if j ∈ S then (M : 𝔸f E) else 1) * S.piecewise (M : l → ℂ_[p])⁻¹ 1 j
    rw [RingHom.map_mul, mul_assoc]
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceIte, Finset.piecewise, Pi.inv_apply, Pi.natCast_apply, map_natCast,
        mul_inv_cancel₀ (Nat.cast_ne_zero (R := ℂ_[p]).2 (NeZero.ne M)), mul_one]
    · simp only [hj, ↓reduceIte, Finset.piecewise, Pi.one_apply, map_one, mul_one]
  -- the vector whose norm is the gauge of `v` at `h`
  let w : WeylIndex l κ → ℂ_[p] :=
    schur κ (fun τ : NumberField.InfinitePlace E ↦ h⁻¹.val.val.map (φ τ)) *ᵥ ιₚ ∘ v
  calc
    _ = ‖schur κ (fun τ ↦ A.map (φ τ)) *ᵥ schur κ (fun _ ↦ Δ) *ᵥ w‖ := by
      simp only [w, mulVec_mulVec, ← Matrix.mul_assoc, hκ_cols.schur_mul_schur, ← h_factor, φ]
    _ ≤ ‖schur κ (fun _ ↦ Δ) *ᵥ w‖ :=
      norm_schur_mulVec_le hκ_cols.1 (fun τ i j ↦ norm_adeleExtension_le_one _ (hA i j)) _
    _ ≤ _ * ‖w‖ := norm_mulVec_le (norm_schur_diagonal_piecewise_inv_le (M := M) S κ) w
    _ = _ := by simp [weylGauge, weylRep, w, φ, -map_inv]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `V.ε : N ⊕ m ≃ n` split the indices, let `ι` be a p-adic place, and let `M ≠ 0` lie in the
ideal of `O.levelModulus 1 false`, the product of the chosen places of `O`. Let the lattice `L` with
point `γ = L.point` be glued for `s`. The diagrams `O.colsPlus` and `O.colsMinus` count the columns
of each height at each infinite place. The vector `y` has the first weight in the letters `N` and
`η` has the second in the letters `m`. Their product `cartanProduct V.ε 1 y η` includes both in the
letters `n` (it is moved by `1`) and projects their tensor product to the weight with column numbers
`O.columnCount` and determinant exponents `O.detExp`. Then the gauge of the product at
`U.block V.ε (h, h') * γ`, with `U.block` the block diagonal matrix, is at most
`‖M‖⁻¹ ^ V.denominatorExponent` times the gauge of `y` at `h` and the gauge of `star η` at `h'`, the
latter through the conjugate embedding. -/
lemma weylGauge_cartanProduct_le [DecidableEq m] [DecidableEq N]
    (hM : (M : NumberField.RingOfIntegers E) ∈ (O.levelModulus 1 false).ideal)
    {s : Matrix a N O.chosenModulusSq.ResidueRing} {L : DividedLattice O} (hL : V.IsGlued s L)
    (h : Gf E N) (h' : Gf E m) (y : WeylIndex N O.colsPlus → ℂ)
    (η : WeylIndex m O.colsMinus → ℂ) :
    weylGauge (ι := ι) O.columnCount O.detExp (U.block V.ε (h, h') * L.point)
        (cartanProduct V.ε 1 y η) ≤
      ‖(M : ℂ_[p])‖⁻¹ ^ V.denominatorExponent *
        (weylGauge (ι := ι) O.colsPlus 0 h y *
          weylGauge (ι := ⟨ιₚ.comp conj⟩) O.colsMinus 0 h' (star η)) := by
  -- `cartanProduct` is an integral matrix applied to the tensor product of two Schur images, one
  -- for each block of `V.ε`; so its norm is at most the product of their norms.
  -- `norm_schur_inv_cols_le_weylGauge` bounds each.
  set g : Gf E n := U.block V.ε (h, h') * L.point
  -- The block `N`: only the columns in the image of `V.dividedEmb` cost a power of `M`.
  have h_big : ‖schur O.colsPlus (fun τ : NumberField.InfinitePlace E ↦
        (g⁻¹.val.val.submatrix id (V.ε ∘ .inl)).map
          (adeleExtension (weightEmbedding ιₚ τ))) *ᵥ ιₚ ∘ y‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^ (∑ τ : NumberField.InfinitePlace E,
          #(univ.map V.dividedEmb) * (range (card N)).sum (O.colsPlus τ)) *
        weylGauge (ι := ι) O.colsPlus 0 h y :=
    V.norm_schur_inv_cols_le_weylGauge hM L V.hasColumnsBelow.1 hL.exists_cols_eq_zero <| by
      rw [← map_inv, Prod.inv_mk, U.block_val]
      refine Matrix.ext fun i j ↦ ?_
      obtain ⟨i' | i', rfl⟩ := V.ε.surjective i
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₁₁, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, ↓reduceIte, zero_mul, Finset.sum_const_zero]
  -- The block `m`, read through the conjugate embedding: every column may cost a power of `M`.
  have h_small : ‖schur O.colsMinus (fun τ : NumberField.InfinitePlace E ↦
        (g⁻¹.val.val.submatrix id (V.ε ∘ .inr)).map
          (adeleExtension (weightEmbedding (ιₚ.comp conj) τ))) *ᵥ ιₚ.comp conj ∘ star η‖ ≤
      ‖(M : ℂ_[p])‖⁻¹ ^ (∑ τ : NumberField.InfinitePlace E,
          card m * (range (card m)).sum (O.colsMinus τ)) *
        weylGauge (ι := ⟨ιₚ.comp conj⟩) O.colsMinus 0 h' (star η) :=
    V.norm_schur_inv_cols_le_weylGauge (ι := ⟨ιₚ.comp conj⟩) (S := univ) hM L V.hasColumnsBelow.2
      ⟨1, fun _ _ h ↦ (h (mem_univ _)).elim⟩ <| by
      rw [← map_inv, Prod.inv_mk, U.block_val]
      refine Matrix.ext fun i j ↦ ?_
      obtain ⟨i' | i', rfl⟩ := V.ε.surjective i
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, ↓reduceIte, zero_mul, Finset.sum_const_zero]
      · simp only [submatrix_apply, id_eq, Function.comp_apply, Equiv.symm_apply_apply,
          fromBlocks_apply₂₂, Matrix.mul_apply, inclMatrix, Matrix.one_apply,
          EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  -- Move the action of `g⁻¹` into `cartanProduct` (`weylRep_mulVec_cartanProduct`) and split the
  -- power of `M` by blocks.
  have hη : ιₚ ∘ η = ιₚ.comp conj ∘ star η :=
    funext fun x ↦ congrArg ιₚ (star_star (η x)).symm
  rw [weylGauge, map_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2 (f := ιₚ), hη]
  change ‖weylRep (mixedWeight n O.colsPlus O.colsMinus)
      (fun τ : NumberField.InfinitePlace E ↦ -∑ i ∈ Finset.Ico 1 (card n), O.colsMinus τ i) _ *ᵥ
    _‖ ≤ _
  rw [weylRep_mulVec_cartanProduct V.hasColumnsBelow.1 V.hasColumnsBelow.2]
  rw [denominatorExponent, sum_add_distrib, pow_add, mul_mul_mul_comm]
  refine (norm_mulVec_le (c := 1) (by simp [norm_intCast_le_one]) _).trans
    ((one_mul _).trans_le ?_)
  -- `g` is unitary, so the transpose of `g` is the conjugate of `g⁻¹`, and conjugation on `E`
  -- turns the conjugate embedding back into the given one.
  have h_conj (τ : NumberField.InfinitePlace E) :
      (weightEmbedding (E := E) (ιₚ.comp conj) τ).comp conj = weightEmbedding ιₚ τ :=
    RingHom.ext (by simp [starRingEnd_apply (R := E)])
  have h_transpose (τ : NumberField.InfinitePlace E) :
      ((GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ))
          g⁻¹.val)⁻¹).valᵀ.submatrix id (V.ε ∘ .inr) =
        (g⁻¹.val.val.submatrix id (V.ε ∘ .inr)).map
          (adeleExtension (weightEmbedding (ιₚ.comp conj) τ)) := by
    rw [U.inv_val_eq_conjTranspose]
    ext i j
    exact ((adeleExtension_star ..).trans (by rw [h_conj]; rfl)).symm
  exact norm_mul_le_of_le ((pi_norm_comp_le (_ *ᵥ _) _).trans h_big)
    ((pi_norm_comp_le (_ *ᵥ _) _).trans (by simpa only [h_transpose] using h_small))

end New.Rows.DividedSplitting

end
