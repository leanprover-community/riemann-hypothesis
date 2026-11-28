module

import Mathlib.RingTheory.PicardGroup
public import Lib.Weil.MixedModel.IsotropicSplitting
public import Lib.DiscreteSeries.FlenstedJensen.Defs
import Lib.Adelic.Landherr
import Lib.Adelic.Unitary.RationalPoints
import Lib.Adelic.Unitary.WeakApproximation
import Lib.Adelic.Witt.WittTheorem
import Lib.Cohomology.Etale.Basic
import Lib.General.LinearAlgebra.HermiteForm
import Lib.General.LinearAlgebra.PolarDecomposition

/-!
# Maximal compact subgroup, splittings of isotropic frames and the Iwasawa decomposition

The file concerns the adelic unitary group `New.G E s` of a CM field `E` and its maximal compact
subgroup `New.maxCompact E s`, and the stabiliser of the span of k for a splitting of a hermitian
space along dual isotropic frames k, l. After the first section `E` carries a CM type and, for the
most part, Weil data (`New.WeilData`: roots of unity of order 5040, a purely imaginary element `j`
and further choices).

## Main definitions and results

* `New.Space.exists_splitting`: every isotropic frame `k` of a hermitian space `V` is part of a
  splitting `V = range l ⊕ V₀ ⊕ range k` (`New.Space.Splitting`, a Witt decomposition). The proof
  compares `V` with the sum of a hyperbolic space and a standard space by Landherr's theorem
  (`New.Space.landherr`) and moves the frame by Witt's theorem (`New.Space.witt`).
* `New.Space.Splitting.radicalCenter`: the centre of the radical, parametrised additively by adelic
  matrices M through M − M*; it sends rational matrices to rational points.
* `New.Space.Splitting.centerCoeff`: the Fourier coefficients of a function along this centre.
* `New.Space.Splitting.iwasawa`: the Iwasawa decomposition for the maximal compact subgroup
  `New.maxCompact`, obtained at each infinite place and over the finite adeles from Witt's theorem
  (`New.Space.Splitting.iwasawa_of_witt`).
* `New.Space.Splitting.exists_eq_radicalElement_mul_levi_mul_isAdapted`: every element is a product
  of an element of the radical, a Levi element and an element adapted to the splitting.

Notions from other files:
* `New.G E s`: the adelic unitary group of the form ε (`New.stdForm`) that is diag(s) at the
  infinite places and the identity at the finite places; `g.adeleMatrix` is the adelic matrix of
  `g`.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with
  xᴴJx = ε; `W.Γ` is the group of rational points in `New.G E s`.
* `New.U A`: the unitary group of a matrix A.
* `New.parabolic`: the invertible matrices that are block upper triangular for a level function.

## Relation to the literature

Known results: Witt's extension theorem for hermitian forms and for unimodular hermitian lattices,
and the Iwasawa decomposition. Witt's theorem is imported: over fields with a nontrivial involution
for invertible hermitian forms (`New.witt`), and over the integral finite adeles only for primitive
frames of the identity form over a CM field containing the roots of unity of order 5040
(`New.witt_Ô`). Its form in the maximal compact subgroup at an infinite place is deduced here: an
isotropic subspace is the graph of an isometry between the coordinates of the two signs. Source: U.
A. First, Witt's extension theorem for quadratic spaces over semiperfect rings, J. Pure Appl.
Algebra 219 (2015), Cor. 4.9 (for fields, Dieudonné, La géométrie des groupes classiques, 1955; for
lattices, Jacobowitz, Amer. J. Math. 84 (1962)). For the Iwasawa decomposition at the finite places:
J. Tits, Reductive groups over local fields, Proc. Sympos. Pure Math. 33 (1979), part 1, 3.3.2 and
3.8.1.
-/

@[expose] public section

noncomputable section

/-!
## The maximal compact subgroup of the adelic unitary group

`New.G E s` is the adelic unitary group of the CM field `E`: one complex unitary group of the sign
matrix `New.signMatrix s` for each infinite place, times the unitary group of the identity matrix
over the finite adeles.
-/

section MaximalCompact

variable (E : Type*) {n : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n]
  [DecidableEq n] (s : n → ℤˣ)

/-- The subgroup K_∞K₀ of G: elements that are unitary matrices at each infinite place and lie
in GL_n(Ô) at the finite places. -/
noncomputable def New.maxCompact : Subgroup (G E s) :=
  Subgroup.prod (Subgroup.pi Set.univ fun _ : NumberField.InfinitePlace E ↦ maxCompactU s)
    (stdLevel E n)

variable {E s}

lemma New.isCompact_maxCompact : IsCompact (maxCompact E s : Set (G E s)) := by
  -- It is a product of copies of the compact group U(diag s) ∩ U(n) with the compact group
  -- `stdLevel`.
  have h_inf : IsCompact (maxCompactU s : Set (USign s)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (maxCompactU s)))
  exact (isCompact_univ_pi fun _ ↦ h_inf).prod isCompact_stdLevel

/-- An element of the adelic unitary group lies in the maximal compact subgroup exactly when its
matrix has orthonormal columns at every infinite place and integral finite entries
(`New.Exchange.IsOrthoIntegral`). -/
lemma New.mem_maxCompact_iff_isOrthoIntegral_adeleMatrix {g : G E s} :
    g ∈ maxCompact E s ↔ Exchange.IsOrthoIntegral g.adeleMatrix := by
  have h_inf (w : NumberField.InfinitePlace E) : g.fst w ∈ maxCompactU s ↔
      (g.adeleMatrix.map (evalInf w)).conjTranspose * g.adeleMatrix.map (evalInf w) = 1 := by
    rw [maxCompactU, Subgroup.mem_subgroupOf, Matrix.mem_unitaryGroupOf_iff, Matrix.mul_one]
    rfl
  rw [maxCompact, Subgroup.mem_prod, Subgroup.mem_pi, mem_stdLevel]
  simp only [Set.mem_univ, forall_const, h_inf, Exchange.IsOrthoIntegral, G.adeleMatrix_snd]

end MaximalCompact

/-! ## Existence of splittings of isotropic frames -/

section SplittingExists

open Matrix ComplexOrder New Exchange Fintype

open scoped Classical in
/-- If a complex matrix `X` is isotropic for the form diag(s), then its rank is at most the number
of coordinates `i` with `s i = ε`, for either sign `ε`. -/
lemma New.rank_le_card_preimage_of_isotropic {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p]
    {s : n → ℤˣ} {X : Matrix n p ℂ} (h_iso : Xᴴ * signMatrix s * X = 0) (ε : ℤˣ) :
    X.rank ≤ card (s ⁻¹' {ε}) := by
  -- XᴴX = ε Xᴴ (diag s + ε) X, and diag s + ε vanishes where s ≠ ε.
  let d : n → ℂ := fun i ↦ s i + ε
  have hd : diagonal d = signMatrix s + (ε : Matrix n n ℂ) := (diagonal_add _ _).symm
  have h_gram : Xᴴ * X = ε • Xᴴ * diagonal d * X := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;>
      simp [hd, Matrix.mul_add, Matrix.add_mul, h_iso]
  have h_supp (i : n) (hi : d i ≠ 0) : i ∈ s ⁻¹' {ε} := by
    contrapose hi
    simp [d, Int.units_ne_iff_eq_neg.1 hi]
  calc X.rank = (ε • Xᴴ * diagonal d * X).rank := by rw [← h_gram, rank_conjTranspose_mul_self]
    _ ≤ (diagonal d).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    _ = card {i : n // d i ≠ 0} := rank_diagonal d
    _ ≤ card (s ⁻¹' {ε}) := card_subtype_mono _ _ h_supp

open scoped Classical in
/-- If each sign occurs at least `card p` times in `s`, then the coordinates can be numbered by
`(p ⊕ p) ⊕ Fin m` so that the first copy of `p` has sign 1 and the second sign -1: the signs become
`hyperbolicSigns p` (1 on the first copy, -1 on the second) joined with some `s₀` on `Fin m`. -/
lemma New.exists_equiv_hyperbolicSigns {n p : Type*} [Fintype n] [Fintype p] {s : n → ℤˣ}
    (h_card : ∀ ε : ℤˣ, card p ≤ card (s ⁻¹' {ε})) :
    ∃ (m : ℕ) (s₀ : Fin m → ℤˣ) (e : (p ⊕ p) ⊕ Fin m ≃ n), s ∘ e = hyperbolicSigns p ⊕ᵥ s₀ := by
  obtain ⟨f⟩ : Nonempty (p ↪ s ⁻¹' {1}) := Function.Embedding.nonempty_of_card_le (h_card 1)
  obtain ⟨f'⟩ : Nonempty (p ↪ s ⁻¹' {-1}) := Function.Embedding.nonempty_of_card_le (h_card (-1))
  have hf (i : p) : s (f i) = 1 ∧ s (f' i) = -1 := ⟨(f i).prop, (f' i).prop⟩
  let φ : p ⊕ p → n := Sum.elim (fun i ↦ f i) (fun i ↦ f' i)
  have hφ : φ.Injective :=
    (Subtype.val_injective.comp f.injective).sumElim (Subtype.val_injective.comp f'.injective)
      fun i j h_eq ↦ by simpa [hf] using congrArg s h_eq
  let e : (p ⊕ p) ⊕ Fin (card {a : n // a ∉ Set.range φ}) ≃ n :=
    ((Equiv.ofInjective φ hφ).sumCongr (equivFin {a : n // a ∉ Set.range φ}).symm).trans
      (Equiv.sumCompl (· ∈ Set.range φ))
  refine ⟨_, fun i ↦ s (e (.inr i)), e, funext fun x ↦ ?_⟩
  rcases x with (i | i) | i <;> simp [e, φ, hf]

open scoped Classical in
/-- If the columns of a left invertible matrix `k` span an isotropic subspace of `V`, then each
sign occurs among the signs `s` of `V` at least as often as `k` has columns. -/
lemma New.Space.card_le_card_preimage_of_isotropic {E : Type*} [Field E] [CMType E] {n p : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] {s : n → ℤˣ} (V : Space E n s)
    {k : Matrix n p E} (hk : HasLeftInv k) (h_iso : kᴴ * V.J * k = 0) (ε : ℤˣ) :
    card p ≤ card (s ⁻¹' {ε}) := by
  -- At an infinite place `w`, `k` in standard coordinates gives a full-rank isotropic matrix `X`.
  let w : NumberField.InfinitePlace E := Classical.ofNonempty
  let X : Matrix n p ℂ := (V.x⁻¹.val * k.map toAdele).map (evalInf w)
  obtain ⟨l, hl⟩ := hk
  refine le_trans ?_ (rank_le_card_preimage_of_isotropic (X := X) ?_ ε)
  · simpa [X, ← Matrix.map_mul, Matrix.mul_assoc, hl] using
      Matrix.rank_mul_le_right ((l.map toAdele * V.x.val).map (evalInf w)) X
  · have h_sign : (stdForm E s).map (evalInf w) = signMatrix s := by simp [signMatrix, stdForm]
    simp only [X, ← h_sign, ← conjTranspose_map (evalInf w) fun _ ↦ rfl, ← Matrix.map_mul,
      V.gram_at_point_eq_map, h_iso, Matrix.map_zero, map_zero]

/-- Let `k` be a left invertible `n × p` matrix over `E` whose columns span an isotropic subspace of
`V`, that is, `kᴴ J k = 0` for the Gram matrix `J`. Then `k` is the frame `D.k` of a splitting `D`
of `V` (dual isotropic frames `D.k`, `D.l` and a copy of `V₀` orthogonal to both) over some space
`V₀` with coordinates indexed by `Fin m`. -/
lemma New.Space.exists_splitting {E : Type} [Field E] [CMType E] [WeilData E] {n : Type*}
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {p : Type} [Fintype p] [DecidableEq p]
    (V : Space E n s) {k : Matrix n p E} (hk : HasLeftInv k) (h_iso : kᴴ * V.J * k = 0) :
    ∃ (m : ℕ) (s₀ : Fin m → ℤˣ) (V₀ : Space E (Fin m) s₀) (D : V.Splitting V₀ p), D.k = k := by
  -- Each sign occurs at least `card p` times, so coordinates split into hyperbolic signs + `s₀`.
  obtain ⟨m, s₀, e, h_signs⟩ :=
    exists_equiv_hyperbolicSigns (V.card_le_card_preimage_of_isotropic hk h_iso)
  let V₀ := signedSpace E s₀
  have h_dim : card n = card (Fin m) + 2 * card p := by simp +arith [← card_congr e]
  -- Landherr gives an isometry from hyperbolic space plus `V₀` onto `V`, yielding a splitting `D`.
  obtain ⟨a, ha⟩ :=
    V.landherr ((hyperbolicSum p V₀).reindex e ((Equiv.comp_symm_eq e _ _).2 h_signs.symm))
  let D : V.Splitting V₀ p := splittingOfGram (a.val.submatrix id e)
    (Eq.trans (b := (a.valᴴ * V.J * a.val).submatrix e e)
      (Matrix.ext fun i j ↦ by simp [Matrix.mul_apply]) (by simp [ha])) h_dim
  -- Witt moves the isotropic frame `D.k` to `k`; apply the same isometry to all of `D`.
  obtain ⟨g, hg⟩ := V.witt ⟨D.lᴴ * V.J, D.gram_lk⟩ hk (D.gram_kk.trans h_iso.symm)
  let M := (D.l.fromCols D.k).fromCols D.i
  refine ⟨m, s₀, V₀, splittingOfGram (g.val.val * M)
    ((U.gram_invariant g M M).trans D.gram_eq_hyperbolicSum) h_dim, ?_⟩
  change (g.val.val * M).toCols₁.toCols₂ = k
  simpa [M, mul_fromCols] using hg

variable {E : Type*} [Field E] [CMType E] {n n₀ p : Type*} [Fintype n] [DecidableEq n]
  [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ}

end SplittingExists

/-!
## Adapted elements, the centre of the radical and the Iwasawa decomposition

H is a splitting of W over W₀ (`New.Space.Splitting`): dual isotropic frames k, l and a copy of W₀
orthogonal to both. In standard adelic coordinates k is `New.Space.Splitting.kAdelic`; the
stabiliser of its span has a unipotent radical with elements `New.Space.Splitting.radicalElement`
and a Levi subgroup parametrised by `New.Space.Splitting.levi`.
-/

namespace New.Space.Splitting

open Matrix WeilData ComplexOrder G

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n n₀ p : Type _} [Fintype n] [DecidableEq n] [Fintype n₀] [DecidableEq n₀] [Fintype p]
  [DecidableEq p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ} {W : Space E n s} {W₀ : Space E n₀ s₀}
  (H : W.Splitting W₀ p)

/-! ### Adapted elements -/

variable {H} in
omit [WeilData E] in
/-- An element adapted to the splitting `H` and the basis `γ` (its frame `H.frameAt h γ`, the matrix
h⁻¹ (l (γ⁻¹)ᴴ, k γ, ι) built from the frames `H.lAdelic`, `H.kAdelic` and the embedding `H.iAdelic`,
has orthonormal columns at the infinite places and is integral) stays adapted after right
multiplication by an element of the maximal compact subgroup. -/
lemma IsAdapted.mul_of_mem_maxCompact {h κ : G E s} {γ : GL p (𝔸 E)} (h_adapted : H.IsAdapted h γ)
    (hκ : κ ∈ maxCompact E s) : H.IsAdapted (h * κ) γ := by
  have h_frame : H.frameAt (h * κ) γ = κ⁻¹.adeleMatrix * H.frameAt h γ := by
    rw [frameAt, frameAt, _root_.mul_inv_rev, G.adeleMatrix_mul, Matrix.mul_assoc]
  rw [IsAdapted, h_frame]
  exact (mem_maxCompact_iff_isOrthoIntegral_adeleMatrix.1 (inv_mem hκ)).mul h_adapted

/-! ### The centre of the radical -/

/-- For an adelic p×p matrix M, the element 1 + k(M − M*)k*ε (k*ε is `H.lCoord`) of the centre of
the unipotent radical of the stabiliser of the span of the isotropic frame k. -/
def radicalCenter : AddChar (Matrix p p (𝔸 E)) (G E s) where
  toFun M := H.radicalElement 0 (-toAdele (j * 2 : E) • M)
  map_zero_eq_one' := ext_adeleMatrix (by simp [radicalElement])
  map_add_eq_mul' := by simp [radicalElement_mul]

@[simp]
lemma adeleMatrix_radicalCenter (M : Matrix p p (𝔸 E)) :
    (H.radicalCenter M).adeleMatrix = 1 + H.kAdelic * (M - Mᴴ) * H.lCoord := by
  -- The scalars cancel because `star j = -j`.
  simp [radicalCenter, radicalElement, smul_smul, ← map_mul, j_ne_zero, Matrix.mul_add,
    Matrix.add_mul, sub_eq_add_neg, add_comm]

/-- If `g` acts on the isotropic frame k of the splitting by the matrix `c`, that is `g k = k c`,
then conjugation by `g` carries the element 1 + k(M − Mᴴ)kᴴε of the centre of the radical to the
element given by `c * M * cᴴ`. -/
lemma mul_radicalCenter {g : G E s} {c : Matrix p p (𝔸 E)} (h : H.ActsOnFrame g c)
    (M : Matrix p p (𝔸 E)) :
    g * H.radicalCenter M = H.radicalCenter (c * M * cᴴ) * g := by
  -- As `g` preserves the form, `g k = k c` gives the adjoint relation `cᴴ lCoord g = lCoord`.
  have h_adj : cᴴ * (H.lCoord * g.adeleMatrix) = H.lCoord :=
    calc cᴴ * (H.lCoord * g.adeleMatrix)
        = (H.kAdelic * c)ᴴ * stdForm E s * g.adeleMatrix := by
          simp only [lCoord, conjTranspose_mul, Matrix.mul_assoc]
      _ = H.kAdelicᴴ * (g.adeleMatrixᴴ * stdForm E s * g.adeleMatrix) := by
          rw [← h, conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = H.lCoord := by rw [g.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix, lCoord]
  -- With `N = M - Mᴴ`, both sides have the matrix `g + k c N lCoord` (`adeleMatrix_radicalCenter`).
  apply G.ext_adeleMatrix
  simp [← g.adeleMatrix.mul_assoc, h, h_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_add, Matrix.add_mul]

@[simp]
lemma radicalCenter_mem {M : Matrix p p (𝔸 E)} (hM : M ∈ ratMatrices E p p) :
    H.radicalCenter M ∈ W.Γ := by
  obtain ⟨a, rfl⟩ := hM
  change H.radicalElement 0 (-toAdele (j * 2 : E) • a.map toAdele) ∈ W.Γ
  simpa only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero] using
    H.radicalElement_mem_Gamma 0 ⟨-(j * 2 : E) • a, Matrix.ext fun i k ↦ by simp⟩

@[fun_prop]
lemma continuous_radicalCenter : Continuous H.radicalCenter := by
  change Continuous fun M : Matrix p p (𝔸 E) ↦ H.radicalElement 0 (-toAdele (j * 2 : E) • M)
  fun_prop

/-- The Fourier coefficient at T of a function D at g: the mean of ψ(tr TM)·D(z(M)g) over adelic
matrices M modulo rational ones, z = `New.Space.Splitting.radicalCenter`. -/
def centerCoeff (T : Matrix p p E) (D : G E s → ℂ) (g : G E s) : ℂ :=
  quotMean (ratMatrices E p p) fun M : Matrix p p (𝔸 E) ↦
    stdAddChar E (T.map toAdele * M).trace * D (H.radicalCenter M * g)

/-! ### The Iwasawa decomposition -/

omit [WeilData E] in
/-- The Iwasawa decomposition in one component `f : 𝔸 E →+* S` of the adeles, where `A` stands for
the form: `H.lCoord` maps to (k*)A for the image k of the isotropic frame `H.kAdelic` (hypothesis
`h_form`). Let `P` be a class of frames such that every left invertible frame is brought into `P`
by an invertible matrix that is block triangular for `wt`, and any two isotropic frames in `P`
differ by an element of `C`. Then for each isometry `u` of `A` there is `κ ∈ C` such that `u * κ`
acts on k by such a block triangular matrix. -/
lemma iwasawa_of_witt {wt : p → ℕ} {S : Type*} [CommRing S] [StarRing S] {A : Matrix n n S}
    {P : Matrix n p S → Prop} {C : Set (U A)} (f : 𝔸 E →+* S) (u : U A)
    (h_triangular : ∀ {X : Matrix n p S}, HasLeftInv X →
      ∃ b ∈ (parabolic wt : Subgroup (GL p S)), P (X * b.val))
    (h_witt : ∀ {X Y : Matrix n p S}, P X → P Y → Xᴴ * A * X = 0 → Yᴴ * A * Y = 0 →
      ∃ κ ∈ C, (κ : Matrix n n S) * X = Y)
    (h_form : H.lCoord.map f = (H.kAdelic.map f)ᴴ * A) :
    ∃ κ ∈ C, ∃ b ∈ (parabolic wt : Subgroup (GL p S)),
      ((u * κ : U A) : Matrix n n S) * H.kAdelic.map f = H.kAdelic.map f * b.val := by
  -- For g = 1 and g = u, bring the frame g⁻¹ k into the class `P` by a block triangular change of
  -- basis `b g`. Both new frames are isotropic, so some κ in `C` carries the first to the second.
  let k : Matrix n p S := H.kAdelic.map f
  have hk_iso : kᴴ * A * k = 0 := by simp [k, ← h_form, ← Matrix.map_mul]
  have h_inv (g : U A) : HasLeftInv (g⁻¹.val.val * k) :=
    ⟨H.kCoord.map f * g.val.val, by simp [k, ← Matrix.map_mul, Matrix.mul_assoc]⟩
  choose b hb h_class using fun g : U A ↦ h_triangular (h_inv g)
  have h_iso (g : U A) :
      (g⁻¹.val.val * k * (b g).val)ᴴ * A * (g⁻¹.val.val * k * (b g).val) = 0 := by
    rw [gram_mul, U.gram_invariant, hk_iso, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨κ, hκ, h_eq⟩ := h_witt (h_class 1) (h_class u) (h_iso 1) (h_iso u)
  have h_frames : κ.val.val * (k * (b 1).val) = u⁻¹.val.val * (k * (b u).val) := by
    simpa [Matrix.mul_assoc] using h_eq
  -- κ k b₁ = u⁻¹ k b_u gives u κ k = k b_u b₁⁻¹.
  refine ⟨κ, hκ, b u * (b 1)⁻¹, mul_mem (hb u) (inv_mem (hb 1)), ?_⟩
  calc (u * κ).val.val * k
      = u.val.val * (κ.val.val * (k * (b 1).val)) * (b 1)⁻¹.val := by simp [Matrix.mul_assoc]
    _ = k * (b u * (b 1)⁻¹).val := by simp [h_frames, Matrix.mul_assoc]

/-- Witt's theorem in K = U(diag s) ∩ U(n): two frames that are orthonormal and isotropic for
diag s differ by an element of K. -/
lemma exists_unitary_mul_eq_of_isotropic {s : n → ℤˣ} {A B : Matrix n p ℂ} (hA : Aᴴ * A = 1)
    (hB : Bᴴ * B = 1) (hA₀ : Aᴴ * (signMatrix s : Matrix n n ℂ) * A = 0)
    (hB₀ : Bᴴ * (signMatrix s : Matrix n n ℂ) * B = 0) :
    ∃ κ ∈ (maxCompactU s : Set (USign s)), (κ : Matrix n n ℂ) * A = B := by
  -- An isotropic subspace is the graph of an isometry between the coordinates of sign 1 and those
  -- of sign -1: the rows of either sign of such a frame have the Gram matrix ½.
  let rows (ε : ℤˣ) (X : Matrix n p ℂ) : Matrix {i : n // s i = ε} p ℂ := X.submatrix (↑) id
  have h_half (ε : ℤˣ) {X : Matrix n p ℂ} (hX : Xᴴ * X = 1) (hX₀ : Xᴴ * signMatrix s * X = 0) :
      (2 : ℂ) • (rows ε X)ᴴ * rows ε X = 1 := by
    have h_sum : (2 : ℂ) • (rows ε X)ᴴ * rows ε X =
        Xᴴ * X + (ε : ℂ) • (Xᴴ * signMatrix s * X) := by
      ext a b
      simp only [rows, signMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
        conjTranspose_apply, submatrix_apply, id, diagonal_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      rw [← Finset.sum_subtype (Finset.univ.filter (s · = ε)) (by simp)
        fun i ↦ 2 * star (X i a) * X i b, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rcases Int.units_eq_one_or ε with rfl | rfl <;>
        rcases Int.units_eq_one_or (s i) with h | h <;> simp [h, two_mul, add_mul]
    rw [h_sum, hX, hX₀, smul_zero, add_zero]
  -- So for each sign a unitary matrix carries the rows of A to the rows of B.
  have h_witt (ε : ℤˣ) : ∃ g : U (1 : Matrix {i : n // s i = ε} {i : n // s i = ε} ℂ),
      g.val.val * rows ε A = rows ε B := by
    refine witt ⟨.I, by simp⟩ (by simp) isUnit_one ⟨_, h_half ε hA hA₀⟩ ⟨_, h_half ε hB hB₀⟩ ?_
    have h_two := (h_half ε hA hA₀).trans (h_half ε hB hB₀).symm
    simpa [Matrix.smul_mul, smul_right_inj (two_ne_zero' ℂ)] using h_two
  choose g hg using h_witt
  -- The two matrices are the diagonal blocks of κ.
  let σ : n ≃ Σ ε : ℤˣ, {i : n // s i = ε} := (Equiv.sigmaFiberEquiv s).symm
  let K : Matrix n n ℂ := (blockDiagonal' fun ε ↦ (g ε).val.val).submatrix σ σ
  have h_unitary : Kᴴ * K = 1 := by
    have h_block (ε : ℤˣ) : (g ε).val.valᴴ * (g ε).val.val = 1 := by
      simpa [star_eq_conjTranspose] using mem_unitaryGroupOf_iff.1 (g ε).prop
    simp [K, ← blockDiagonal'_mul, h_block, ← Pi.one_def]
  have h_comm : signMatrix s * K = K * signMatrix s := by
    ext i j
    by_cases h : s i = s j
    · simp [signMatrix, h, mul_comm]
    · simp [signMatrix, K, σ, blockDiagonal'_apply, h]
  have h_form : Kᴴ * signMatrix s * K = signMatrix s := by
    rw [Matrix.mul_assoc, h_comm, ← Matrix.mul_assoc, h_unitary, Matrix.one_mul]
  have h_mem : U.of IsHermitianInvolution.isUnit K h_form ∈ maxCompactU s := by
    simpa [maxCompactU, Subgroup.mem_subgroupOf, mem_unitaryGroupOf_iff,
        star_eq_conjTranspose] using h_unitary
  refine ⟨_, h_mem, ?_⟩
  ext i j
  -- Row i of κ A is the row i of the block of sign s i.
  calc (K * A) i j
      = ∑ k : Σ ε : ℤˣ, {i : n // s i = ε},
          (blockDiagonal' fun ε ↦ (g ε).val.val) ⟨s i, i, rfl⟩ k * A k.2 j :=
        Fintype.sum_equiv σ _ _ fun _ ↦ rfl
    _ = ((g (s i)).val.val * rows (s i) A) ⟨i, rfl⟩ j := by
        rw [Fintype.sum_sigma, Finset.sum_eq_single (s i)]
        · simp [Matrix.mul_apply, rows]
        · exact fun ε _ hε ↦ by simp [blockDiagonal'_apply_ne _ _ _ hε.symm]
        · exact fun h ↦ absurd (Finset.mem_univ _) h
    _ = B i j := congrFun (congrFun (hg (s i)) ⟨i, rfl⟩) j

/-- For a Witt decomposition `H` of `W` with isotropic frame `k`, every `g` in the adelic unitary
group `G E s` of `W` has a right translate `g * κ`. Here `κ` lies in the maximal compact subgroup
K_∞K₀, and `g * κ` acts on `k` by some `b` in GL_p(𝔸) (`H.ActsOnFrame`: g κ k = k b). This `b` is
block triangular for the weights `wt : p → ℕ`. -/
lemma exists_mem_maxCompact_actsOnFrame (g : G E s) (wt : p → ℕ) :
    ∃ κ ∈ maxCompact E s, ∃ b : GL p (𝔸 E),
      b.val.BlockTriangular wt ∧ H.ActsOnFrame (g * κ) b.val := by
  -- Apply `iwasawa_of_witt` at each infinite place, with orthonormal frames (Gram–Schmidt), and
  -- at the finite places, with frames that are integral and left invertible over Ô (Witt's
  -- theorem over Ô is `witt_Ô`); then glue the components.
  choose κ hκ b hb h_inf using fun w : NumberField.InfinitePlace E ↦
    H.iwasawa_of_witt (P := fun X ↦ Xᴴ * X = 1) (evalInf w) (g.fst w)
      (exists_orthonormal_mul wt) exists_unitary_mul_eq_of_isotropic
      (by simp [← ext_iff, lCoord, stdForm, signMatrix])
  let fin : 𝔸 E →+* 𝔸f E := RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)
  obtain ⟨κ', hκ', b', hb', h_fin⟩ :=
    H.iwasawa_of_witt fin g.snd
      (fun hX ↦ isValuationPair_Ô.exists_isPrimitiveMatrix_mul hX wt)
      (fun hX hY hX₀ hY₀ ↦ witt_Ô hX hY (by simpa using hX₀.trans hY₀.symm))
      (by simp [← ext_iff, fin, lCoord, stdForm] :
        H.lCoord.map fin = (H.kAdelic.map fin)ᴴ * (1 : Matrix n n (𝔸f E)))
  refine ⟨(κ, κ'), ⟨fun w _ ↦ hκ w, hκ'⟩, mkAdelicGL (b, b'),
    fun i j hij ↦ Prod.ext (funext fun w ↦ hb w hij) (hb' hij),
    matrix_ext_𝔸 (fun w ↦ ?_) ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact h_inf w
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact h_fin

/-- The Iwasawa decomposition. Every `g` has a right translate `g * κ`, with `κ` in the maximal
compact subgroup, that acts on the isotropic frame by a matrix `b`, block triangular for the
weights `wt` (`H.ActsOnFrame`), and is therefore the product of a unipotent element
`H.radicalElement c z`, with adelic matrices `c`, `z`, and the Levi element `H.levi (b, u)`, where
`u` is in the unitary group of the smaller space. For the first part alone see
`New.Space.Splitting.exists_mem_maxCompact_actsOnFrame`.

This is an adelic form of the Iwasawa decomposition G = PK (Bruhat–Tits at the finite places) for
this unitary group and the stabilisers of isotropic flags. -/
lemma iwasawa (g : G E s) (wt : p → ℕ) :
    ∃ κ ∈ maxCompact E s, ∃ b : GL p (𝔸 E),
      b.val.BlockTriangular wt ∧
      H.ActsOnFrame (g * κ) b.val ∧
      ∃ (c : Matrix n₀ p (𝔸 E)) (z : Matrix p p (𝔸 E)) (u : G E s₀),
        g * κ = H.radicalElement c z * H.levi (b, u) := by
  obtain ⟨κ, hκ, b, h_triangular, h_frame⟩ := H.exists_mem_maxCompact_actsOnFrame g wt
  -- An element that stabilises the span of the frame is a radical element times a Levi element.
  obtain ⟨c, z, t, u, h_eq, ht : t.val = b.val, -⟩ := H.exists_eq_radicalElement_mul_levi h_frame
  obtain rfl : t = b := Units.ext ht
  exact ⟨κ, hκ, t, h_triangular, h_frame, c, z, u, h_eq⟩

/-- The Iwasawa decomposition with an adapted factor: every `g` is an element of the radical times a
Levi element times an element `h` adapted to the splitting `H` and the basis `1`. -/
lemma exists_eq_radicalElement_mul_levi_mul_isAdapted {E n n₀ p : Type} [Field E] [CMType E]
    [WeilData E] [Fintype n] [DecidableEq n] [Fintype n₀] [DecidableEq n₀] [Fintype p]
    [DecidableEq p] {s : n → ℤˣ} {s₀ : n₀ → ℤˣ}
    {W : Space E n s} {W₀ : Space E n₀ s₀} (H : W.Splitting W₀ p) (g : G E s) :
    ∃ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)) (a : GL p (𝔸 E)) (g₀ : G E s₀) (h : G E s),
      H.IsAdapted h 1 ∧
      g = H.radicalElement c b * H.levi (a, g₀) * h := by
  -- Write `g = q κ⁻¹` and an adapted `h₁ = q₁ κ₁⁻¹` with `q`, `q₁` parabolic and `κ`, `κ₁` compact.
  obtain ⟨h₁, h_adapted : H.IsAdapted h₁ 1, -⟩ := H.exists_isAdapted_and_frame_eq 1
  obtain ⟨κ, hκ, a, -, ha⟩ := H.exists_mem_maxCompact_actsOnFrame g (wt := 0)
  obtain ⟨κ₁, hκ₁, a₁, -, ha₁⟩ := H.exists_mem_maxCompact_actsOnFrame h₁ (wt := 0)
  have h_inv : H.ActsOnFrame (h₁ * κ₁)⁻¹ a₁⁻¹.val :=
    calc (h₁ * κ₁)⁻¹.adeleMatrix * H.kAdelic
        = (h₁ * κ₁)⁻¹.adeleMatrix * (H.kAdelic * a₁.val) * a₁⁻¹.val := by simp [Matrix.mul_assoc]
      _ = H.kAdelic * a₁⁻¹.val := by
        rw [← ha₁, ← Matrix.mul_assoc, ← G.adeleMatrix_mul, inv_mul_cancel, G.adeleMatrix_one,
          Matrix.one_mul]
  have h_parabolic : H.ActsOnFrame (g * κ * (h₁ * κ₁)⁻¹) (a.val * a₁⁻¹.val) := by
    rw [ActsOnFrame, G.adeleMatrix_mul, Matrix.mul_assoc, h_inv, ← Matrix.mul_assoc, ha,
      Matrix.mul_assoc]
  obtain ⟨c, b, t, g₀, h_eq : g * κ * (h₁ * κ₁)⁻¹ = H.radicalElement c b * H.levi (t, g₀), -⟩ :=
    H.exists_eq_radicalElement_mul_levi h_parabolic
  refine ⟨c, b, t, g₀, h₁ * (κ₁ * κ⁻¹),
    h_adapted.mul_of_mem_maxCompact (mul_mem hκ₁ (inv_mem hκ)), ?_⟩
  rw [← h_eq]
  group

end New.Space.Splitting

end
