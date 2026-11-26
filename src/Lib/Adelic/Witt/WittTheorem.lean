module

import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Witt.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
public import Lib.Adelic.Unitary.Defs
public import Lib.General.LinearAlgebra.IntegralLattices
import Lib.Adelic.Adeles.IdeleModulus
import Lib.Base
import Lib.GaloisRep.Hilbert90.TameActions
import Lib.GaloisRep.Hilbert90.UnitaryGroups

/-!
# Witt's theorem over fields and over Ô; quasi-reflections, Eichler maps, frames

`J` is a hermitian matrix over a commutative ring with involution, with form
`h(u, v) = star u ⬝ᵥ J *ᵥ v`, and `New.U J` is the group of invertible `g` with `gᴴ * J * g = J`.
For invertible such `J`, Witt's theorem says that left invertible matrices with equal Gram matrices
differ by an element of `New.U J`. It is proved over a field with nontrivial involution using
quasi-reflections. Let `E` be a CM field that contains a primitive root of unity of order 5040
(`New.HasPrimitiveRoot5040 E`). Over its integral finite adeles `New.Ô E`, invertible hermitian
matrices have orthonormal bases, units fixed by conjugation are norms, and Witt's theorem is proved
for the standard hermitian form and primitive matrices, with an integral unitary matrix. For the
split form `T.splitGram` with `ϱ` hyperbolic planes and middle block `T`, the file then studies the
frame `f = (e₁, …, e_ϱ, z)` (`𝔰.besselFrame`, whose last entry `𝔰.besselFrame 𝔰.top` is `z`) and the
action of the unipotent group `New.Shape.Form.besselU` on it.

## Main definitions and results

* `New.quasiReflection`: the quasi-reflection along `v`, for a unit `σ` with `σ + star σ = h(v, v)`.
* `New.witt_of_quasiReflection_mem`: left invertible `X`, `Y` with the same Gram matrix satisfy
  `g * X = Y` for some `g` in any subgroup of `New.U J` that contains all quasi-reflections.
* `New.witt`: the same with `g` in `New.U J`.
* `New.exists_orthonormal_Ô`: a hermitian matrix invertible over `Ô` is `Ô`-congruent to `1`.
* `New.witt_Ô`: Witt's theorem for primitive `n × k` matrices over `Ô`.
* `New.exists_unitary_eq_eichlerMap`: for hermitian `J`, the Eichler map
  `v ↦ v + h(u, v) x - h(x, v) (u + ς x)` (`New.eichlerMap`) is an isometry if `x` is isotropic, `u`
  is orthogonal to `x` and `ς + star ς = h(u, u)`.

Notions from other files:
* `New.Shape`: the data `𝔰` of a number `ϱ` of hyperbolic planes and a finite index set `κ`. A
  `T : 𝔰.Form A` is a square matrix indexed by `κ` and one more index `z`.
* `New.Shape.Form.splitGram`: the Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix T: identity blocks pair the first and last ϱ indices, T is the middle block, all else is
  zero. Its unitary group is `T.G`.
* `New.Shape.Form.frameGram`: the (ϱ+1) × (ϱ+1) matrix of the products h(f_j, γ f_l) of the frame f
  with its image under γ, where h is the form `New.Shape.Form.splitGram T`.
* `New.frameMatrix`: the submatrix of γ on the rows and columns of the frame.
* `New.intGL`: for a subring O of R, the subgroup GL_n(O) of GL_n(R): matrices with entries in O
  whose inverse has entries in O.
* `New.IsPrimitiveMatrix`: a matrix and some left inverse of it have entries in a subring.

## Relation to the literature

Known; see `Lib.Adelic.Witt.IwasawaDecomposition`, `Lib.DiscreteSeries.Bruhat.FloorGroups` and
`Lib.DiscreteSeries.Bruhat.ComplexPlace` for sources.
-/

@[expose] public section

/-! ## Quasi-reflections -/

section QuasiReflection

open Matrix IsLocalRing

namespace New

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] [StarRing R] {J : Matrix n n R}

omit [DecidableEq n] in
/-- The form h(u, v) = uᴴ J v of a hermitian matrix `J` is hermitian: the conjugate of h(u, v) is
h(v, u). -/
lemma star_dotProduct_mulVec_comm (hJ : Jᴴ = J) (u v : n → R) :
    star (star u ⬝ᵥ J *ᵥ v) = star v ⬝ᵥ J *ᵥ u := by
  grind [star_dotProduct, star_mulVec_dotProduct]

/-- The quasi-reflection x ↦ x − v σ⁻¹ h(v, x) in U(J), where h(v, x) = vᴴJx, J is hermitian and
invertible, and σ is a unit with σ + σ̄ = h(v, v). -/
noncomputable def quasiReflection (hJ : Jᴴ = J) (hJ' : IsUnit J) (v : n → R) (σ : Rˣ)
    (h : (σ : R) + star (σ : R) = star v ⬝ᵥ J *ᵥ v) : U J :=
  U.of hJ' (1 - (↑σ⁻¹ : R) • vecMulVec v (star v ᵥ* J)) <| by
    set τ : R := ↑σ⁻¹
    have h_coeff : τ * star τ * (star v ᵥ* J ⬝ᵥ v) = star τ + τ := by
      have hτ : τ * σ = 1 := σ.inv_mul
      have hτ_star : star τ * star (σ : R) = 1 := by rw [← star_mul', hτ, star_one]
      rw [← dotProduct_mulVec, ← h]
      linear_combination star τ * hτ + τ * hτ_star
    ext i j
    simp [sub_mul, mul_sub, vecMulVec_mul, mul_vecMulVec, star_vecMul, vecMulVec_mulVec,
      vecMulVec_apply, hJ]
    linear_combination (J *ᵥ v) i * (star v ᵥ* J) j * h_coeff

/-- The quasi-reflection along `v` with parameter `σ` sends `x` to `x − σ⁻¹ h(v, x) v`. -/
lemma quasiReflection_mulVec (hJ : Jᴴ = J) (hJ' : IsUnit J) (v : n → R) (σ : Rˣ)
    (hσ : (σ : R) + star (σ : R) = star v ⬝ᵥ J *ᵥ v) (x : n → R) :
    quasiReflection hJ hJ' v σ hσ *ᵥ x = x - ((↑σ⁻¹ : R) * star v ⬝ᵥ J *ᵥ x) • v := by
  simp [quasiReflection, sub_mulVec, smul_mulVec, vecMulVec_mulVec, dotProduct_mulVec, smul_smul]

end New

end QuasiReflection

namespace New

/-!
## Witt's theorem over a field with involution

Witt's extension theorem for an invertible hermitian matrix `J` over a field with an involution that
is not the identity (some `z - star z` is a unit).

The columns are matched one at a time, each by at most two quasi-reflections that fix the columns
already matched.
-/

section Witt

open Matrix Finset

variable {R n k : Type _} [Field R] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
variable {X Y : Matrix n k R}

omit [DecidableEq n] in
lemma HasLeftInv.injective_mulVec (hX : HasLeftInv X) : X.mulVec.Injective :=
  let ⟨L, (hL : L * X = 1)⟩ := hX
  Function.LeftInverse.injective (g := L.mulVec) fun x ↦ by simp [hL]

/-- A matrix `X` over a field whose map `x ↦ X *ᵥ x` has trivial kernel has a left inverse. -/
lemma HasLeftInv.of_ker_le_bot (h_ker : X.mulVecLin.ker ≤ ⊥) : HasLeftInv X := by
  obtain ⟨g, hg⟩ := X.toLin'.exists_leftInverse_of_injective (le_bot_iff.1 h_ker)
  refine ⟨g.toMatrix', toLin'.injective ?_⟩
  rw [toLin'_mul, toLin'_toMatrix', hg, toLin'_one]

/-- A nonzero vector over a field, read as a matrix with one column, has a left inverse. -/
lemma HasLeftInv.of_ne_zero {x : n → R} (h_ne : x ≠ 0) : HasLeftInv (replicateCol Unit x) := by
  obtain ⟨i, hi⟩ : ∃ i : n, x i ≠ 0 := Function.ne_iff.1 h_ne
  exact ⟨single () i (x i)⁻¹, by aesop⟩

/-- A subspace `L` of `n → R` has a basis written as the columns of an `n × d` matrix `x`, where `d`
is the dimension of `L`: `x` has a left inverse and its column space is `L`. -/
lemma Filling.exists_hasLeftInv_colSpan_eq (L : Submodule R (n → R)) :
    ∃ x : Matrix n (Fin (Module.finrank R L)) R, HasLeftInv x ∧ colSpan x = L := by
  let e : (Fin (Module.finrank R L) → R) ≃ₗ[R] L := .ofFinrankEq _ _ (by simp)
  let f : (Fin (Module.finrank R L) → R) →ₗ[R] n → R := L.subtype ∘ₗ e.toLinearMap
  have h_lin : f.toMatrix'.mulVecLin = f := by rw [← toLin'_apply', toLin'_toMatrix']
  have h_ker : f.ker = ⊥ := by simp [f, LinearMap.ker_comp]
  have h_range : f.range = L := by simp [f]
  exact ⟨f.toMatrix', .of_ker_le_bot (by rw [h_lin, h_ker]), by rw [colSpan, h_lin, h_range]⟩

variable [StarRing R] {J : Matrix n n R}

omit [DecidableEq n] in
lemma HasLeftInv.of_isUnit_gram (h_gram : IsUnit (Xᴴ * J * X)) : HasLeftInv X :=
  ⟨h_gram.unit⁻¹.val * (Xᴴ * J), by rw [Matrix.mul_assoc, h_gram.val_inv_mul]⟩

/-- Witt's theorem by quasi-reflections: over a field with involution having some z ≠ z̄, for
invertible hermitian J and a subgroup H of the unitary group U(J) containing all quasi-reflections
x ↦ x − v σ⁻¹ vᴴJx, left invertible X, Y with XᴴJX = YᴴJY satisfy gX = Y for some g in H.

A variant of Witt's extension theorem for nondegenerate hermitian forms. -/
lemma witt_of_quasiReflection_mem (hz : ∃ z : R, IsUnit (z - star z)) {J : Matrix n n R}
    (hJ : Jᴴ = J) (hJ' : IsUnit J) (hX : HasLeftInv X) (hY : HasLeftInv Y)
    (h_gram : Xᴴ * J * X = Yᴴ * J * Y) (H : Subgroup (U J))
    (hH : ∀ (v : n → R) (σ : Rˣ) (hσ : (σ : R) + star (σ : R) = star v ⬝ᵥ J *ᵥ v),
      quasiReflection hJ hJ' v σ hσ ∈ H) :
    ∃ g ∈ H, (g : Matrix n n R) * X = Y := by
  classical
  let B := Matrix.toLinearMapₛₗ₂' R (starRingEnd R) (RingHom.id R) J
  have hB (v w : n → R) : B v w = star v ⬝ᵥ J *ᵥ w := by
    simp [B, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, dotProduct, mulVec, Finset.mul_sum,
      mul_comm, mul_assoc]
  let V : TauCeti.SignedHermitianSpace R (n → R) (starRingEnd R) 1 :=
    { form := B
      form_swap := fun v w ↦ by
          simpa [hB, starRingEnd_apply] using (star_dotProduct_mulVec_comm hJ v w).symm
      separatingLeft := fun v hv ↦ funext fun i ↦ by
        obtain ⟨w, hw⟩ := mulVec_surjective_iff_isUnit.2 hJ' (Pi.single i 1)
        simpa [hB, hw] using hv w }
  have form (v w : n → R) : V.form v w = star v ⬝ᵥ J *ᵥ w := hB v w
  let act : U J →* ((n → R) ≃ₗ[R] (n → R)) :=
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R))).toMonoidHom.comp (U J).subtype
  have act_apply (g : U J) (x : n → R) : act g x = (g : Matrix n n R) *ᵥ x := rfl
  have h_sub : V.quasiReflectionSubgroup ≤ H.map act := V.quasiReflectionSubgroup_le_iff.2 <| by
    intro v s hs
    have h_trace : (s : R) + star (s : R) = star v ⬝ᵥ J *ᵥ v := by
      simpa [form, starRingEnd_apply] using hs
    refine ⟨quasiReflection hJ hJ' v s h_trace, hH v s h_trace, ?_⟩
    ext x
    simp [act_apply, quasiReflection_mulVec, TauCeti.SignedHermitianSpace.quasiReflection_apply,
      form]
  have h_col (i j : k) : V.form (X.col i) (X.col j) = V.form (Y.col i) (Y.col j) := by
    rw [form, form, dotProduct_mulVec, dotProduct_mulVec]
    exact congrFun₂ h_gram i j
  obtain ⟨g, hg, h_map⟩ := V.exists_mem_quasiReflectionSubgroup_apply_eq
    (hz.imp fun _ hz h ↦ hz.ne_zero (sub_eq_zero.2 h.symm))
    (mulVec_injective_iff.1 hX.injective_mulVec) (mulVec_injective_iff.1 hY.injective_mulVec) h_col
  obtain ⟨u, hu, rfl⟩ := h_sub hg
  exact ⟨u, hu, ext_col fun i ↦ h_map i⟩

/-- **Witt's theorem.** Let `R` be a field with an involution that is not the identity and let `J`
be an invertible hermitian matrix. Left invertible `X`, `Y` with `Xᴴ * J * X = Yᴴ * J * Y` satisfy
`g * X = Y` for some `g` in the unitary group `U J` of the `g` with `gᴴ * J * g = J`.

Known result: Witt's extension theorem for hermitian forms. -/
lemma witt (hz : ∃ z : R, IsUnit (z - star z)) {J : Matrix n n R} (hJ : Jᴴ = J) (hJ' : IsUnit J)
    (hX : HasLeftInv X) (hY : HasLeftInv Y) (h_gram : Xᴴ * J * X = Yᴴ * J * Y) :
    ∃ g : U J, (g : Matrix n n R) * X = Y :=
  let ⟨g, _, hg⟩ := witt_of_quasiReflection_mem hz hJ hJ' hX hY h_gram ⊤ (by simp)
  ⟨g, hg⟩

end Witt

end New

/-!
## Orthonormal bases and norms over Ô

Two consequences of `E` containing a primitive root of unity of order `7! = 5040`
(`New.HasPrimitiveRoot5040`), for the ring `New.Ô` of integral finite adeles of a CM field `E`. This
hypothesis is stronger than `E/E⁺` being unramified at the finite places. It is used through an
element `z` of `Ô E` with `z - star z` a unit (`New.exists_isUnit_sub_star_Ô`), which gives
orthonormal frames over the profinite ring `Ô E` (`New.exists_fixed_orthonormal_frame`).

* `New.exists_orthonormal_Ô`: a hermitian matrix invertible over `Ô` is `Ô`-congruent to `1`.
* `New.exists_unit_star_mul_self_eq`: a conjugation-invariant unit of `Ô` is a norm `star x * x`;
  this is the case of `1 × 1` matrices.
-/

section OrthonormalFrame

open Matrix NumberField

namespace New

variable {E n : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]

/-- If the CM field `E` contains a primitive root of unity of order 5040, the ring `Ô E` of its
integral finite adeles has an element `z` such that `z - star z` is a unit. -/
lemma exists_isUnit_sub_star_Ô [HasPrimitiveRoot5040 E] : ∃ z : Ô E, IsUnit (z - star z) := by
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, IsUnit (z - star z) := HasPrimitiveRoot5040.exists_isUnit_sub_star
  have h_star : star (algebraMap (𝓞 E) (Ô E) z) = algebraMap (𝓞 E) (Ô E) (star z) := by
    ext v : 3
    simp
  exact ⟨algebraMap (𝓞 E) (Ô E) z,
    by simpa only [h_star, map_sub] using hz.map (algebraMap (𝓞 E) (Ô E))⟩

/-- Let the CM field `E` contain a primitive root of unity of order 5040. An invertible hermitian
matrix `b` over the ring `Ô E` of integral finite adeles has an orthonormal frame `g` that is
congruent to `1` modulo the left ideal generated by `b - 1`. -/
lemma exists_orthonormal_frame_Ô [HasPrimitiveRoot5040 E] {b : Matrix n n (Ô E)}
    (hb_unit : IsUnit b) (hb_herm : bᴴ = b) :
    ∃ g W : Matrix n n (Ô E), g = 1 + W * (b - 1) ∧ gᴴ * b * g = 1 := by
  -- This is `exists_fixed_orthonormal_frame` for the trivial automorphism.
  obtain ⟨z, hz⟩ := exists_isUnit_sub_star_Ô (E := E)
  obtain ⟨g, W, hg, -, h_frame⟩ := exists_fixed_orthonormal_frame isProfiniteRing_intAdeles
    isTameAtLevel_one rfl hz (by simp) hb_unit hb_herm rfl
  exact ⟨g, W, hg, h_frame⟩

end New

end OrthonormalFrame

section OrthonormalAdelic

open Matrix NumberField New

variable {E : Type _} {n : Type _} [Field E] [NumberField E] [Fintype n]
variable [IsCMField E] [HasPrimitiveRoot5040 E]

/-- Let the CM field `E` contain a primitive root of unity of order 5040, and let `Ô E` be its ring
of integral finite adeles. A hermitian matrix `b` with entries in the finite adeles `𝔸f E`, lying in
`GL_n(Ô E)` (`IsUnimodular (Ô E) b`) satisfies `kᴴ b k = 1` for some `k` in `GL_n(Ô E)`.

An adelic variant, over all finite places at once, of the local fact that unimodular hermitian
lattices in the unramified case have orthonormal bases (Kirschmer). -/
lemma New.exists_orthonormal_Ô [DecidableEq n] {b : Matrix n n (𝔸f E)}
    (hb : IsUnimodular (Ô E) b) : ∃ k ∈ intGL n (Ô E), k.valᴴ * b * k.val = 1 := by
  -- `b` comes from an invertible hermitian matrix `B` over the ring `Ô E`, where
  -- `exists_orthonormal_frame_Ô` gives an orthonormal frame.
  obtain ⟨hb_herm, u, hu, rfl⟩ := hb
  obtain ⟨B, rfl⟩ : ∃ B : GL n (Ô E), GeneralLinearGroup.map (Ô E).subtype B = u := hu
  have hB_herm : B.valᴴ = B := by simpa [← ext_iff, Subtype.ext_iff] using hb_herm
  obtain ⟨g, -, -, hg : gᴴ * B * g = 1⟩ := exists_orthonormal_frame_Ô B.isUnit hB_herm
  -- `g` is invertible over `Ô E`, with inverse `gᴴ * B`; map everything to the adeles
  let G : GL n (Ô E) := ⟨g, gᴴ * B, mul_eq_one_symm hg, hg⟩
  refine ⟨GeneralLinearGroup.map (Ô E).subtype G, ⟨G, rfl⟩, ?_⟩
  change (g.map (Ô E).subtype)ᴴ * B.val.map (Ô E).subtype * g.map (Ô E).subtype = 1
  rw [← map_conjTranspose_mul_mul (Ô E).subtype (by simp), hg]
  simp

/-- Let the CM field `E` contain a primitive root of unity of order 5040. Every
conjugation-invariant finite adele `u` of `E` that is a local unit at every finite place is the norm
`star x * x` of a unit `x` of the ring `Ô E` of integral finite adeles.

Units are norms in unramified extensions of local fields (cf. Jacobowitz, Kirschmer). This is the
quadratic case of conjugation on `E`, at all finite places at once, split places included. -/
lemma New.exists_unit_star_mul_self_eq {u : 𝔸f E} (hu_star : star u = u)
    (hu_val : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), Valued.v (u w) = 1) :
    ∃ x : (Ô E)ˣ, star (x : 𝔸f E) * x = u := by
  -- The case of `1 × 1` matrices of `exists_orthonormal_frame_Ô`: some `c` has
  -- `star c * u * c = 1`, and then `u` is the norm of `c⁻¹ = star c * u`.
  let u' : Ô E := ⟨u, mem_Ô.2 fun w ↦ (hu_val w).le⟩
  have hu'_star : star u' = u' := Subtype.ext (by simpa using hu_star)
  obtain ⟨g, -, -, hg⟩ := exists_orthonormal_frame_Ô
    ((isUnit_Ô.2 hu_val : IsUnit u').map (scalar Unit)) (by simp [hu'_star])
  let c : Ô E := g () ()
  have hc : star c * u' * c = 1 := by simpa [Matrix.mul_apply] using congrFun₂ hg () ()
  have h_norm : star (star c * u') * (star c * u') = u' := by
    rw [star_mul', star_star, hu'_star]
    linear_combination u' * hc
  exact ⟨.mkOfMulEqOne (star c * u') c hc, by simpa using congrArg Subtype.val h_norm⟩

end OrthonormalAdelic

/-!
## Witt's theorem over Ô

Witt's theorem for the standard hermitian form over the integral finite adeles `New.Ô E` of a CM
field `E`: primitive matrices with the same Gram matrix differ by an integral unitary matrix.

* `New.isPrimitiveMatrix_iff`: a square matrix is primitive over `O` iff it lies in `New.intGL n O`.

The proof finds an invertible `a` with `a * X = Y` and `aᴴ * Y = X`. It then makes `a` unitary with
an orthonormal frame of `aᴴ * a` (`New.exists_orthonormal_frame_Ô`).
-/

section WittAdelic

open Matrix NumberField

namespace New

variable {E n k : Type*} [Field E] [NumberField E] [IsCMField E]
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [DecidableEq k]

omit [DecidableEq n] [Fintype k] in
/-- A matrix that is primitive over the subring `O` (it and some left inverse have entries in `O`)
comes from a left invertible matrix over the ring `O`. -/
lemma IsPrimitiveMatrix.exists_map_subtype_eq {R : Type*} [CommRing R] {O : Subring R}
    {X : Matrix n k R} (h : IsPrimitiveMatrix O X) :
    ∃ Y : Matrix n k O, HasLeftInv Y ∧ Y.map O.subtype = X := by
  -- Read `X` and its left inverse `L` as matrices over `O`.
  obtain ⟨hX, L, hL, hLX⟩ := h
  obtain ⟨X', rfl⟩ : ∃ X' : Matrix n k O, X'.map O.subtype = X := ⟨fun i j ↦ ⟨X i j, hX i j⟩, rfl⟩
  obtain ⟨L', rfl⟩ : ∃ L' : Matrix k n O, L'.map O.subtype = L := ⟨fun i j ↦ ⟨L i j, hL i j⟩, rfl⟩
  have h_map : (L' * X').map O.subtype = (1 : Matrix k k O).map O.subtype := by
    rw [Matrix.map_mul, hLX, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨X', ⟨L', map_injective O.subtype_injective h_map⟩, rfl⟩

/-- A square matrix is primitive over the subring `O` (it and some left inverse have entries in `O`)
iff it is invertible and both it and its inverse have entries in `O`. -/
lemma isPrimitiveMatrix_iff {R : Type*} [CommRing R] {O : Subring R} {g : Matrix n n R} :
    IsPrimitiveMatrix O g ↔ ∃ x ∈ intGL n O, x.val = g := by
  constructor
  · -- a left inverse `L` of a square matrix is its inverse: `g` is the inverse of the unit `L`
    rintro ⟨hg, L, hL, hLg⟩
    exact ⟨(Units.mkOfMulEqOne L g hLg)⁻¹, mem_intGL.2 ⟨hg, hL⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx_int, hx_inv_int⟩ := mem_intGL.1 hx
    exact ⟨hx_int, ↑x⁻¹, hx_inv_int, x.inv_mul⟩

omit [IsCMField E] in
/-- A square matrix over the ring `Ô E` of integral finite adeles is invertible if its reduction
to the residue field at every finite place is invertible. -/
lemma isUnit_of_forall_isUnit_reduceAt {M : Matrix n n (Ô E)}
    (hM : ∀ w : FinPlace E, IsUnit ((reduceAt w).mapMatrix M)) : IsUnit M := by
  rw [isUnit_iff_isUnit_det, isUnit_Ô]
  intro w
  have h_ne : reduceAt w M.det ≠ 0 := by
    simpa [RingHom.map_det] using ((isUnit_iff_isUnit_det _).1 (hM w)).ne_zero
  exact (mem_Ô.1 M.det.property w).eq_of_not_lt (by rwa [← reduceAt_eq_zero])

omit [IsCMField E] in
/-- For square matrices `a`, `x`, `y` over the ring `Ô E` of integral finite adeles of a number
field `E`, there is a matrix `c` such that `a + (1 - a * x) * c * (1 - y * a)` is invertible. -/
lemma exists_isUnit_add_Ô (a x y : Matrix n n (Ô E)) :
    ∃ c : Matrix n n (Ô E), IsUnit (a + (1 - a * x) * c * (1 - y * a)) := by
  -- Write `a = p * D * q` in Smith form and take `c = p * e * q`, where the diagonal idempotent `e`
  -- has `i`-th entry `1` at the places where `d i` reduces to zero, and `0` at the others.
  classical
  obtain ⟨p, -, q, -, d, rfl : a = p.val * diagonal d * q.val⟩ :=
    isValuationPair_Ô.top.smith_normal_form a
  set D : Matrix n n (Ô E) := diagonal d
  let e : Matrix n n (Ô E) := diagonal fun i ↦ ⟨idem {w | reduceAt w (d i) = 0}, idem_mem_Ô _⟩
  refine ⟨p * e * q, isUnit_of_forall_isUnit_reduceAt fun w ↦ ?_⟩
  set r : Matrix n n (Ô E) →+* Matrix n n (ResField w) := (reduceAt w).mapMatrix (m := n)
  -- modulo `w`, in each diagonal position exactly one of `D` and `e` is non-zero
  have ⟨D_mul_e, e_mul_D, e_mul_e⟩ : r D * r e = 0 ∧ r e * r D = 0 ∧ r e * r e = r e := by
    simp [D, e, r, diagonal_map (map_zero _), funext_iff, -reduceAt_eq_zero]
  -- these relations show that `D + e` is a two-sided multiple of the matrix modulo `w`
  refine isUnit_of_mul_isUnit_right (x := r ((1 + D * q * x * p * e) * p⁻¹))
    (isUnit_of_mul_isUnit_left (y := r (q⁻¹ * (1 + e * q * y * p * D))) ?_)
  suffices h : IsUnit (r D + r e) by
    convert h using 1
    rw [← map_mul, ← map_mul]
    simp [add_assoc, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, D_mul_e, e_mul_D, e_mul_e,
      ← mul_assoc (r D) (r e), ← mul_assoc (r e) (r D), ← mul_assoc (r e) (r e)]
  simp [D, e, r, diagonal_map (map_zero _), isUnit_iff_isUnit_det, Finset.prod_ne_zero_iff,
    -reduceAt_eq_zero]
  grind

/-- For left invertible matrices `X`, `Y` over the ring `Ô E` of integral finite adeles of a CM
field `E` with `Xᴴ X = Yᴴ Y`, some invertible `a` sends `X` to `Y` while its adjoint sends `Y`
to `X`. -/
lemma exists_isUnit_mul_eq_and_conjTranspose_mul_eq {X Y : Matrix n k (Ô E)} (hX : HasLeftInv X)
    (hY : HasLeftInv Y) (h_gram : Xᴴ * X = Yᴴ * Y) :
    ∃ a : Matrix n n (Ô E), IsUnit a ∧ a * X = Y ∧ aᴴ * Y = X := by
  obtain ⟨L, hL : L * X = 1⟩ := hX
  obtain ⟨M, hM : M * Y = 1⟩ := hY
  -- `a₀` has both properties; it is corrected to a unit by a term that kills `X` and whose
  -- adjoint kills `Y`
  let a₀ : Matrix n n (Ô E) := Y * L + Mᴴ * Xᴴ * (1 - X * L)
  have ⟨ha₀_X, ha₀_Y⟩ : a₀ * X = Y ∧ a₀ᴴ * Y = X := by
    simp [a₀, hL, hM, h_gram, Matrix.mul_assoc, Matrix.sub_mul, Matrix.add_mul]
  obtain ⟨c, hc⟩ := exists_isUnit_add_Ô a₀ (Lᴴ * Yᴴ) (X * M)
  refine ⟨a₀ + (1 - a₀ * (Lᴴ * Yᴴ)) * c * (1 - X * M * a₀), hc, ?_, ?_⟩
  · simp [ha₀_X, hM, Matrix.mul_assoc, Matrix.sub_mul, Matrix.add_mul]
  · simp [ha₀_Y, hL, Matrix.mul_assoc, Matrix.sub_mul, Matrix.add_mul]

/-- Witt's theorem over the ring `Ô E` of integral finite adeles of a CM field `E` that contains a
primitive root of unity of order 5040: two `n × k` matrices `X`, `Y` with entries in `Ô E`, left
inverses over `Ô E` and `Xᴴ X = Yᴴ Y` satisfy `g X = Y` for some `g` in `stdLevel E n`, the group of
`g` in `GL_n(Ô E)` with `gᴴ g = 1`.

An integral variant of Witt's extension theorem for hermitian forms. It treats only the standard
form, not a general invertible hermitian matrix. -/
lemma witt_Ô [HasPrimitiveRoot5040 E] {X Y : Matrix n k (𝔸f E)}
    (hX : IsPrimitiveMatrix (Ô E) X) (hY : IsPrimitiveMatrix (Ô E) Y) (h_gram : Xᴴ * X = Yᴴ * Y) :
    ∃ g ∈ stdLevel E n, (g : Matrix n n (𝔸f E)) * X = Y := by
  -- Over `Ô E`, find an invertible `a` with `a * X = Y` and `aᴴ * Y = X`. Then `aᴴ * a` fixes `X`,
  -- so does its orthonormal frame `T`, and `a * T` is unitary and sends `X` to `Y`.
  obtain ⟨X, hX_inv : HasLeftInv X, rfl⟩ := hX.exists_map_subtype_eq
  obtain ⟨Y, hY_inv : HasLeftInv Y, rfl⟩ := hY.exists_map_subtype_eq
  have h_gram' : Xᴴ * X = Yᴴ * Y := by
    simpa [← ext_iff, Matrix.mul_apply, Subtype.ext_iff] using h_gram
  obtain ⟨a, ha_unit, ha_X, ha_Y⟩ :=
    exists_isUnit_mul_eq_and_conjTranspose_mul_eq hX_inv hY_inv h_gram'
  -- the frame `T` of the hermitian unit `aᴴ * a` is `1` modulo `aᴴ * a - 1`, which kills `X`
  obtain ⟨T, W, hT : T = 1 + W * (aᴴ * a - 1), hT_frame : Tᴴ * (aᴴ * a) * T = 1⟩ :=
    exists_orthonormal_frame_Ô (b := aᴴ * a) (by simp [isUnit_conjTranspose, ha_unit]) (by simp)
  have hT_X : T * X = X := by
    simp [hT, ha_X, ha_Y, Matrix.mul_assoc, Matrix.sub_mul, Matrix.add_mul]
  let g : U (1 : Matrix n n (Ô E)) :=
    U.of isUnit_one (a * T) (by simpa [mul_assoc] using hT_frame)
  refine ⟨U.map (Ô E).subtype (by simp) (by simp) g, ⟨g.val, rfl⟩, ?_⟩
  change (a * T).map (Ô E).subtype * X.map (Ô E).subtype = Y.map (Ô E).subtype
  rw [← Matrix.map_mul, Matrix.mul_assoc, hT_X, ha_X]

/-- Witt's theorem for orthonormal frames over the ring `Ô E` of integral finite adeles of a CM
field `E` that contains a primitive root of unity of order 5040: if the matrices `X` and `Y` over
the finite adeles `𝔸f E` have entries in `Ô E` and Gram matrix `1` for the hermitian form with
matrix `1`, then `g * X = Y` for some `g` in `stdLevel E n`, the group of `g` in `GL_n(Ô E)` with
`gᴴ g = 1`. -/
lemma witt_Ô_of_orthonormal [HasPrimitiveRoot5040 E] {X Y : Matrix n k (𝔸f E)}
    (hX_gram : Xᴴ * (1 : Matrix n n (𝔸f E)) * X = 1)
    (hY_gram : Yᴴ * (1 : Matrix n n (𝔸f E)) * Y = 1)
    (hX_int : IsIntMatrix (Ô E) X) (hY_int : IsIntMatrix (Ô E) Y) :
    ∃ g ∈ stdLevel E n, (g : Matrix n n (𝔸f E)) * X = Y := by
  rw [Matrix.mul_one] at hX_gram hY_gram
  have h_prim {Z : Matrix n k (𝔸f E)} (h_int : IsIntMatrix (Ô E) Z) (h_gram : Zᴴ * Z = 1) :
      IsPrimitiveMatrix (Ô E) Z :=
    ⟨h_int, Zᴴ, fun i j ↦ star_mem_Ô (h_int j i), h_gram⟩
  exact witt_Ô (h_prim hX_int hX_gram) (h_prim hY_int hY_gram) (hX_gram.trans hY_gram.symm)

end New

end WittAdelic

/-!
## The unipotent Bessel group acting on the frame

The basis indices `New.Shape.BesselIndex` are `e₁, …, e_ϱ`, then the middle indices (those of `κ`
and `z`), then `e*₁, …, e*_ϱ`.

* `New.eq_one_of_mem_besselU_of_fix`: an element of `New.Shape.Form.besselU` that fixes ϱ vectors
  whose coordinates at `e*₁, …, e*_ϱ` form the identity matrix is trivial.
-/

namespace New

section FrameAction

open Matrix Fin Sum Function BesselIndex

variable {A : Type*} [CommRing A] {𝔰 : Shape}
variable {T : 𝔰.Form A} [StarRing A]
variable {x x' γ : T.G}

@[simp]
lemma besselFrame_castSucc (a : Fin 𝔰.ϱ) : 𝔰.besselFrame (castSucc a) = inl a := by
  simp [besselFrame]

@[simp]
lemma besselFrame_top : 𝔰.besselFrame 𝔰.top = 𝔰.z := by simp [besselFrame]

/-- The vector in position `a` of the frame (e₁, …, e_ϱ, z) has level `a`, where `level` is the
grading of the basis indices for which `New.Shape.Form.besselU` is block unitriangular. -/
lemma level_besselFrame (a : Fin (𝔰.ϱ + 1)) : level (𝔰.besselFrame a) = a := by
  induction a using lastCases <;> simp [level]

lemma besselFrame_injective : 𝔰.besselFrame.Injective := by simp [Injective, forall_fin_succ']

/-- For the grading `level` of the basis indices, for which `besselU` is block unitriangular, the
middle indices (of level ϱ) and those of e*₁, …, e*_ϱ (of level 2ϱ − a in position `a`) have level
at least ϱ. -/
lemma le_level_inr (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) : 𝔰.ϱ ≤ level (inr i : 𝔰.BesselIndex) := by
  cases i with
  | inl i => simp [level]
  | inr a =>
    change 𝔰.ϱ ≤ 2 * 𝔰.ϱ - a
    omega

/-- An element `x` of the block unitriangular group `New.Shape.Form.besselU` acts on the frame
(e₁, …, e_ϱ, z) by an upper unitriangular matrix: `frameMatrix x`, the submatrix of `x` on the
frame, agrees with the identity on and below the diagonal. -/
lemma frameMatrix_unitriangular (hx : x ∈ T.besselU) (a b : Fin (𝔰.ϱ + 1)) (hba : b ≤ a) :
    frameMatrix x a b = (1 : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) A) a b := by
  simpa [frameMatrix, Matrix.one_apply, besselFrame_injective.eq_iff] using
    mem_besselU.1 hx (𝔰.besselFrame a) (𝔰.besselFrame b) (by simpa [level_besselFrame] using hba)

/-- An element of the unitary group `T.G` lies in `besselU0`, the elements of the block
unitriangular group `besselU` that fix each vector of the frame (e₁, …, e_ϱ, z), iff it lies in
`besselU` and its submatrix on the frame is the identity. -/
lemma mem_besselU0_iff : x ∈ T.besselU0 ↔ x ∈ T.besselU ∧ frameMatrix x = 1 := by
  let g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := x
  have h_fixer : x ∈ T.besselFixer ↔ ∀ (i : 𝔰.BesselIndex) (b : Fin (𝔰.ϱ + 1)),
      g i (𝔰.besselFrame b) = if i = 𝔰.besselFrame b then 1 else 0 := by
    simp [g, besselFixer, Subgroup.mem_subgroupOf, Matrix.one_apply]
  have h_frame : frameMatrix x = 1 ↔ ∀ a b : Fin (𝔰.ϱ + 1),
      g (𝔰.besselFrame a) (𝔰.besselFrame b) = if a = b then 1 else 0 := by
    simp [g, ← ext_iff, frameMatrix, Matrix.one_apply]
  rw [besselU0, Subgroup.mem_inf, h_fixer, h_frame, and_congr_right_iff]
  refine fun hx ↦ ⟨fun h a b ↦ ?_, fun h i b ↦ ?_⟩
  · simpa [besselFrame_injective.eq_iff] using h (𝔰.besselFrame a) b
  cases i with
  | inl a => simpa [← besselFrame_castSucc, besselFrame_injective.eq_iff] using h (castSucc a) b
  | inr i =>
    have h_level : level (𝔰.besselFrame b) ≤ level (inr i : 𝔰.BesselIndex) :=
      (level_besselFrame b).trans_le (b.is_le.trans (le_level_inr i))
    simpa [g, Matrix.one_apply] using mem_besselU.1 hx _ _ h_level

/-- Let `T.G` be the unitary group of the split form `T.splitGram` on the basis e₁, …, e_ϱ, x_i
(i ∈ κ), z, e*₁, …, e*_ϱ, indexed by `𝔰.BesselIndex`. Let `x'` lie in the Bessel unipotent group
`T.besselU` of isometries that are block upper unitriangular for the levels, with identity middle
block. In the middle rows and the rows e*₁, …, e*_ϱ (the rows `inr i`), and in every column other
than those of e*₁, …, e*_ϱ (the indices `eStar a`), the entries of `x'` are those of the identity
matrix. -/
lemma apply_inr_of_mem_besselU (hx' : x' ∈ T.besselU) (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ)
    (j : 𝔰.BesselIndex) (hj : ∀ a : Fin 𝔰.ϱ, j ≠ eStar a) :
    (x' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) (inr i) j = if inr i = j then 1 else 0 := by
  have h_level : level j ≤ 𝔰.ϱ := by
    rcases j with a | c | a <;> simp_all [level]
  simpa [Matrix.one_apply] using mem_besselU.1 hx' (inr i) j (h_level.trans (le_level_inr i))

/-- Let `besselU` be the group of isometries of the split form `splitGram T` that are block upper
unitriangular. The form is taken on the basis e₁, …, e_ϱ, x_i, z, e*₁, …, e*_ϱ (`BesselIndex`), with
`T` its Gram matrix on X₀ ⊕ ⟨z⟩, where X₀ is spanned by the x_i (i ∈ κ). An element `x'` of
`besselU` is 1 if it fixes ϱ vectors (the columns of `B`) whose coordinates at e*₁, …, e*_ϱ (the
last block of rows, `B.toRows₂.toRows₂`) form the identity matrix. -/
lemma eq_one_of_mem_besselU_of_fix (hx' : x' ∈ T.besselU) {B : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) A}
    (h_fix : (x' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) * B = B)
    (hB : B.toRows₂.toRows₂ = 1) : x' = 1 := by
  -- The rows `inr i` of `x'` are those of `1`, by `apply_inr_of_mem_besselU` and, in the columns
  -- `eStar b`, by `h_fix` and `hB`. The isometry equation in the row `eStar a` then gives the row
  -- `inl a` outside these columns, and `h_fix` gives the remaining entries.
  set g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := ↑x'
  have hB_star (a b : Fin 𝔰.ϱ) : B (eStar a) b = if a = b then 1 else 0 := congrFun₂ hB a b
  have h_row (i : 𝔰.BesselIndex)
      (hi : ∀ j : 𝔰.BesselIndex, (∀ a : Fin 𝔰.ϱ, j ≠ eStar a) → g i j = if i = j then 1 else 0)
      (j : 𝔰.BesselIndex) : g i j = if i = j then 1 else 0 := by
    by_cases! hj : ∀ a : Fin 𝔰.ϱ, j ≠ eStar a
    · exact hi j hj
    obtain ⟨b, rfl⟩ := hj
    have h_zero : (g - 1) * B = 0 := by simp [Matrix.sub_mul, h_fix]
    simpa [Matrix.mul_apply, Matrix.one_apply, hi, hB_star, sub_eq_zero] using congrFun₂ h_zero i b
  have h_inr (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (j : 𝔰.BesselIndex) :
      g (inr i) j = if inr i = j then 1 else 0 :=
    h_row (inr i) (apply_inr_of_mem_besselU hx' i) j
  have h_inl (a : Fin 𝔰.ϱ) (j : 𝔰.BesselIndex) : g (inl a) j = if inl a = j then 1 else 0 := by
    refine h_row (inl a) (fun l hl ↦ ?_) j
    have h_isometry : (gᴴ * T.splitGram * g) (eStar a) l = T.splitGram (eStar a) l :=
      congrFun₂ (mem_unitaryGroupOf_iff.1 x'.property) (eStar a) l
    obtain b | c | b := l
    case inr.inr => exact absurd rfl (hl b)
    all_goals
      simpa [splitGram, Matrix.mul_apply, Matrix.one_apply, apply_ite star, h_inr] using h_isometry
  refine Subtype.ext (Units.ext ?_)
  ext (a | i) j
  exacts [h_inl a j, h_inr i j]

/-- An element `x'` of the block unitriangular group `New.Shape.Form.besselU` maps the frame
(e₁, …, e_ϱ, z) into its span. So the frame columns of `M * x'` are those of `M` times
`frameMatrix x'`, the submatrix of `x'` on the frame. The rows of `M` are indexed by an arbitrary
type `m`, and `e : n → m` selects any family of them. -/
lemma submatrix_mul_besselFrame {m n : Type*} (hx' : x' ∈ T.besselU)
    (M : Matrix m 𝔰.BesselIndex A) (e : n → m) :
    (M * (x' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)).submatrix e 𝔰.besselFrame =
      M.submatrix e 𝔰.besselFrame * frameMatrix x' := by
  -- The rows `inr i` of `x'` vanish in the frame columns, except for a `1` at `𝔰.z`.
  ext i b
  induction b using lastCases <;>
    simp [sum_univ_castSucc, apply_inr_of_mem_besselU hx', Matrix.mul_apply, frameMatrix]

/-- The submatrix on the frame (e₁, …, e_ϱ, z) is multiplicative when the right factor lies in the
block unitriangular group `New.Shape.Form.besselU`. -/
lemma frameMatrix_mul (hx' : x' ∈ T.besselU) :
    frameMatrix (x * x') = frameMatrix x * frameMatrix x' := by
  simpa [frameMatrix] using
    submatrix_mul_besselFrame hx' (x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) 𝔰.besselFrame

/-- Let `Z(γ) = T.frameGram γ` be the matrix of the products `h(f_j, γ f_l)` for the frame
`f = (e₁, …, e_ϱ, z)` and the split form `h` with middle block `T`, whose unitary group is `T.G`.
Suppose `x`, `x'` lie in the Bessel unipotent group `T.besselU`, the isometries that are block upper
unitriangular with identity middle block. If `m = frameMatrix x` and `m' = frameMatrix x'` are their
submatrices on the frame, then `Z(x'⁻¹ γ x) = m'ᴴ Z(γ) m`. -/
lemma frameGram_inv_mul_mul (hx' : x' ∈ T.besselU) (hx : x ∈ T.besselU) :
    T.frameGram (x'⁻¹ * γ * x).val = (frameMatrix x')ᴴ * T.frameGram γ * frameMatrix x := by
  -- With `J = T.splitGram` we have `J x'⁻¹ = x'ᴴ J`. The factor `x` splits off on the right by
  -- `submatrix_mul_besselFrame`, and `x'ᴴ` on the left by its conjugate transpose.
  let c : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := γ
  have h_left : ((x' : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)ᴴ * T.splitGram * c).submatrix
      𝔰.besselFrame 𝔰.besselFrame = (frameMatrix x')ᴴ * T.frameGram γ := by
    simpa [c, ← mul_assoc, frameGram] using
      congrArg conjTranspose (submatrix_mul_besselFrame hx' (T.splitGram * c)ᴴ 𝔰.besselFrame)
  rw [← h_left, ← submatrix_mul_besselFrame hx, ← U.form_mul_inv_eq]
  simp [c, frameGram, mul_assoc]

end FrameAction

end New

/-!
## Eichler isometries and leading minors of the frame matrix

Eichler maps in the unitary group `New.U J`, and the matrix `Z(γ) = T.frameGram γ` of the products
of the frame with its image under `γ`.

* `New.Filling.frameGram_inv`: `Z(γ⁻¹) = Z(γ)ᴴ` when the split form is hermitian and invertible.
-/

section EichlerMaps

open Matrix Fintype Fin

namespace New

variable {A : Type*} [CommRing A] [StarRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of the Eichler map v ↦ v + h(u, v)x − h(x, v)(u + ςx), where h is the form of J.

A variant of the standard Eichler transformation of a hermitian form, without the usual conditions
on x, u, ς that make it an isometry. -/
noncomputable def eichlerMap (J : Matrix n n A) (x : n → A) (u : n → A) (ς : A) : Matrix n n A :=
  1 + vecMulVec x (star u ᵥ* J) - vecMulVec (u + ς • x) (star x ᵥ* J)

lemma eichlerMap_mulVec {J : Matrix n n A} {x u : n → A} {ς : A} (v : n → A) :
    eichlerMap J x u ς *ᵥ v = v + (star u ⬝ᵥ J *ᵥ v) • x - (star x ⬝ᵥ J *ᵥ v) • (u + ς • x) := by
  simp [eichlerMap, sub_mulVec, add_mulVec, vecMulVec_mulVec, dotProduct_mulVec]

/-- Let `J` be hermitian, with form h(v, w) = vᴴ J w. Suppose `x` is isotropic for h, `u` is
orthogonal to `x`, and `ς + star ς = h(u, u)`. Then the Eichler map `New.eichlerMap J x u ς` is the
matrix of an element of the unitary group `New.U J`. -/
lemma exists_unitary_eq_eichlerMap {J : Matrix n n A} {x u : n → A} {ς : A} (hJ : Jᴴ = J)
    (hxx : star x ⬝ᵥ J *ᵥ x = 0) (hux : star u ⬝ᵥ J *ᵥ x = 0)
    (hς : ς + star ς = star u ⬝ᵥ J *ᵥ u) :
    ∃ e : U J, e = eichlerMap J x u ς := by
  -- The Eichler map `e'` of `-u` and `star ς` is both the inverse of `e` and its adjoint for the
  -- form of `J`. Each matrix identity is applied to a vector and expanded.
  set e : Matrix n n A := eichlerMap J x u ς with he
  set e' : Matrix n n A := eichlerMap J x (-u) (star ς) with he'
  have hxu : star x ⬝ᵥ J *ᵥ u = 0 := by rw [← star_dotProduct_mulVec_comm hJ, hux, star_zero]
  have mul_inv : e * e' = 1 := by
    refine ext_iff_mulVec.2 fun v ↦ ?_
    simp only [he, he', ← mulVec_mulVec, one_mulVec, eichlerMap_mulVec, mulVec_add, mulVec_sub,
      mulVec_smul, mulVec_neg,
      star_neg, neg_dotProduct, hxx, hux, hxu, ← hς]
    module
  have inv_mul : e' * e = 1 := mul_eq_one_comm.1 mul_inv
  have adjoint : eᴴ * J = J * e' := by
    refine ext_iff_mulVec.2 fun v ↦ ?_
    simp only [he, he', eichlerMap, conjTranspose_sub, conjTranspose_add, conjTranspose_one,
      conjTranspose_vecMulVec, star_vecMul, hJ, star_star, star_add, star_smul, star_neg,
      ← mulVec_mulVec, sub_mulVec, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      ← dotProduct_mulVec, add_dotProduct, smul_dotProduct, neg_dotProduct, smul_eq_mul,
      mulVec_sub, mulVec_add, mulVec_neg, mulVec_smul]
    module
  exact ⟨⟨⟨e, e', mul_inv, inv_mul⟩,
    mem_unitaryGroupOf_iff.2 <| show eᴴ * J * e = J by rw [adjoint, mul_assoc, inv_mul, mul_one]⟩,
    rfl⟩

variable {𝔰 : Shape} {T : 𝔰.Form A} {γ : T.G}

/-- The matrix `T.frameGram γ` is `fᴴ J (γ f)`, where `J = T.splitGram` and `frameImage γ` consists
of the columns of `γ` at the frame indices, so that `f = frameImage 1` is the frame itself. -/
lemma Filling.frameGram_eq_frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) :
    T.frameGram γ =
      (frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A))ᴴ * (T.splitGram * frameImage γ) := by
  ext i j
  simp [frameGram, Matrix.mul_apply, Matrix.one_apply]

/-- If the split form `T.splitGram` is hermitian and invertible, then `Z(γ⁻¹) = Z(γ)ᴴ` for unitary
`γ`, where `Z(γ) = T.frameGram γ` is the matrix of the products `h(f_j, γ f_l)`. -/
@[simp]
lemma Filling.frameGram_inv [h : Floors.IsHermitianUnit T.splitGram] :
    T.frameGram ↑γ⁻¹ = (T.frameGram γ)ᴴ := by
  -- `J γ⁻¹ = γᴴ J` for unitary `γ`, and `J` is hermitian.
  simp [h.conjTranspose_eq, ← U.form_mul_inv_eq, frameGram]

omit [StarRing A] in
/-- Cramer's rule for the last basis vector: for an `(m + 1) × (m + 1)` matrix `Z` over a
commutative ring, some `y` has `Z y = det Z` times the last basis vector, and the last coordinate
of `y` is the leading `m × m` minor of `Z`. -/
lemma exists_mulVec_eq_single_det {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) A) :
    ∃ y : Fin (m + 1) → A,
      Z *ᵥ y = Pi.single (last m) Z.det ∧ y (last m) = leadingMinor Z (last m).castSucc := by
  -- Take the last column of the adjugate; its last entry is the cofactor of the corner entry.
  refine ⟨Z.adjugate.col (last m), funext fun i ↦ ?_, ?_⟩
  · change (Z * Z.adjugate) i (last m) = (Pi.single (last m) Z.det : Fin (m + 1) → A) i
    simp [mul_adjugate, Matrix.one_apply, Pi.single_apply]
  · change Z.adjugate (last m) (last m) = (Z.submatrix castSucc castSucc).det
    simp [adjugate_fin_succ_eq_det_submatrix]

end New

end EichlerMaps
