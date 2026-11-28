module

import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.Unramified.Existence
import TauCeti.RingTheory.RootsOfUnity.LocalRing
public import Lib.Cohomology.Etale.Basic
public import Lib.General.NumberTheory.CoefficientRings
import Lib.ClassField.Places.TameInertia
import Lib.General.NumberTheory.PadicLimitsValuation
import Lib.PadicComparison.Descent.TestCategory

/-!
# Coefficient rings with a large residue field

Adjoining the roots of unity of order `ℓ ^ k - 1` to a finite extension of `ℚ_ℓ` multiplies the
degree by at most `k` and gives a residue field with at least `ℓ ^ k - 1` elements. The extension is
unramified, but this is not needed: the ramification index is at most the degree, which grows
linearly in `k`, while `ℓ ^ k` grows faster.

* `New.Selmer.frequently_lt_card_residueField`: beyond every coefficient ring there is one whose
  residue field is large compared with the ramification index.

Notions from other files:
* `New.CoeffRing ℓ`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, ordered
  by inclusion;
* `New.ThePrime ℓ`: the class saying that `ℓ` is prime.
-/

@[expose] public section

namespace New.Selmer

open IsDiscreteValuationRing IsLocalRing IntermediateField Module Polynomial

variable {ℓ : ℕ} [ThePrime ℓ]

/-- An element `x` of `ℚ̄_ℓ` of norm less than `1` and of degree `d` over `ℚ_ℓ` satisfies
`‖x‖ ^ d ≤ ‖ℓ‖`. -/
lemma norm_pow_natDegree_minpoly_le {x : PadicAlgCl ℓ} (hx : ‖x‖ < 1) :
    ‖x‖ ^ (minpoly ℚ_[ℓ] x).natDegree ≤ ‖(ℓ : PadicAlgCl ℓ)‖ := by
  -- `‖x‖ ^ d` is the norm of the constant coefficient, an element of `ℚ_ℓ` of norm less than `1`.
  have h_pos : (minpoly ℚ_[ℓ] x).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'
  have h_coeff : ‖x‖ ^ (minpoly ℚ_[ℓ] x).natDegree = ‖(minpoly ℚ_[ℓ] x).coeff 0‖ := by
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
      Real.rpow_inv_natCast_pow (norm_nonneg _) h_pos]
  have h_lt : ‖(minpoly ℚ_[ℓ] x).coeff 0‖ < (ℓ : ℝ) ^ (0 : ℤ) := by
    simpa [← h_coeff] using pow_lt_one₀ (norm_nonneg x) hx h_pos
  rw [h_coeff, ← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)), PadicAlgCl.norm_extends]
  simpa using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one _ 0).1 h_lt

/-- If a coefficient ring `O`, the ring of integers of a finite Galois extension of `ℚ_ℓ`, is
contained in a finite extension `K` of `ℚ_ℓ`, then its ramification index, the valuation of `ℓ`
in `O`, is at most the degree of `K`. -/
lemma addVal_ell_le_finrank (O : CoeffRing ℓ) (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] K] (hK : ∀ x ∈ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)), x ∈ K) :
    addVal O (ℓ : ↑O) ≤ finrank ℚ_[ℓ] K := by
  -- For a uniformiser `ϖ` of degree `d`, `ℓ` divides `ϖ ^ d`.
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  let d : ℕ := (minpoly ℚ_[ℓ] ϖ.val).natDegree
  have h_norm : ‖(ϖ : PadicAlgCl ℓ)‖ < 1 :=
    (O.norm_le_one ϖ).lt_of_ne (mt (O.isUnit_iff_norm_eq_one ϖ).2 hϖ.not_isUnit)
  have h_dvd : (ℓ : ↑O) ∣ ϖ ^ d := by
    simpa [O.dvd_iff_norm_le] using norm_pow_natDegree_minpoly_le h_norm
  have h_deg : d ≤ finrank ℚ_[ℓ] K := by
    simpa only [d,
      K.minpoly_eq] using minpoly.natDegree_le (A := ℚ_[ℓ]) (⟨ϖ.val, hK _ ϖ.property⟩ : K)
  calc addVal O (ℓ : ↑O) ≤ addVal O (ϖ ^ d) := addVal_le_iff_dvd.2 h_dvd
    _ = d := hϖ.addVal_pow _
    _ ≤ finrank ℚ_[ℓ] K := Nat.cast_le.2 h_deg

/-- An element `ζ` of `ℚ̄_ℓ` with `ζ ^ (ℓ ^ k - 1) = 1`, where `k ≠ 0`, has degree at most `k` over
`ℚ_ℓ`. -/
lemma natDegree_minpoly_le_of_pow_eq_one {k : ℕ} [NeZero k] {ζ : PadicAlgCl ℓ}
    (hζ : ζ ^ (ℓ ^ k - 1) = 1) : (minpoly ℚ_[ℓ] ζ).natDegree ≤ k := by
  -- The `(ℓ ^ k - 1)`-st roots of unity lie in the degree-`k` unramified extension.
  let U := TauCeti.unramifiedExtension ℚ_[ℓ] (PadicAlgCl ℓ) k
  have h_mem : ζ ∈ U := by
    change ζ ∈ TauCeti.unramifiedExtension ℚ_[ℓ] (PadicAlgCl ℓ) k
    rw [TauCeti.unramifiedExtension_eq_adjoin_setOf_pow_eq_one (NeZero.ne k)]
    exact subset_adjoin _ _ (by simpa [Padic.natCard_residueField] using hζ)
  have h_degree : finrank ℚ_[ℓ] U = k := TauCeti.finrank_unramifiedExtension (NeZero.ne k)
  have : FiniteDimensional ℚ_[ℓ] U := .of_finrank_pos (h_degree.symm ▸ NeZero.pos k)
  simpa only [U.minpoly_eq, h_degree] using minpoly.natDegree_le (A := ℚ_[ℓ]) (⟨ζ, h_mem⟩ : U)

/-- If a coefficient ring `O`, the ring of integers of a finite Galois extension of `ℚ_ℓ`, holds a
primitive `m`-th root of unity `ζ` of `ℚ̄_ℓ` and `m` is prime to `ℓ`, then the residue field of
`O` has at least `m` elements. -/
lemma le_card_residueField_of_isPrimitiveRoot {O : CoeffRing ℓ} {m : ℕ} (hm : ¬ℓ ∣ m) {ζ : ↑O}
    (hζ : IsPrimitiveRoot (ζ : PadicAlgCl ℓ) m) : m ≤ Nat.card (ResidueField O) := by
  have : Finite (ResidueField O) := Ring.HasFiniteQuotients.finiteQuotient (not_a_field O)
  have hm_unit : IsUnit (m : ↑O) := by
    have h : IsUnit (m : ℤ_[ℓ]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm))
    simpa only [map_natCast] using h.map (algebraMap ℤ_[ℓ] O)
  have hζO : IsPrimitiveRoot ζ m :=
    .of_map_of_injective (f := O.val.val) hζ Subtype.val_injective
  exact (hζO.map_residue hm_unit).eq_orderOf.le.trans orderOf_le_card

variable (ℓ) in
/-- For every natural number `a` there is a positive `k` with `a k + 1 < ℓ ^ k - 1`. -/
lemma exists_mul_add_one_lt_pow_sub_one (a : ℕ) : ∃ k : ℕ, 0 < k ∧ a * k + 1 < ℓ ^ k - 1 := by
  let j : ℕ := 2 * a + 1
  -- The exponent `2 j` works, as `(j + 1) ^ 2 ≤ ℓ ^ (2 j)`.
  refine ⟨j * 2, by positivity, Nat.lt_sub_of_add_lt ?_⟩
  calc a * (j * 2) + 1 + 1 < (j + 1) ^ 2 := by grind
    _ ≤ (ℓ ^ j) ^ 2 := Nat.pow_le_pow_left (Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt) 2
    _ = ℓ ^ (j * 2) := (pow_mul ℓ j 2).symm

variable (ℓ) in
/-- For every natural number `c` and every coefficient ring, that is, the ring of integers of a
finite Galois extension of `ℚ_ℓ`, there is a coefficient ring containing it whose residue field has
more than `c · e + 1` elements, where `e`, the valuation of `ℓ`, is the ramification index of the
containing ring. -/
lemma frequently_lt_card_residueField (c : ℕ) :
    ∃ᶠ O : CoeffRing ℓ in Filter.atTop,
      c * addVal O (ℓ : ↑O) + 1 < Nat.card (ResidueField O) := by
  -- Adjoin to the field `K₀`, of degree `d`, a primitive root of unity of order `ℓ ^ k - 1`, where
  -- `c d k + 2 < ℓ ^ k`.
  refine Filter.frequently_atTop.2 ?_
  rintro ⟨_, K₀, rfl⟩
  let d : ℕ := finrank ℚ_[ℓ] K₀
  obtain ⟨k, hk_pos, hk⟩ : ∃ k : ℕ, 0 < k ∧ c * (d * k) + 1 < ℓ ^ k - 1 := by
    simpa only [← mul_assoc] using exists_mul_add_one_lt_pow_sub_one ℓ (c * d)
  have : NeZero k := ⟨hk_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl ℓ) (ℓ ^ k - 1)
  have hζ_int : IsIntegral ℚ_[ℓ] ζ := Algebra.IsIntegral.isIntegral ζ
  have : IsCyclotomicExtension {ℓ ^ k - 1} ℚ_[ℓ] ℚ_[ℓ]⟮ζ⟯ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[ℓ]
  have : FiniteDimensional ℚ_[ℓ] ℚ_[ℓ]⟮ζ⟯ := adjoin.finiteDimensional hζ_int
  have : IsGalois ℚ_[ℓ] ℚ_[ℓ]⟮ζ⟯ := IsCyclotomicExtension.isGalois {ℓ ^ k - 1} _ _
  let K : FiniteGaloisIntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := ⟨K₀.toIntermediateField ⊔ ℚ_[ℓ]⟮ζ⟯⟩
  obtain ⟨O, hO⟩ : ∃ O : CoeffRing ℓ, ∀ x : PadicAlgCl ℓ,
      x ∈ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) ↔ ‖x‖ ≤ 1 ∧ x ∈ K.toIntermediateField :=
    ⟨⟨_, K, rfl⟩, fun x ↦ Iff.rfl⟩
  have hζ_mem : ζ ∈ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) := (hO ζ).2
    ⟨(hζ.isOfFinOrder (NeZero.ne _)).norm_eq_one.le,
      (le_sup_right : ℚ_[ℓ]⟮ζ⟯ ≤ K.toIntermediateField) (mem_adjoin_simple_self _ ζ)⟩
  have h_deg : finrank ℚ_[ℓ] K ≤ d * k :=
    (finrank_sup_le _ _).trans <| Nat.mul_le_mul_left d <|
      (adjoin.finrank hζ_int).trans_le (natDegree_minpoly_le_of_pow_eq_one hζ.pow_eq_one)
  refine ⟨O, ?_, ?_⟩
  · rintro x ⟨hx_norm, hx_mem⟩
    exact (hO x).2 ⟨hx_norm, (le_sup_left : K₀.toIntermediateField ≤ K.toIntermediateField) hx_mem⟩
  have h_addVal : addVal O (ℓ : ↑O) ≤ (d * k : ℕ) :=
    (addVal_ell_le_finrank O K.1 fun x hx ↦ ((hO x).1 hx).2).trans (Nat.cast_le.2 h_deg)
  calc c * addVal O (ℓ : ↑O) + 1 ≤ c * (d * k : ℕ) + 1 := by gcongr
    _ < (ℓ ^ k - 1 : ℕ) := by exact_mod_cast hk
    _ ≤ Nat.card (ResidueField O) := Nat.cast_le.2 <|
      le_card_residueField_of_isPrimitiveRoot not_dvd_pow_sub_one (ζ := ⟨ζ, hζ_mem⟩) hζ

end New.Selmer
