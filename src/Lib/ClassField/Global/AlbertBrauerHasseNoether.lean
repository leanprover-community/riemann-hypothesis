module

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.CategoryTheory.Shift.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.HasseNorm.Basic
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units
public import Lib.ClassField.HeckeL.EulerProduct
public import Lib.ClassField.Local.ArtinMap
import Lib.Adelic.Hecke.ClassSums
import Lib.ClassField.GaloisCohomology.TateIndexFormula
import Lib.ClassField.Global.ArtinMap
import Lib.ClassField.HeckeL.ContinuationAtOne
import Lib.General.NumberTheory.SUnitsAndClassNumber

/-!
# Real place symbols, the second inequality and Albert–Brauer–Hasse–Noether

Let `K` be a number field and let `Γ` act as the Galois group of `Ω/K`, where `Ω` (`New.Ω`) is the
algebraic closure of `ℚ`. The first section treats complex conjugations in `Γ` and the symbols of
totally positive elements of `K`. The second section proves the second inequality for a Galois
extension `L / K`; the proof compares Dirichlet densities of primes of degree one. In the last
section `L` is the field cut out by a character `χ` of `Γ`; it treats local norms and Artin symbols,
applies Tau Ceti's Hasse norm theorem in prime degree when the real places of `K` stay real in `L`,
and deduces the Albert–Brauer–Hasse–Noether theorem.

## Main definitions and results

* `New.IsTotallyPositive.exists_resH2_cyclicClass_eq_zero`: the symbol of a totally positive `x`
  restricts to zero on an open subgroup containing every complex conjugation.
* `New.second_inequality`: for `L / K` Galois, an open subgroup `W` of the finite ideles that
  contains the totally positive principal ideles and the norms from `L` has index at most `[L : K]`.
  Each of its cosets contains the uniformiser idele `ϖ_v` for infinitely many `v` of prime norm
  (`New.frequently_prime_uniformizer_div_mem_of_adeleNorm_mem`).
* `New.exists_hasPrimeDensity_addChar_uniformizer`: the values of a character `f` of the quotient by
  `W` at the `ϖ_v` have mean `1 - m` if `f` is trivial and `-m` otherwise, for some `m : ℕ`.
* `New.exists_localNorm_of_abelianLift_artinAt`: an element of a completion with trivial local
  symbol is a local norm.
* `New.albert_brauer_hasse_noether`: a class in H²(Γ, Ωˣ) is zero if it dies at every finite place
  and over a finite extension in which the real places stay real.

Notions from other files:
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K as its Galois group, with
  open stabilisers.
* `New.QZChar.abelianLift`: The homomorphism induced by the continuous character χ on the
  topological abelianisation of Γ, with values in ℚ/ℤ written multiplicatively.
* `New.artinAt`: The local Artin map K_v^× → Γ^ab: the Artin map to the abelianised decomposition
  group of the chosen place above v, followed by the map induced by inclusion.

## Relation to the literature

Known result: Global class field theory, comprising Albert–Brauer–Hasse–Noether, reciprocity,
existence and norms. Only finite ideles are used, with real places handled by total positivity, and
existence is proved only for totally complex fields. Reciprocity starts from cyclotomic characters
of prime conductor, with the auxiliary character chosen by B. H. Neumann's covering lemma. Source:
J. S. Milne, Class Field Theory (v4.03, 2020), VI 4.9, VII 4–9, VIII 4; Tate, Global class field
theory, in Cassels–Fröhlich 1967, ch. VII; H. Hasse, Die Struktur der R. Brauerschen
Algebrenklassengruppe, Math. Ann. 107 (1933) (reciprocity from the sum formula).

See also `Lib.ClassField.Places.LocalFields` and `Lib.ClassField.HeckeL.ContinuationAtOne`.
-/

@[expose] public section

/-!
## Symbols of totally positive elements at the real places

`New.IsComplexConj c` says that `c` acts as complex conjugation under some embedding of `Ω` in `ℂ`.
`New.cyclicClass _ χ w` is the class in `H²` of the cocycle `(g, h) ↦ carry (χ g) (χ h) • w`, which
stands for `δχ ∪ w`. For `w` coming from `x : Kˣ` with coefficients `Ωˣ`, it is the symbol `(χ, x)`.
-/

namespace New

open NumberField Complex DiscreteUnits Cohomology QZChar DiscreteModule ComplexEmbedding NeZero
  PadicInt Units

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K]

/-- In a totally complex field `K` every element `x` is totally positive (`New.IsTotallyPositive`:
`φ x > 0` for every ring homomorphism `φ : K →+* ℝ`), since there is no such `φ`. -/
lemma Cohomology.isTotallyPositive_of_isTotallyComplex [t : IsTotallyComplex K] (x : K) :
    IsTotallyPositive x := by
  intro φ
  -- There is no `φ : K →+* ℝ`: it would give a real embedding of `K` in `ℂ`.
  refine (t.complexEmbedding_not_isReal (ofRealHom.comp φ) ?_).elim
  ext
  simp

variable {c : Γ} [Algebra K Ω] [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω]

/-- Let `c` act on `Ω` as complex conjugation under the embedding `j : Ω →+* ℂ` (`hj`). Then `j`
restricted to `K` is a real embedding, since `c` fixes `K`. -/
lemma Cohomology.isReal_comp_algebraMap {j : Ω →+* ℂ} (hj : ∀ x : Ω, j (c • x) = star (j x)) :
    IsReal (j.comp (algebraMap K Ω)) := by
  ext
  simp [← hj, ← star_def]

variable (Γ) in
/-- If the field `K` has a real place `w`, some `c` in `Γ` acts on the field `Ω` (`New.Ω`,
the algebraic closure of `ℚ`) as complex conjugation (`New.IsComplexConj`: under some embedding
`j : Ω →+* ℂ`, `j (c • x)` is the complex conjugate of `j x`). -/
lemma exists_isComplexConj {w : InfinitePlace K} (hw : w.IsReal) :
    ∃ c : Γ, IsComplexConj c := by
  -- An extension `j` of the real embedding to `Ω` and its conjugate agree on `K`, so they differ
  -- by an element `c` of `Γ`.
  let j : Ω →+* ℂ := lift Ω w.embedding
  have h_agree : j.comp (algebraMap K Ω) = (star j).comp (algebraMap K Ω) := by aesop
  obtain ⟨c, hc⟩ := exists_apply_smul_eq_of_comp_algebraMap_eq Γ (K := K) j (star j) h_agree
  exact ⟨c, j, hc⟩

include G in
/-- A complex conjugation `c` (`hc`) is an involution, as `Γ` acts faithfully on `Ω`. -/
lemma IsComplexConj.mul_self (hc : IsComplexConj c) : c * c = 1 := by
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
  -- `c * c` acts on `Ω` as the identity: `j` turns it into conjugating twice.
  refine G.faithful.eq_of_smul_eq_smul fun x : Ω ↦ j.injective ?_
  simp [mul_smul, hj]

/-- For a character `χ` of `Γ` and a totally positive `x : Kˣ` there is an open subgroup `U` that
(a) contains every complex conjugation (the real places of `K` stay real in its fixed field)
and (b) on which the symbol `(χ, x) ∈ H²(Γ, Ωˣ)` restricts to zero. Here `Ω` is the field `New.Ω`,
the algebraic closure of `ℚ`, on which `Γ` acts as the Galois group over `K`. -/
lemma IsTotallyPositive.exists_resH2_cyclicClass_eq_zero {χ : ↥(QZChar Γ)} {x : Kˣ}
    (hx : IsTotallyPositive x.val) :
    ∃ U : OpenSubgroup Γ,
      (∀ c : Γ, IsComplexConj c → c ∈ U) ∧
      (unitsModule Γ).resH2 U
        (cyclicClass (unitsModule Γ).ρ χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x))) = 0 := by
  -- Take a square root `y` of `x` in `Ω`. The symbol `(χ, y ^ 2)` dies on the elements that fix
  -- `y` and lie in the kernel of `χ + χ`, and every complex conjugation is among them.
  obtain ⟨y, hy⟩ : ∃ y : DiscreteUnits Ω, 2 • y = (DiscreteUnits.ofBase Γ Ω (.ofMul x)).val :=
    exists_nsmul _ two_ne_zero
  let U : OpenSubgroup Γ := ⟨_, G.isOpen_stabilizer (y.toMul : Ω)⟩ ⊓ ⟨_, isOpen_ker (χ + χ)⟩
  have h_on_U (g : U.toSubgroup) : (unitsModule Γ).ρ g y = y ∧ 2 • χ.val g = 0 := by
    obtain ⟨hg_fix, hg_ker⟩ := g.property
    exact ⟨DiscreteUnits.ext hg_fix, (two_nsmul _).trans hg_ker⟩
  refine ⟨U, fun c hc ↦ ⟨?_, ?_⟩, resH2_cyclicClass_eq_zero hy h_on_U⟩
  · -- The square of `j y` is the value of `x` at a real embedding, which is positive; so `j y` is
    -- real and `c` fixes `y`.
    obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
    let φ : K →+* ℝ := (isReal_comp_algebraMap hj).embedding
    have h_sq : j (y.toMul : Ω) ^ 2 = φ x := by
      simpa [φ, toMul_nsmul, val_pow_eq_pow_val] using
        congrArg (fun z : DiscreteUnits Ω ↦ j (z.toMul : Ω)) hy
    have h_real : (j (y.toMul : Ω)).im = 0 := by simpa [← sq_nonneg_iff, h_sq] using (hx φ).le
    exact j.injective ((hj _).trans (conj_eq_iff_im.mpr h_real))
  · -- `χ c + χ c = χ (c * c) = 0`, as `c` is an involution.
    exact map_mul_eq_one (toHom χ) hc.mul_self

/-- A totally complex field `K` has no complex conjugation `c` (`hc`) in `Γ`: it would give a real
embedding of `K`. -/
lemma IsComplexConj.false_of_isTotallyComplex (hc : IsComplexConj c) [t : IsTotallyComplex K] :
    False := by
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
  exact t.complexEmbedding_not_isReal _ (isReal_comp_algebraMap hj)

omit [TopologicalSpace Γ] in
/-- A complex conjugation `c` (`hc`) inverts the `N`-th roots of unity: the cyclotomic character
mod `N` (`New.cyclotomicCharMod`) is `-1` at `c`. Here `Ω` is the field `New.Ω`, the algebraic
closure of `ℚ`. -/
lemma IsComplexConj.cyclotomicCharMod_eq_neg_one (hc : IsComplexConj c) {N : ℕ} [NeZero N] :
    cyclotomicCharMod Ω N c = -1 := by
  -- For an `N`-th root of unity `ζ`, both `c • ζ` and `ζ ^ (N - 1)` are inverse to `ζ`.
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : Ω, j (c • x) = star (j x) := hc
  have h_val : (New.cyclotomicCharMod Ω N c).val = (N - 1 : ℕ) := by
    refine cyclotomicCharMod_eq_iff.mpr fun ζ hζ ↦
      left_inv_eq_right_inv (a := ζ) (j.injective ?_) ?_
    · have h_norm : ‖j ζ‖ = 1 :=
        norm_eq_one_of_pow_eq_one (by simp [← map_pow, hζ]) (NeZero.ne N)
      simp [hj, conj_mul', h_norm]
    · rw [mul_pow_sub_one (NeZero.ne N), hζ]
  ext
  simp [h_val, NeZero.pos, ZMod.natCast_self]

omit [TopologicalSpace Γ] in
/-- The `l`-adic cyclotomic character `New.cyclotomicChar` is `-1` at a complex conjugation `c`
(`hc`). -/
lemma IsComplexConj.cyclotomicChar_eq_neg_one (hc : IsComplexConj c) (l : ℕ) [Fact (Nat.Prime l)] :
    cyclotomicChar Ω l c = -1 := by
  -- The value is `-1` modulo every `l ^ r`.
  refine ext (ext_of_toZModPow.mp fun r ↦ ?_)
  simpa [cyclotomicCharMod_prime_pow_eq, ← val_inj] using
    hc.cyclotomicCharMod_eq_neg_one (N := l ^ r)

end New

/-! ## The second inequality and equidistribution of primes in norm cosets -/

section SecondInequality

open Complex Module QuotientGroup Subgroup AddChar Finset DFunLike New

attribute [local instance low] Fintype.ofFinite

/-- Let ψ and finitely many c_i be homomorphisms from a monoid to ℂ, with ψ(x) = 1 whenever no
c_i(x) is −1. Then ψ times the product of some of the c_i is trivial. -/
lemma New.exists_mul_prod_eq_one {G ι : Type*} [Monoid G] [Fintype ι] (ψ : G →* ℂ) (c : ι → G →* ℂ)
    (h : ∀ x : G, (∀ i : ι, c i x ≠ -1) → ψ x = 1) :
    ∃ T : Finset ι, ψ * T.prod c = 1 := by
  classical
  -- The product `∏ i, (1 + c i x)` vanishes unless `ψ x = 1`, so multiplying it by `ψ x` changes
  -- nothing. Expanded over subsets `T`, this is a linear relation between characters; by their
  -- independence the trivial character, the term `T = ∅` on the left, occurs on the right too.
  by_contra! hne
  have h_expand (x : G) : ∑ T : Finset ι, (T.prod c) x = ∏ i, (1 + c i x) := by
    simp [← powerset_univ, ← prod_one_add]
  have hψ (x : G) : ∏ i, (1 + c i x) = ψ x * ∏ i, (1 + c i x) := by grind [prod_eq_zero_iff]
  have h_coeffs : ∑ T : Finset ι, Finsupp.single (T.prod c) (1 : ℂ) =
      ∑ T : Finset ι, Finsupp.single (ψ * T.prod c) 1 :=
    linearIndependent_monoidHom G ℂ (funext fun x ↦ by simpa [← mul_sum, ← h_expand] using hψ x)
  -- The coefficient of `1` is zero on the right; on the left it counts the `T` with product `1`.
  have h_prod_ne_one : ∀ ⦃T : Finset ι⦄, T.prod c ≠ 1 := by
    simpa [Finsupp.single_apply, hne] using DFunLike.congr_fun h_coeffs 1
  exact h_prod_ne_one prod_empty

variable {K : Type*}
  (L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  {W : Subgroup (𝔸f K)ˣ} (hW_open : W.IsOpen)
  (hW_pos : ∀ x : Kˣ, IsTotallyPositive x.val → principalIdele (x : Kˣ) ∈ W)

include hW_open hW_pos

/-- Let `W` be an open subgroup of the finite ideles (`hW_open`) containing the principal ideles of
the totally positive elements (`hW_pos`), and `f` a character of the quotient by `W`, written
additively (so `f = 0` is the trivial character). The mean of `f` at the uniformiser ideles
(`New.HasPrimeDensity`, Dirichlet density over the finite places) is `1 - m` if `f = 0` and `-m`
otherwise, for some natural number `m`. -/
lemma New.exists_hasPrimeDensity_addChar_uniformizer (f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ) :
    ∃ m : ℕ,
      HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
        ((if f = 0 then 1 else 0) - m) := by
  split_ifs with hf
  · -- The trivial character is `1` everywhere, with mean `1`.
    exact ⟨0, by simp_all [hasPrimeDensity_const]⟩
  let ψ : (𝔸f K)ˣ →* ℂ := f.toMonoidHom.comp (mk' W)
  have hW : W ≤ ψ.ker := le_comap_mk' W f.toMonoidHom.ker
  -- Let `Φ w` be the embedding into `ℂ` at the infinite place `w`. On `Kˣ`, `ψ` is trivial where no
  -- `Φ w x / |Φ w x|` is `-1`, so it is the inverse of a product of some of these characters: `ψ`
  -- is a Hecke character of a type with entries 0 and 1.
  let sgn (w : NumberField.InfinitePlace K) : Kˣ →* ℂ :=
    { toFun x := Φ w x.val / ‖Φ w x‖
      map_one' := by simp
      map_mul' := by simp [field] }
  have h_pos (x : Kˣ) (hx : ∀ w : NumberField.InfinitePlace K, sgn w x ≠ -1) :
      IsTotallyPositive x.val := by
    intro φ
    refine lt_of_not_ge fun h_neg ↦ hx (.mk (ofRealHom.comp φ)) ?_
    simp [sgn, Φ, abs_of_nonpos h_neg, IsSelfAdjoint, ext_iff]
  obtain ⟨T, hT⟩ :
      ∃ T : Finset (NumberField.InfinitePlace K), ψ.comp principalIdele * T.prod sgn = 1 :=
    exists_mul_prod_eq_one _ sgn fun x hx ↦ hW (hW_pos x (h_pos x hx))
  have h_hecke : IsHeckeOfType ψ.toHomUnits (piecewise T 1 0) := by
    -- The kernel of `ψ` contains the open subgroup `W`, and on `Kˣ` the product of `ψ` and the
    -- `sgn w` with `w ∈ T` is `1` (`hT`).
    refine ⟨by simpa [ψ.ker_toHomUnits] using isOpen_mono hW hW_open, ?_⟩
    simp_all [sgn, piecewise, ext_iff, Finset.univ_inter]
  have h_ne : ψ.toHomUnits ≠ 1 := by
    refine fun h_one ↦ hf (AddChar.ext _ _ (Quot.ind fun a ↦ ?_))
    exact congrArg Units.val (DFunLike.congr_fun h_one a)
  -- A non-trivial Hecke character has mean `-m` at the uniformisers, for some `m : ℕ`.
  obtain ⟨m, -, hm⟩ := h_hecke.exists_hasPrimeDensity_neg_natCast Set.finite_empty h_ne
  have hψ_apply (a : (𝔸f K)ˣ) : ψ a = f (Additive.ofMul ⟦a⟧) := rfl
  exact ⟨m, by simpa [heckeCoeff, hψ_apply] using hm⟩

omit hW_pos in
/-- Let `L / K` be Galois and `W` an open subgroup of finite index of the finite ideles of `K` that
contains the norms from `L` (`h_norm`). If each character `f` of the quotient by `W` has mean `d f`
at the uniformiser ideles, then the index of `W` is at most `Re (∑ f, [L : K] * d f)`. -/
private lemma index_re_le_sum_of_hasPrimeDensity [FiniteIndex W]
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W)
    (d : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ → ℂ)
    (hd : ∀ f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ,
      HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
        (d f)) :
    (W.index : ℂ).re ≤ (∑ f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ, (finrank K L : ℂ) * d f).re := by
  classical
  -- `D v`: the primes above `v` of the same norm; `#(D v)` has mean 1.
  let D (v : FinPlace K) : Set (FinPlace L) := {w : FinPlace L | w.below K = v ∧ w.q = v.q}
  -- The Galois group permutes the primes above `v` transitively, so there are at most `[L : K]`.
  have h_card (v : FinPlace K) : (D v).ncard ≤ finrank K L := by
    rcases (D v).eq_empty_or_nonempty with hD | ⟨w, rfl, -⟩
    · simp [hD]
    grw [← IsGalois.card_aut_eq_finrank,
      ← Finite.card_range_le fun g : Gal(L/K) ↦ w.comap (g : L →+* L)]
    exact Set.ncard_le_ncard fun u ⟨hu_below, _⟩ ↦ w.exists_gal_comap_eq hu_below.symm
  -- Write `ϖ_v = locIdele v (uniformizer v)` for the uniformiser idele at `v`. If `W` holds the
  -- units at `v` and `w ∈ D v`, then `ϖ_v` is the norm of `ϖ_w` up to a unit.
  have h_mem : ∀ᶠ v in .cofinite, (D v).Nonempty → locIdele v (uniformizer v) ∈ W := by
    filter_upwards [eventually_unramified (mk' W) (by simpa)] with v h_unit ⟨w, hw, hq⟩
    subst hw
    specialize h_unit (uniformizer _ / localNorm K w (uniformizer w))
    simp_all [v_localNorm (f := 1), ← adeleNorm_locIdele, (eq_one_iff _).mpr]
  -- For almost all `v`, `[W] * #(D v) ≤ [L : K] * ∑ f, f(ϖ_v)` with `[W]` the index: the sum is
  -- `[W]` if `ϖ_v ∈ W` and `0` otherwise. Compare the densities of the two sides.
  refine (hasPrimeDensity_card_degree_one L W.index).re_le_re (.sum (fun _ ↦ finrank K L) hd)
    (h_mem.mono fun v hv _ ↦ ?_)
  rcases (D v).eq_empty_or_nonempty with hD | hD
  · simp_all [D, ← mul_sum, sum_apply_eq_ite, apply_ite, mul_nonneg]
  · have h_mul : (W.index : ℝ) * (D v).ncard ≤ finrank K L * W.index := by grw [h_card, mul_comm]
    simpa [(eq_one_iff _).mpr (hv hD), index, mul_comm] using h_mul

/-- Let `L / K` be Galois and `W` an open subgroup of the finite ideles of `K` (`hW_open`) that
contains the totally positive principal ideles (`hW_pos`) and the norms from `L` (`h_norm`). A
character `f` of the quotient by `W` has mean `1` at the uniformiser ideles if it is trivial
(`f = 0`), and mean `0` otherwise. -/
private lemma hasPrimeDensity_addChar_uniformizer_of_adeleNorm_mem
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W)
    (f : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ) :
    HasPrimeDensity (fun v : FinPlace K ↦ f (Additive.ofMul ⟦locIdele v (uniformizer v)⟧))
      (if f = 0 then 1 else 0) := by
  classical
  have h_fin : FiniteIndex W := finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos
  -- The means are `1 - m g` or `-m g` with `m g : ℕ`, and the positive index is at most their sum
  -- times `[L : K]`, so every `m g` vanishes.
  choose m hm using exists_hasPrimeDensity_addChar_uniformizer (K := K) hW_open hW_pos
  have h_le : (W.index : ℂ).re ≤
      (∑ g, (finrank K L : ℂ) * ((if g = 0 then 1 else 0) - m g)).re :=
    index_re_le_sum_of_hasPrimeDensity L hW_open h_norm _ hm
  have h_pos : (0 : ℝ) < (∑ g, (finrank K L : ℂ) * ((if g = 0 then 1 else 0) - m g)).re :=
    (Nat.cast_pos.mpr Nat.card_pos).trans_le h_le
  have hm0 (g : AddChar (Additive ((𝔸f K)ˣ ⧸ W)) ℂ) : m g = 0 := by
    simp_all [← Nat.cast_sum, ← mul_sum, finrank_pos]
  simpa [hm0 f] using hm f

/-- Let `L / K` be Galois and `W` an open subgroup of the finite ideles of `K` (`hW_open`) that
contains the totally positive principal ideles (`hW_pos`) and the norms from `L` (`h_norm`). Then
the index of `W` is at most `[L : K]`. -/
private lemma index_le_finrank_of_adeleNorm_mem
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W) :
    W.index ≤ finrank K L := by
  have h_fin : FiniteIndex W := finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos
  simpa using index_re_le_sum_of_hasPrimeDensity L hW_open h_norm _
    (hasPrimeDensity_addChar_uniformizer_of_adeleNorm_mem L hW_open hW_pos h_norm)

/-- Let `L / K` be Galois and `W` an open subgroup of the finite ideles of `K` (`hW_open`) that
contains the totally positive principal ideles (`hW_pos`) and the norms from `L` (`h_norm`). Then
every coset `a W` contains the uniformiser ideles of infinitely many primes `v` of prime norm
`v.q`. -/
lemma New.frequently_prime_uniformizer_div_mem_of_adeleNorm_mem
    (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W) (a : (𝔸f K)ˣ) :
    ∃ᶠ v : FinPlace K in Filter.cofinite, v.q.Prime ∧ locIdele v (uniformizer v) / a ∈ W := by
  classical
  have h_fin : FiniteIndex W := finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos
  -- With `ϖ_v` the uniformiser idele at `v`, `∑ f, f(ϖ_v / a)` has mean 1. If the claim failed,
  -- this sum would vanish for almost all `v` of prime norm, so its mean would be 0.
  intro h_not
  refine ((HasPrimeDensity.sum (fun f ↦ f (.ofMul a⁻¹))
      (hasPrimeDensity_addChar_uniformizer_of_adeleNorm_mem L hW_open hW_pos h_norm)).re_le_re
      (hasPrimeDensity_const 0) (h_not.mono ?_)).not_gt (by simp)
  simp +contextual [← map_add_eq_mul, sum_apply_eq_ite, neg_add_eq_sub, eq_iff_div_mem, sub_eq_zero]

/-- The second inequality of class field theory, with equidistribution. Let `L / K` be Galois and
`W` an open subgroup of the finite ideles of `K` (`hW_open`) containing the principal ideles of the
totally positive elements (`hW_pos`) and the norms of finite ideles of `L` (`h_norm`). Then (a)
`W` has finite index at most `[L : K]`, and (b) each coset `a W` contains the uniformiser ideles of
infinitely many primes of prime norm: `frequently_prime_uniformizer_div_mem_of_adeleNorm_mem`. -/
lemma New.second_inequality (h_norm : ∀ y : (𝔸f L)ˣ, Units.map (adeleNorm K L) y ∈ W) :
    FiniteIndex W ∧
    W.index ≤ finrank K L ∧
    ∀ a : (𝔸f K)ˣ, ∃ᶠ v : FinPlace K in Filter.cofinite,
      v.q.Prime ∧ locIdele v (uniformizer v) / a ∈ W :=
  ⟨finiteIndex_idele_subgroup_of_isOpen W hW_open hW_pos,
    index_le_finrank_of_adeleNorm_mem L hW_open hW_pos h_norm,
    frequently_prime_uniformizer_div_mem_of_adeleNorm_mem L hW_open hW_pos h_norm⟩

end SecondInequality

/-!
## Albert–Brauer–Hasse–Noether with a stronger hypothesis at real places

Γ is the Galois group of an algebraic closure Ω of a number field K, and χ is a character of Γ
(`New.QZChar`). L is the field cut out by χ, that is, the fixed field of its kernel. The local
symbol of x at v is `New.QZChar.abelianLift χ (New.artinAt Γ v x)`, and `New.adeleNorm` is the
adelic norm.
-/

namespace New

open Ideal NumberField Cohomology Units NeZero Algebra QZChar

variable {Γ K L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra K L]

/-- The adelic norm `New.adeleNorm K L` takes the principal idele of `x` in `Lˣ` to the principal
idele of the norm of `x`. -/
@[local simp]
lemma map_adeleNorm_principalIdele (x : Lˣ) :
    (principalIdele x).map (adeleNorm K L) = principalIdele (x.map (Algebra.norm K)) := by
  aesop

/-- For a finite adele `y` of `L` and a finite place `v` of `K`, the `v`-component of the adelic
norm of `y` is a limit, in the completion of `K` at `v`, of norms of elements of `L`. -/
lemma adeleNorm_mem_closure {y : 𝔸f L} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} :
    adeleNorm K L y v ∈
      closure (Set.range fun x : L ↦ algebraMap K (v.adicCompletion K) (Algebra.norm K x)) := by
  -- `y ↦ adeleNorm K L y v` is continuous, `L` is dense in the finite adeles, and on `L` it is the
  -- norm.
  have h_cont : Continuous fun y ↦ adeleNorm K L y v := (continuous_evalAt v).comp (by fun_prop)
  have h_on_L (x : L) : adeleNorm K L (algebraMap L (𝔸f L) x) v =
      algebraMap K (v.adicCompletion K) (Algebra.norm K x) := by aesop
  exact map_mem_closure h_cont (denseRange_algebraMap_finAdele y)
    (Set.mapsTo_range_iff.mpr fun x ↦ ⟨x, (h_on_L x).symm⟩)

variable [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] [Algebra L Ω]
  [IsScalarTower K L Ω] {χ : QZChar Γ} [IsProGalois (ker χ) L Ω]

/-- Let the continuous character χ : Γ → ℚ/ℤ cut out the finite extension L of K, and let K_v be the
completion of K at the finite place v. If a unit u of K_v is a limit in K_v of norms from L to K,
then χ vanishes on the local Artin symbol `artinAt Γ v u`. When `u` is a component of the adelic
norm of a finite idele of L, the hypothesis is `adeleNorm_mem_closure`. -/
lemma abelianLift_artinAt_eq_one_of_mem_closure {v : FinPlace K} {u : (v.adicCompletion K)ˣ}
    (hu : u.val ∈
      closure (Set.range fun x : L ↦ algebraMap K (v.adicCompletion K) (Algebra.norm K x))) :
    abelianLift χ (artinAt Γ v u) = 1 := by
  -- The kernel of `abelianLift χ ∘ artinAt Γ v` is closed, since the target is discrete, and it
  -- contains the norms, whose global symbol `(χ, x)` is zero.
  have h_closed : IsClosed {w : (v.adicCompletion K)ˣ | abelianLift χ (artinAt Γ v w) = 1} :=
    (isClosed_discrete {1}).preimage
      ((continuous_abelianLift χ).comp (continuous_hom_locField_units _))
  refine closure_minimal ?_ h_closed (isOpenMap_val.preimage_closure_subset_closure_preimage hu)
  rintro w ⟨z, hz⟩
  have hz_ne : z ≠ 0 := fun h_zero ↦ by simpa [h_zero] using hz.symm
  let x : Kˣ := .map (norm K) (.mk0 z hz_ne)
  have hw : ideleAt v (principalIdele x) = w := ext hz
  rw [← hw, Set.mem_ofPred, v.isPlaceOver_placeOver.abelianLift_artinAt_eq_one_iff,
    (cyclicClass_eq_zero_iff_norm (L := L) x).mpr ⟨.mk0 z hz_ne, rfl⟩, map_zero]

/-- The character χ kills the Artin symbol of the norm of every finite idele of the field L that it
cuts out. -/
@[simp]
lemma abelianLift_artinMap_adeleNorm (y : (𝔸f L)ˣ) :
    abelianLift χ (artinMap Γ (Units.map (adeleNorm K L) y)) = 1 := by
  rw [abelianLift_artinMap_eq_finprod, finprod_eq_one_of_forall_eq_one fun _ ↦
    abelianLift_artinAt_eq_one_of_mem_closure adeleNorm_mem_closure]

/-- The kernel of the local symbol consists of local norms. Let L be the field cut out by χ, let w
be a finite place of L over the place v = `w.below K` of K, and let x be a unit of the completion
K_v of K at v with `χ (artinAt Γ v x)` trivial. Then there is a unit y of the completion
`LocField w` of L at w whose local norm to K_v is x. -/
lemma exists_localNorm_of_abelianLift_artinAt {w : FinPlace L} {x : (LocField (w.below K))ˣ}
    (hx : abelianLift χ (artinAt Γ (w.below K) x) = 1) :
    ∃ y : (LocField w)ˣ, localNorm K w y = x := by
  rw [w.isPlaceOver_placeOver.isPlaceOver_below.abelianLift_artinAt] at hx
  -- Inside the decomposition group, `χ` kills exactly the elements that come from `Gal(Ω/L)`.
  have h_ker (g : decompGroup Γ (placeOver w)) :
      (χ : Γ → QZ) g = 0 ↔ ∃ g' : decompGroup (ker χ) (placeOver w), (ker χ).subtype g' = g := by
    aesop
  exact (w.isPlaceOver_placeOver.isNormCompatible (ker χ).subtype 1 (fun _ _ ↦ rfl)
    (IsScalarTower.algebraMap_apply K L Ω)).exists_localNorm_eq
    (χ := QZChar.comap (subgroupIncl _) χ) h_ker hx

open InfinitePlace Subgroup Finset Nat SUnit DiscreteModule MulSemiringAction Function

/-- Let f : E → G be a homomorphism to a commutative group, J, N subgroups of G with f(E)·J = G,
and U = f⁻¹J. Then [G : f(E)(N ∩ J)] · [U : U ∩ f⁻¹N] = [J : J ∩ N]. -/
lemma relIndex_mul_index_sup {E G : Type*} [Group E] [CommGroup G] {f : E →* G} {J N : Subgroup G}
    {U : Subgroup E} (h_top : f.range ⊔ J = ⊤) (h_mem : ∀ {x : E}, f x ∈ J ↔ x ∈ U) :
    (N.comap f).relIndex U * (f.range ⊔ N ⊓ J).index = N.relIndex J := by
  -- The tower formula for the subgroups `N ⊓ J ≤ (N ⊓ J ⊔ f.range) ⊓ J ≤ J`; its two steps
  -- are the two factors on the left.
  obtain rfl : J.comap f = U := Subgroup.ext fun _ ↦ h_mem
  -- Upper step: joining `J` to `N ⊓ J ⊔ f.range` gives all of `G`.
  have h_relIndex_upper : (N ⊓ J ⊔ f.range).relIndex J = (f.range ⊔ N ⊓ J).index := by
    rw [← relIndex_sup_left J, sup_comm (N ⊓ J), sup_assoc, sup_of_le_right (inf_le_right (a := N)),
      h_top, relIndex_top_right]
  -- Lower step: by the modular law the middle group is `N ⊓ J ⊔ f.range ⊓ J`, and
  -- `f.range ⊓ J` is the image of `U`.
  have h_relIndex_lower :
      (N ⊓ J).relIndex ((N ⊓ J ⊔ f.range) ⊓ J) = (N.comap f).relIndex (J.comap f) := by
    rw [sup_inf_assoc_of_le _ inf_le_right, relIndex_sup_left, ← map_comap_eq, ← relIndex_comap,
      N.comap_inf, inf_relIndex_right]
  rw [← h_relIndex_upper, ← h_relIndex_lower, relIndex_inf_mul_relIndex,
    inf_of_le_left le_sup_left, inf_relIndex_right]

omit [NumberField K] [NumberField L] in
/-- If `χ` kills all complex conjugations, the real places stay real in the field `L` it cuts out:
`L / K` is unramified at the infinite places. -/
lemma isUnramifiedAtInfinitePlaces_of_mem_ker (hc : ∀ c : Γ, IsComplexConj c → c ∈ ker χ) :
    IsUnramifiedAtInfinitePlaces K L := by
  refine ⟨(comap_surjective (K := Ω)).forall.mpr ?_⟩
  rintro ⟨_, j, rfl⟩
  refine isUnramified_iff.mpr ((isReal_or_isComplex _).imp_left fun h_real ↦ ?_)
  -- If `j` is real on `K`, it differs from its conjugate by a complex conjugation `g` fixing `L`.
  replace h_real : (InfinitePlace.mk (j.comp (algebraMap K Ω))).IsReal := by
    rwa [IsScalarTower.algebraMap_eq K L Ω]
  obtain ⟨g, hg⟩ : ∃ g : Γ, ∀ x : Ω, j (g • x) = star j x :=
    exists_apply_smul_eq_of_comp_algebraMap_eq Γ j (star j) (isReal_mk_iff.mp h_real).symm
  exact ⟨_, isReal_comp_algebraMap (c := (⟨g, hc g ⟨j, hg⟩⟩ : ker χ)) hg, rfl⟩

open scoped AdicCompletionExtension in
attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver in
open TauCeti TauCeti.GlobalNumberFields in
/-- Hasse's norm theorem in prime degree. Let `L / K` be Galois of prime degree, cut out by `χ`, and
let `χ` kill every complex conjugation. If `x` in `Kˣ` has trivial local symbol
`χ (artinAt Γ v x)` at every finite place `v` of `K`, then `x` is the norm of some `z` in
`Lˣ`. -/
lemma exists_map_norm_eq_of_abelianLift_artinAt_eq_one [IsGalois K L]
    (hl : (Module.finrank K L).Prime) (hc : ∀ c : Γ, IsComplexConj c → c ∈ ker χ) {x : Kˣ}
    (hx : ∀ v : FinPlace K, abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1) :
    ∃ z : Lˣ, z.map (Algebra.norm K) = x := by
  classical
  have : Fact (Module.finrank K L).Prime := ⟨hl⟩
  have : IsCyclic Gal(L/K) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
  have h_norm : x ∈ normGroup K L := by
    apply (TauCeti.ClassFieldTheory.isGlobalNorm_iff_isLocalNormEverywhere K L x).2
    rw [isLocalNormEverywhere_def]
    constructor
    · intro v
      rw [isFiniteLocalNorm_iff]
      obtain ⟨w, rfl⟩ := FinPlace.comap_surjective (algebraMap K L) v
      obtain ⟨y, hy⟩ := exists_localNorm_of_abelianLift_artinAt (χ := χ) (hx (w.below K))
      let u := w.below K
      -- The two completion algebra structures agree because both extend the same field map.
      let P (a : Algebra (LocField u) (LocField w)) : Prop :=
        letI := a
        localNorm K w y = y.map (Algebra.norm (LocField u))
      have h_local : P ((locMap (algebraMap K L) (rfl : w.comap (algebraMap K L) = u)).toAlgebra) :=
        (IsPlaceOver.finite_and_localNorm_eq_norm K w).2 y
      have h_alg : (locMap (algebraMap K L) (rfl : w.comap (algebraMap K L) = u)).toAlgebra =
          IsDedekindDomain.HeightOneSpectrum.adicCompletionExtensionAlgebra K L u w := by
        refine Algebra.algebra_ext _ _ fun z ↦ ?_
        rw [RingHom.algebraMap_toAlgebra,
          IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
        exact RingHom.congr_fun
          (IsDedekindDomain.HeightOneSpectrum.eq_adicCompletionExtension_of_continuous K L u w
            (continuous_locMap _ _) (fun a ↦ locMap_algebraMap _ _ a)) z
      rw [h_alg] at h_local
      change localNorm K w y = y.map (Algebra.norm (LocField u)) at h_local
      -- Use the local norm witness at `w` and the identity at all other places over `u`.
      let t : {w : FinPlace L // w.asIdeal.LiesOver u.asIdeal} := ⟨w, inferInstance⟩
      refine ⟨Pi.mulSingle t y, ?_⟩
      rw [finprod_eq_single _ t fun w' hw' ↦ by simp [Pi.mulSingle_eq_of_ne hw'],
        Pi.mulSingle_eq_same]
      exact Units.ext ((Algebra.coe_normUnits _ _).trans
        (congrArg Units.val (h_local.symm.trans hy)))
    · intro v
      -- No real place becomes complex, so the norm at a place above `v` is surjective.
      rw [isInfiniteLocalNorm_def]
      obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
      have : w.LiesOver v := hw ▸ inferInstance
      have h_unram := isUnramifiedAtInfinitePlaces_of_mem_ker (L := L) hc
      exact TauCeti.mem_range_normUnits_completion_of_finrank_eq_one K L v
        ⟨⟨w, inferInstance⟩, (h_unram.isUnramified w).finrank_eq_one v⟩ _
  obtain ⟨z, hz⟩ := mem_normGroup_iff.1 h_norm
  exact ⟨z, Units.ext hz⟩

/-- Albert–Brauer–Hasse–Noether. Let α be a class in H²(Γ, Ωˣ), where Γ acts as the Galois group of
`New.Ω` (the algebraic closure of ℚ) over the number field K. If α restricts to zero on the
decomposition group of every place of Ω over a finite place of K (`h_dec`) and on an open subgroup
U of Γ containing all complex conjugations (`h_conj`, `h_res`: over an extension in which the real
places stay real), then α = 0. -/
lemma albert_brauer_hasse_noether (α : (unitsModule Γ).H2)
    (h_dec : ∀ {A : ClosurePlace} {v : FinPlace K}, IsPlaceOver A v →
      (unitsModule Γ).resH2 (decompGroup Γ A) α = 0)
    (U : OpenSubgroup Γ) (h_conj : ∀ g : Γ, IsComplexConj g → g ∈ U)
    (h_res : (unitsModule Γ).resH2 U α = 0) :
    α = 0 := by
  -- Reduce to the case where `U` is normal of prime index.
  wlog hU : U.Normal ∧ U.index.Prime with h_step
  · -- `α` dies on the normal core `W` of `U`; climb to `Γ` in steps `V ≤ U'` of prime index
    -- (`mem_of_prime_step`), applying the reduced case over the fixed field of `U'`.
    have h_finiteIndex : U.toSubgroup.FiniteIndex := U.finiteIndex_of_finite_quotient
    let W : OpenSubgroup Γ :=
      ⟨U.normalCore, isOpen_of_isClosed_of_finiteIndex _ (normalCore_isClosed _ U.isClosed)⟩
    -- Restriction to `W` factors through restriction to `U`.
    have h_factor : (unitsModule Γ).resH2 W α =
        (pairMapH2 (.mk (inclusion U.normalCore_le) (continuous_subtypeVal.subtype_mk _)) .id)
          ((unitsModule Γ).resH2 U α) := by
      induction α using QuotientAddGroup.induction_on
      rfl
    have hW : (unitsModule Γ).resH2 W α = 0 := by rw [h_factor, h_res, map_zero]
    refine mem_of_prime_step ⊥ hW fun U' V hV _ h_le h_index s hs h_resV ↦ ⟨s, hs, ?_⟩
    obtain rfl : s = 0 := hs
    rw [sub_zero] at h_resV ⊢
    refine h_step ((unitsModule Γ).resH2 U' α) ?_ V ?_ h_resV ⟨hV, h_index⟩
    · -- `α` dies on the decomposition group in `Γ`, so on its intersection with `U'`, which is the
      -- decomposition group in `U'`.
      intro A v hA
      refine resH2_subgroupOf_eq_zero_symm (M := unitsModule Γ) (U := U') (V := decompGroup Γ A) ?_
      rw [h_dec hA.isPlaceOver_below, map_zero]
    · -- The conjugates of a complex conjugation are complex conjugations, so lie in `U`.
      rintro g ⟨j, hj⟩
      refine h_le fun b ↦ h_conj _ ⟨j.comp (toRingHom _ _ b⁻¹), fun x ↦ ?_⟩
      -- `b⁻¹ • (b g b⁻¹) • x = g • (b⁻¹ • x)`, so this is `hj` at `b⁻¹ • x`.
      simpa [mul_smul, Subgroup.smul_def] using hj (b⁻¹ • x)
  -- Now `U` is the kernel of a character `χ`, so `α` is a symbol `(χ, x)` (`cyclicClass_spec`). The
  -- local symbols of `x` are trivial, so `x` is a norm.
  obtain ⟨h_normal, h_prime⟩ := hU
  obtain ⟨U, hU_open⟩ := U
  obtain ⟨χ, rfl⟩ : ∃ χ : QZChar Γ, ker χ = U :=
    exists_ker_eq_of_isCyclic ⟨U, hU_open⟩ (isCyclic_of_prime_card (hp := ⟨h_prime⟩) rfl)
  obtain ⟨x, rfl⟩ : ∃ x : Kˣ, α = cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω (.ofMul x)) :=
    ((cyclicClass_spec χ).left α).mp h_res
  have h_symbol (v : FinPlace K) :
      abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1 :=
    v.isPlaceOver_placeOver.abelianLift_artinAt_eq_one_iff.mpr (h_dec v.isPlaceOver_placeOver)
  exact (cyclicClass_eq_zero_iff_norm (L := fixedFieldOf (ker χ)) x).mpr
    (exists_map_norm_eq_of_abelianLift_artinAt_eq_one (by rwa [finrank_fixedFieldOf]) h_conj
      h_symbol)

end New
