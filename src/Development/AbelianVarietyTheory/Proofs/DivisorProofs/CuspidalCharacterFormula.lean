import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspValueComparison
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameCharacterTorusValues
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField

section
noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.isInt (x : _root_.Formalism.CyclotomicNorms.Fbar g) : IsIntegral (ZMod g) x :=
  Algebra.IsIntegral.isIntegral x

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar {f : (ZMod g)[X]} (hf : f ≠ 0) {x : _root_.Formalism.CyclotomicNorms.Fbar g} :
    x ∈ _root_.Formalism.CyclotomicNorms.rootsBar f ↔ aeval x f = 0 := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, aeval_def]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.nodup_minpoly (x : _root_.Formalism.CyclotomicNorms.Fbar g) : (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) x)).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  exact nodup_roots ((PerfectField.separable_of_irreducible
    (minpoly.irreducible (_root_.GlobalTheory.GoodCharsCompare.isInt x))).map)

theorem rootsBar_mul {f h : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0) :
    rootsBar (f * h) = rootsBar f + rootsBar h := by
  rw [rootsBar, rootsBar, rootsBar, Polynomial.map_mul, roots_mul]
  exact mul_ne_zero (Polynomial.map_ne_zero hf) (Polynomial.map_ne_zero hh)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_of_rootsBar {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : _root_.Formalism.CyclotomicNorms.rootsBar f = _root_.Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  have key : ∀ {p : (ZMod g)[X]}, p.Monic →
      ((_root_.Formalism.CyclotomicNorms.rootsBar p).map fun a => X - C a).prod = p.map (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)) := by
    intro p hp
    unfold _root_.Formalism.CyclotomicNorms.rootsBar
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      IsAlgClosed.card_roots_eq_natDegree
  apply Polynomial.map_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g))
    (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective
  rw [← key hf, ← key hh, e]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.card_rootsBar (f : (ZMod g)[X]) :
    (_root_.Formalism.CyclotomicNorms.rootsBar f).card = f.natDegree := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem exists_minpoly {P : (ZMod g)[X]} (hm : P.Monic) (hP : Irreducible P) :
    ∃ x : Fbar g, P = minpoly (ZMod g) x := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) P (degree_pos_of_irreducible hP).ne'
  exact ⟨x, minpoly.eq_of_irreducible_of_monic hP hx hm⟩

abbrev dg (y : Fbar g) : ℕ := (minpoly (ZMod g) y).natDegree

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.dg_pos (y : _root_.Formalism.CyclotomicNorms.Fbar g) : 0 < _root_.GlobalTheory.GoodCharsCompare.dg y :=
  minpoly.natDegree_pos (_root_.GlobalTheory.GoodCharsCompare.isInt y)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar (y : _root_.Formalism.CyclotomicNorms.Fbar g) :
    y ^ g ^ _root_.GlobalTheory.GoodCharsCompare.dg y = y ∧
    ∀ i < _root_.GlobalTheory.GoodCharsCompare.dg y, ∀ j < _root_.GlobalTheory.GoodCharsCompare.dg y,
      y ^ g ^ i = y ^ g ^ j → i = j := by
  have hg : g.Prime := Fact.out
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {y}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {y}) := Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) {y}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {y}) =
      g ^ _root_.GlobalTheory.GoodCharsCompare.dg y := by
    rw [Module.card_eq_pow_finrank (K := ZMod g) (V := IntermediateField.adjoin (ZMod g) {y}),
      ZMod.card, IntermediateField.adjoin.finrank hint]
  have fixed : ∀ k, 0 < k → y ^ g ^ k = y → _root_.GlobalTheory.GoodCharsCompare.dg y ≤ k := by
    intro k hk hy
    let S : Subfield (_root_.Formalism.CyclotomicNorms.Fbar g) :=
      (iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k).eqLocusField (RingHom.id _)
    let T : IntermediateField (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) := S.toIntermediateField (fun x => by
      show iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) x) =
        algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) x
      rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow])
    have hKT : IntermediateField.adjoin (ZMod g) {y} ≤ T :=
      IntermediateField.adjoin_simple_le_iff.mpr (by
        show iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g k y = y
        rw [iterateFrobenius_def, hy])
    have hne : (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero _ hk.ne' hg.one_lt
    have hle : Fintype.card (IntermediateField.adjoin (ZMod g) {y}) ≤ g ^ k := by
      classical
      calc Fintype.card (IntermediateField.adjoin (ZMod g) {y})
          = (Finset.univ.image fun z : IntermediateField.adjoin (ZMod g) {y} =>
              (z : _root_.Formalism.CyclotomicNorms.Fbar g)).card := by
            rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).roots.toFinset.card := by
            apply Finset.card_le_card
            intro z hz
            obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
            have hw : (w : _root_.Formalism.CyclotomicNorms.Fbar g) ^ g ^ k = w := by
              rw [← iterateFrobenius_def]
              exact hKT w.2
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hw,
              sub_self]
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).roots.card := Multiset.toFinset_card_le _
        _ ≤ (X ^ g ^ k - X : (_root_.Formalism.CyclotomicNorms.Fbar g)[X]).natDegree := card_roots' _
        _ = g ^ k := FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hk.ne' hg.one_lt
    rw [hcard] at hle
    exact (Nat.pow_le_pow_iff_right hg.one_lt).mp hle
  refine ⟨?_, ?_⟩
  · have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) y)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  · have key : ∀ i j, i < j → j < _root_.GlobalTheory.GoodCharsCompare.dg y → y ^ g ^ i = y ^ g ^ j → False := by
      intro i j hij hj e
      have hfix : y ^ g ^ (j - i) = y := by
        apply (iterateFrobenius (_root_.Formalism.CyclotomicNorms.Fbar g) g i).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add,
          Nat.sub_add_cancel hij.le]
        exact e.symm
      have := fixed (j - i) (Nat.sub_pos_of_lt hij) hfix
      omega
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj e).elim
    · exact h
    · exact (key j i h hi e.symm).elim

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g (f : (ZMod g)[X]) (y : _root_.Formalism.CyclotomicNorms.Fbar g) (i : ℕ)
    (h : aeval y f = 0) : aeval (y ^ g ^ i) f = 0 := by
  induction i with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, pow_mul, ← expand_aeval, ZMod.expand_card, map_pow, ih,
      zero_pow (Fact.out : g.Prime).ne_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
open Classical in
theorem _root_.GlobalTheory.GoodCharsCompare.roots_minpoly (y : _root_.Formalism.CyclotomicNorms.Fbar g) :
    (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y)).toFinset =
      (Finset.range (_root_.GlobalTheory.GoodCharsCompare.dg y)).image fun i => y ^ g ^ i := by
  have h0 : minpoly (ZMod g) y ≠ 0 := minpoly.ne_zero (_root_.GlobalTheory.GoodCharsCompare.isInt y)
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Multiset.mem_toFinset, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar h0]
    exact _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g _ _ _ (minpoly.aeval _ _)
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    · calc _ ≤ (_root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y)).card := Multiset.toFinset_card_le _
        _ = _ := _root_.GlobalTheory.GoodCharsCompare.card_rootsBar _
    · intro i hi j hj e
      exact (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 i (by simpa using hi) j
        (by simpa using hj) e

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.mem_roots_minpoly {y z : _root_.Formalism.CyclotomicNorms.Fbar g} :
    z ∈ _root_.Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod g) y) ↔ ∃ i, z = y ^ g ^ i := by
  classical
  constructor
  · intro hz
    rw [← Multiset.mem_toFinset, _root_.GlobalTheory.GoodCharsCompare.roots_minpoly] at hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar
      (minpoly.ne_zero (_root_.GlobalTheory.GoodCharsCompare.isInt y))]
    exact _root_.GlobalTheory.GoodCharsCompare.aeval_pow_g _ _ _ (minpoly.aeval _ _)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.pow_g_of {y : _root_.Formalism.CyclotomicNorms.Fbar g} {d : ℕ} (h : y ^ (g ^ d - 1) = 1) :
    y ^ g ^ d = y := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow d g (Fact.out : g.Prime).pos), pow_succ, h, one_mul]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_sub_one_eq_one_of_pow_pow_eq {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.pow_dg {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) :
    y ^ (g ^ _root_.GlobalTheory.GoodCharsCompare.dg y - 1) = 1 :=
  pow_sub_one_eq_one_of_pow_pow_eq hy (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1

theorem exists_prim {d : ℕ} (hd : 0 < d) :
    ∃ (φ : GaloisField g d →ₐ[ZMod g] Fbar g) (u : GaloisField g d), IsPrimitiveRoot (φ u) (g ^ d - 1) := by
  let φ : GaloisField g d →ₐ[ZMod g] Fbar g := IsAlgClosed.lift
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField g d)ˣ)
  refine ⟨φ, u, IsPrimitiveRoot.map_of_injective ?_ φ.injective⟩
  rw [Nat.card_units, GaloisField.card g d hd.ne'] at hu
  rw [← hu, ← orderOf_units]
  exact IsPrimitiveRoot.orderOf _

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.rootC_prim {d : ℕ} (hd : 0 < d) :
    IsPrimitiveRoot (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1)) (g ^ d - 1) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC
  exact Complex.isPrimitiveRoot_exp _ (_root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos hd).ne'

theorem rootOfOne_eq (d m : ℕ) : rootOfOne g d m = rootC (g ^ d - 1) ^ m := by
  have : 1 ≤ g ^ d := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
  rw [rootOfOne, rootC, ← Complex.exp_nat_mul, Nat.cast_sub this]
  congr 1
  push_cast
  ring

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_log (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d)
    {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ^ (g ^ d - 1) = 1) :
    ∃ m, ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ m := by
  haveI : NeZero (g ^ d - 1) := ⟨(_root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos hd).ne'⟩
  obtain ⟨i, -, hi⟩ := (_root_.GlobalTheory.GoodCharsCompare.rootC_prim (g := g) hd).eq_pow_of_pow_eq_one
    (ξ := ω y) (by rw [← map_pow, hy, map_one])
  exact ⟨i, hi.symm⟩

theorem pow_eq_of_rootC {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ (g ^ d - 1) = 1) {a b : ℕ}
    (h : rootC (g ^ d - 1) ^ a = rootC (g ^ d - 1) ^ b) : z ^ a = z ^ b := by
  haveI : NeZero (g ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨m, -, rfl⟩ := (rootC_prim (g := g) hd).eq_pow_of_pow_eq_one hz
  rw [← pow_mul, mul_comm, pow_mul, h, ← pow_mul, ← pow_mul, mul_comm]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.labelChar_eq (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d)
    {x y : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) {m : ℕ}
    (hm : ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ m) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.labelChar ω d x y = ω x ^ m := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.labelChar
  have npos := _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos (g := g) hd
  have hprim := _root_.GlobalTheory.GoodCharsCompare.rootC_prim (g := g) hd
  have red : ∀ ξ : ℂ, ξ ^ (g ^ d - 1) = 1 → ∀ k, ξ ^ k = ξ ^ (k % (g ^ d - 1)) := by
    intro ξ hξ k
    conv_lhs => rw [← Nat.mod_add_div k (g ^ d - 1), pow_add, pow_mul, hξ, one_pow, mul_one]
  have hs : ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^
      sInf {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a} :=
    Nat.sInf_mem (s := {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a}) ⟨m, hm⟩
  have hxn : ω x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hmod : sInf {a | ω y = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison.rootC (g ^ d - 1) ^ a} % (g ^ d - 1) =
      m % (g ^ d - 1) := by
    apply hprim.pow_inj (Nat.mod_lt _ npos) (Nat.mod_lt _ npos)
    rw [← red _ hprim.pow_eq_one, ← red _ hprim.pow_eq_one]
    exact hs.symm.trans hm
  rw [red _ hxn, hmod, ← red _ hxn]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_preimage {ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ}
    (hω : Function.Injective ω) {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ (g ^ d - 1) = 1) :
    ∃ y : _root_.Formalism.CyclotomicNorms.Fbar g, y ^ (g ^ d - 1) = 1 ∧ ω y = z := by
  classical
  have hg : g.Prime := Fact.out
  have npos := _root_.GlobalTheory.GoodCharsCompare.g_pow_sub_pos (g := g) hd
  have hnF : ((g ^ d - 1 : ℕ) : _root_.Formalism.CyclotomicNorms.Fbar g) ≠ 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow d g hg.pos), Nat.cast_pow, CharP.cast_eq_zero,
      zero_pow hd.ne', zero_sub, Nat.cast_one, neg_ne_zero]
    exact one_ne_zero
  have hsep : (X ^ (g ^ d - 1) - C (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).Separable :=
    separable_X_pow_sub_C 1 hnF one_ne_zero
  have hA : (nthRoots (g ^ d - 1) (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).toFinset.card = g ^ d - 1 := by
    unfold nthRoots
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
      natDegree_X_pow_sub_C]
  have himage : (nthRoots (g ^ d - 1) (1 : _root_.Formalism.CyclotomicNorms.Fbar g)).toFinset.image ω ⊆
      (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    rw [Multiset.mem_toFinset, mem_nthRoots npos] at hy ⊢
    rw [← map_pow, hy, map_one]
  have hcardB : (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset.card ≤ g ^ d - 1 :=
    (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)
  have heq := Finset.eq_of_subset_of_card_le himage
    (by rw [Finset.card_image_of_injective _ hω, hA]; exact hcardB)
  have hzB : z ∈ (nthRoots (g ^ d - 1) (1 : ℂ)).toFinset := by
    rw [Multiset.mem_toFinset, mem_nthRoots npos]
    exact hz
  rw [← heq] at hzB
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzB
  rw [Multiset.mem_toFinset, mem_nthRoots npos] at hy
  exact ⟨y, hy, rfl⟩

theorem exists_matrix {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι) {y : Fbar g}
    (hy : y ^ (g ^ Fintype.card ι - 1) = 1) :
    ∃ M : Matrix ι ι (ZMod g), minpoly (ZMod g) M = minpoly (ZMod g) y := by
  haveI : NeZero (g ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨φ, u, hu⟩ := exists_prim (g := g) hd
  obtain ⟨m, -, hm⟩ := hu.eq_pow_of_pow_eq_one hy
  let B : Module.Basis ι (ZMod g) (GaloisField g (Fintype.card ι)) :=
    (Module.finBasisOfFinrankEq _ _ (GaloisField.finrank g hd.ne')).reindex (Fintype.equivFin ι).symm
  refine ⟨Algebra.leftMulMatrix B (u ^ m), ?_⟩
  rw [minpoly.algHom_eq _ (Algebra.leftMulMatrix_injective B), ← hm, ← map_pow, minpoly.algHom_eq _ φ.injective]

theorem charpoly_eq_pow {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) {y : Fbar g}
    (h : minpoly (ZMod g) M = minpoly (ZMod g) y) : ∃ k, M.charpoly = minpoly (ZMod g) y ^ k := by
  have hm : aeval (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g))))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g))) = 0 := by
    have h1 := minpoly.aeval (ZMod g) M
    rw [h] at h1
    have h2 : aeval (M.map (algebraMap (ZMod g) (Fbar g))) (minpoly (ZMod g) y) = 0 := by
      have := aeval_algHom_apply (Algebra.ofId (ZMod g) (Fbar g)).mapMatrix M (minpoly (ZMod g) y)
      rw [h1, map_zero] at this
      exact this
    have h3 := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := Fbar g) (n := ι)) (M.map (algebraMap (ZMod g) (Fbar g)))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g)))
    rw [aeval_map_algebraMap (Fbar g) (M.map (algebraMap (ZMod g) (Fbar g))), h2, map_zero] at h3
    exact h3
  have key : ∀ q : (ZMod g)[X], q.Monic → Irreducible q → q ∣ M.charpoly → q = minpoly (ZMod g) y := by
    intro q hq hi hd
    obtain ⟨z, rfl⟩ := exists_minpoly hq hi
    have hz : aeval z M.charpoly = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval _ _)
    have hev : Module.End.HasEigenvalue (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map, IsRoot,
        eval_map_algebraMap]
      exact hz
    rw [Module.End.hasEigenvalue_iff_isRoot] at hev
    have h3 := hev.dvd (minpoly.dvd _ _ hm)
    rw [IsRoot, eval_map_algebraMap] at h3
    exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (isInt y)) h3 (minpoly.monic (isInt y))).symm
  have gen : ∀ n, ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → f ∣ M.charpoly →
      ∃ k, f = minpoly (ZMod g) y ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn hd
      by_cases h1 : f = 1
      · exact ⟨0, by simp [h1]⟩
      · have hu : ¬ IsUnit f := fun hu => h1 (hf.isUnit_iff.1 hu)
        obtain ⟨P, hPm, hP, t, rfl⟩ := exists_monic_irreducible_factor f hu
        have hh : t.Monic := hPm.of_mul_monic_left hf
        have hlt : t.natDegree < n := by
          rw [← hn, hPm.natDegree_mul hh]
          have := hP.natDegree_pos
          omega
        obtain ⟨k, hk⟩ := ih _ hlt t hh rfl (dvd_of_mul_left_dvd hd)
        exact ⟨k + 1, by rw [pow_succ', ← hk, ← key P hPm hP (dvd_of_mul_right_dvd hd)]⟩
  exact gen _ _ M.charpoly_monic rfl dvd_rfl

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.rootsBar_pow (f : (ZMod g)[X]) (k : ℕ) : _root_.Formalism.CyclotomicNorms.rootsBar (f ^ k) = k • _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, roots_pow]

theorem finrank_eig {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) {y : Fbar g}
    (h : minpoly (ZMod g) M = minpoly (ZMod g) y) {k : ℕ} (hk : M.charpoly = minpoly (ZMod g) y ^ k)
    {z : Fbar g} (hz : z ∈ rootsBar (minpoly (ZMod g) y)) :
    Module.finrank (Fbar g) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z) = k := by
  classical
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  have hm : aeval (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g))))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g))) = 0 := by
    have h1 := minpoly.aeval (ZMod g) M
    rw [h] at h1
    have h2 : aeval (M.map (algebraMap (ZMod g) (Fbar g))) (minpoly (ZMod g) y) = 0 := by
      have := aeval_algHom_apply (Algebra.ofId (ZMod g) (Fbar g)).mapMatrix M (minpoly (ZMod g) y)
      rw [h1, map_zero] at this
      exact this
    have h3 := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := Fbar g) (n := ι)) (M.map (algebraMap (ZMod g) (Fbar g)))
      ((minpoly (ZMod g) y).map (algebraMap (ZMod g) (Fbar g)))
    rw [aeval_map_algebraMap (Fbar g) (M.map (algebraMap (ZMod g) (Fbar g))), h2, map_zero] at h3
    exact h3
  have hss := Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (PerfectField.separable_of_irreducible (minpoly.irreducible (isInt y))).map.squarefree hm
  rw [← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, LinearMap.finrank_maxGenEigenspace_eq,
    Matrix.charpoly_toLin', Matrix.charpoly_map, ← count_roots]
  change Multiset.count z (rootsBar M.charpoly) = k
  rw [hk, rootsBar_pow, Multiset.count_nsmul, Multiset.count_eq_one_of_mem (nodup_minpoly y) hz, mul_one]

theorem cuspVal_eq_torusValue (ω : Fbar g →*₀ ℂ) {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι)
    (M : Matrix ι ι (ZMod g)) {x y : Fbar g} (hx : x ^ (g ^ Fintype.card ι - 1) = 1)
    (h : minpoly (ZMod g) M = minpoly (ZMod g) y) {m : ℕ} (hm : ω y = rootC (g ^ Fintype.card ι - 1) ^ m) :
    cuspVal ω x M = torusValue g (Fintype.card ι) (dg y) (ω x) m := by
  classical
  obtain ⟨k, hk⟩ := charpoly_eq_pow M h
  have hdk : Fintype.card ι = dg y * k := by
    rw [← M.charpoly_natDegree_eq_dim, hk, (minpoly.monic (isInt y)).natDegree_pow, mul_comm]
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left (hdk ▸ hd)
  have hq : Fintype.card ι / dg y = k := by rw [hdk, Nat.mul_div_cancel_left _ (dg_pos y)]
  have hR : (rootsBar M.charpoly).toFinset = (rootsBar (minpoly (ZMod g) y)).toFinset := by
    rw [hk, rootsBar_pow, Multiset.toFinset_nsmul _ _ hk0.ne']
  have hcard : (rootsBar (minpoly (ZMod g) y)).toFinset.card = dg y := by
    rw [Multiset.toFinset_card_of_nodup (nodup_minpoly y), card_rootsBar]
  rw [cuspVal, if_pos ⟨_, k, minpoly.irreducible (isInt y), hk⟩, torusValue, hq]
  have e1 : ∀ z ∈ (rootsBar (minpoly (ZMod g) y)).toFinset,
      labelChar ω (Fintype.card ι) x z * ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z)),
          (1 - (g : ℂ) ^ (dg y * i)) =
      labelChar ω (Fintype.card ι) x z * ∏ i ∈ Finset.Ico 1 k, (1 - (g : ℂ) ^ (dg y * i)) := by
    intro z hz
    rw [finrank_eig M h hk (Multiset.mem_toFinset.1 hz)]
  have e2 : ∑ z ∈ (rootsBar (minpoly (ZMod g) y)).toFinset, labelChar ω (Fintype.card ι) x z =
      ∑ i ∈ Finset.range (dg y), ω x ^ (m * g ^ i) := by
    rw [roots_minpoly, Finset.sum_image]
    · refine Finset.sum_congr rfl fun i _ => labelChar_eq ω hd hx ?_
      rw [map_pow, hm, ← pow_mul]
    · intro i hi j hj h
      exact (frobenius_orbit_degreeOverPrimeFieldFbar y).2 i (by simpa using hi) j (by simpa using hj) h
  have e3 : ∏ i ∈ Finset.Ico 1 k, (1 - (g : ℂ) ^ (dg y * i)) =
      (-1) ^ (k - 1) * ∏ i ∈ Finset.Ico 1 k, ((g : ℂ) ^ (dg y * i) - 1) := by
    rw [← Nat.card_Ico, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  have e4 : (-1 : ℂ) ^ (Fintype.card ι - 1) * (-1) ^ (k - 1) = (-1) ^ (Fintype.card ι - k) := by
    have hle : k ≤ Fintype.card ι := hdk ▸ Nat.le_mul_of_pos_left _ (dg_pos y)
    rw [← pow_add, show Fintype.card ι - 1 + (k - 1) = Fintype.card ι - k + 2 * (k - 1) by omega, pow_add, pow_mul]
    simp
  have e5 := Finset.sum_congr rfl e1
  rw [← Finset.sum_mul, e2, e3] at e5
  have := hR
  convert_to (-1) ^ (Fintype.card ι - 1) * (∑ z ∈ (rootsBar (minpoly (ZMod g) y)).toFinset,
      labelChar ω (Fintype.card ι) x z * ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) z)),
          (1 - (g : ℂ) ^ (dg y * i))) = _
  · rw [← hcard, ← hR]
  rw [e5, ← e4]
  ring

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.sum_shift {z : ℂ} {m e : ℕ} (h : z ^ (m * g ^ e) = z ^ m) (j : ℕ) :
    ∑ i ∈ Finset.range e, (z ^ g ^ j) ^ (m * g ^ i) = ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
  have hper : ∀ i, z ^ (m * g ^ (i + e)) = z ^ (m * g ^ i) := fun i => by
    rw [show m * g ^ (i + e) = m * g ^ e * g ^ i by ring, pow_mul, h, ← pow_mul]
  have shift : ∀ j, ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) =
      ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (e + 1), z ^ (m * g ^ (i + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + 1 + j)) + z ^ (m * g ^ (0 + j)) :=
        Finset.sum_range_succ' _ _
      have h2 : ∑ i ∈ Finset.range (e + 1), z ^ (m * g ^ (i + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) + z ^ (m * g ^ (e + j)) :=
        Finset.sum_range_succ _ _
      have h3 : z ^ (m * g ^ (e + j)) = z ^ (m * g ^ (0 + j)) := by
        rw [add_comm e j, hper, zero_add]
      have h4 : ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + 1 + j)) =
          ∑ i ∈ Finset.range e, z ^ (m * g ^ (i + j)) :=
        add_right_cancel (h1.symm.trans (h2.trans (congrArg (HAdd.hAdd _) h3)))
      rw [← ih, ← h4]
      exact Finset.sum_congr rfl fun i _ => by rw [show i + (j + 1) = i + 1 + j by omega]
  rw [← shift j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul]
  congr 1
  ring

theorem sum_period {z : ℂ} {m e : ℕ} (h : z ^ (m * g ^ e) = z ^ m) (k : ℕ) :
    ∑ i ∈ Finset.range (e * k), z ^ (m * g ^ i) = k * ∑ i ∈ Finset.range e, z ^ (m * g ^ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul, ← sum_shift h (e * k)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
    congr 1
    ring

theorem period_of (ω : Fbar g →*₀ ℂ) {d : ℕ} (hd : 0 < d) {x y : Fbar g} (hx : x ^ (g ^ d - 1) = 1) {m : ℕ}
    (hm : ω y = rootC (g ^ d - 1) ^ m) : ω x ^ (m * g ^ dg y) = ω x ^ m := by
  refine pow_eq_of_rootC (g := g) hd (by rw [← map_pow, hx, map_one]) ?_
  rw [pow_mul, ← hm, ← map_pow, (frobenius_orbit_degreeOverPrimeFieldFbar y).1]

theorem mem_orbit_of_sums {z w : ℂ} {d : ℕ} (hd : 0 < d)
    (h : ∀ m : ℕ, ∑ i ∈ Finset.range d, z ^ (m * g ^ i) = ∑ i ∈ Finset.range d, w ^ (m * g ^ i)) :
    ∃ j, w = z ^ g ^ j := by
  classical
  by_contra hn
  push Not at hn
  have hQ : ∀ Q : ℂ[X], ∑ i ∈ Finset.range d, Q.eval (z ^ g ^ i) = ∑ i ∈ Finset.range d, Q.eval (w ^ g ^ i) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => simp only [eval_add, Finset.sum_add_distrib, hp, hq]
    | monomial n a =>
      simp only [eval_monomial, ← Finset.mul_sum, ← pow_mul]
      have := h n
      simp only [mul_comm n] at this
      rw [this]
  let S : Finset ℂ := (((Finset.range d).image fun i => z ^ g ^ i) ∪ (Finset.range d).image fun i => w ^ g ^ i).erase w
  let Q : ℂ[X] := ∏ a ∈ S, (X - C a)
  have hz : ∀ a ∈ S, Q.eval a = 0 := by
    intro a ha
    rw [eval_prod]
    exact Finset.prod_eq_zero ha (by simp)
  have hw : Q.eval w ≠ 0 := by
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun a ha => ?_
    simpa [sub_eq_zero] using (Finset.ne_of_mem_erase ha).symm
  have h1 := hQ Q
  rw [Finset.sum_eq_zero (fun i hi => hz _ (Finset.mem_erase.2 ⟨(hn i).symm,
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)⟩))] at h1
  have h2 : ∑ i ∈ Finset.range d, Q.eval (w ^ g ^ i) =
      ∑ i ∈ (Finset.range d).filter (fun i => w ^ g ^ i = w), Q.eval w := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    split_ifs with hh
    · rw [hh]
    · exact hz _ (Finset.mem_erase.2 ⟨hh, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)⟩)
  rw [h2, Finset.sum_const, nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1.symm with h3 | h3
  · have : 0 ∈ (Finset.range d).filter (fun i => w ^ g ^ i = w) := by simp [hd]
    exact Finset.card_ne_zero_of_mem this (by exact_mod_cast h3)
  · exact hw h3

end GlobalTheory.GoodCharsCompare
end
end

section
noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_dg_mul_eq_self (y : _root_.Formalism.CyclotomicNorms.Fbar g) (q : ℕ) :
    y ^ g ^ (_root_.GlobalTheory.GoodCharsCompare.dg y * q) = y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_dg_mul {d : ℕ} (hd : 0 < d) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ^ (g ^ d - 1) = 1) : ∃ k, d = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
  have hDpos := _root_.GlobalTheory.GoodCharsCompare.dg_pos y
  have hd' : y ^ g ^ d = y := _root_.GlobalTheory.GoodCharsCompare.pow_g_of hy
  refine ⟨d / _root_.GlobalTheory.GoodCharsCompare.dg y, ?_⟩
  have hr : y ^ g ^ (d % _root_.GlobalTheory.GoodCharsCompare.dg y) = y ^ g ^ 0 := by
    rw [pow_zero, pow_one]
    conv_rhs => rw [← hd', ← Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y), pow_add, pow_mul,
      pow_pow_dg_mul_eq_self]
  have h1 := (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 _ (Nat.mod_lt _ hDpos) 0 hDpos hr
  have h2 := Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y)
  rw [h1, add_zero] at h2
  exact h2.symm

theorem exists_unit_of_pow {y : Fbar g} (hy : y ^ (g ^ 1 - 1) = 1) :
    ∃ c : (ZMod g)ˣ, algebraMap (ZMod g) (Fbar g) c = y := by
  obtain ⟨k, hk⟩ := exists_dg_mul one_pos hy
  have h1 : dg y = 1 := Nat.eq_one_of_mul_eq_one_right hk.symm
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, zero_pow (g_pow_sub_pos one_pos).ne'] at hy
    exact zero_ne_one hy
  exact ⟨Units.mk0 c hc0, hc⟩

theorem unit_pow (c : (ZMod g)ˣ) : algebraMap (ZMod g) (Fbar g) c ^ (g ^ 1 - 1) = 1 := by
  rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one]

theorem exists_alpha {ω ω' : Fbar g →*₀ ℂ} (hω : Function.Injective ω) (hω' : Function.Injective ω') :
    ∃ α : Fbar g ≃* Fbar g, ∀ x, ω (α x) = ω' x := by
  have key : ∀ {ω ω' : Fbar g →*₀ ℂ}, Function.Injective ω → ∀ x, ∃ z, ω z = ω' x := by
    intro ω ω' hω x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · obtain ⟨z, -, hz⟩ := exists_preimage hω (dg_pos x) (z := ω' x) (by rw [← map_pow, pow_dg hx, map_one])
      exact ⟨z, hz⟩
  choose a ha using key (ω' := ω') hω
  choose a' ha' using key (ω' := ω) hω'
  exact ⟨⟨⟨a, a', fun x => hω' (by rw [ha', ha]), fun x => hω (by rw [ha, ha'])⟩,
    fun x y => hω (by simp only [ha, map_mul])⟩, ha⟩

theorem exists_exp (α : Fbar g ≃* Fbar g) {d : ℕ} (hd : 0 < d) :
    ∃ a : ℕ, ∀ z : Fbar g, z ^ (g ^ d - 1) = 1 → α z = z ^ a := by
  have : NeZero (g ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨φ, u, hu⟩ := exists_prim (g := g) hd
  obtain ⟨a, -, ha⟩ := hu.eq_pow_of_pow_eq_one (ξ := α (φ u)) (by rw [← map_pow, hu.pow_eq_one, map_one])
  refine ⟨a, fun z hz => ?_⟩
  obtain ⟨k, -, rfl⟩ := hu.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_beta {ω ω' : Fbar g →*₀ ℂ} (hω : Function.Injective ω) (hω' : Function.Injective ω') :
    ∃ β : Fbar g ≃* Fbar g, ∀ d, 0 < d → ∀ x y : Fbar g, x ^ (g ^ d - 1) = 1 → y ^ (g ^ d - 1) = 1 →
      labelChar ω' d x y = labelChar ω d (β x) y := by
  obtain ⟨α, hα⟩ := exists_alpha hω hω'
  refine ⟨α.trans α, fun d hd x y hx hy => ?_⟩
  obtain ⟨a, ha⟩ := exists_exp α hd
  obtain ⟨n, hn⟩ := exists_log ω hd hy
  have hx1 : α x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  have hx2 : α (α x) ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx1, map_one]
  rw [labelChar_eq ω' hd hx (m := n * a) (by rw [← hα, ha y hy, map_pow, hn, ← pow_mul]), MulEquiv.trans_apply,
    labelChar_eq ω hd hx2 hn, ha _ hx1, map_pow, hα, ← pow_mul, mul_comm]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_sub_one_eq_one_of_pow_pow_eq_self {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.root_pow {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι (ZMod g)} (hM : M.det ≠ 0)
    {p : (ZMod g)[X]} {k : ℕ} (hp : Irreducible p) (hk : M.charpoly = p ^ k) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ∈ _root_.Formalism.CyclotomicNorms.rootsBar M.charpoly) : y ^ (g ^ Fintype.card ι - 1) = 1 := by
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  have hchar0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, ← coeff_zero_eq_aeval_zero',
      map_eq_zero] at hy
    apply hM
    rw [Matrix.det_eq_sign_charpoly_coeff, hy, mul_zero]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [hk, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar one_ne_zero, map_one] at hy
    exact one_ne_zero hy
  have hyp : aeval y p = 0 := by
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, hk, map_pow] at hy
    exact (pow_eq_zero_iff hk0).mp hy
  have hdvd : minpoly (ZMod g) y ∣ p := minpoly.dvd _ _ hyp
  have hassoc : Associated (minpoly (ZMod g) y) p :=
    associated_of_dvd_dvd hdvd ((minpoly.irreducible hint).dvd_symm hp hdvd)
  have hdeg : p.natDegree = _root_.GlobalTheory.GoodCharsCompare.dg y :=
    (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)).symm
  have hcard : Fintype.card ι = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hk, natDegree_pow, hdeg, mul_comm]
  apply pow_pow_sub_one_eq_one_of_pow_pow_eq_self hy0
  rw [hcard]
  exact pow_pow_dg_mul_eq_self y k

theorem cuspVal_congr {ω ω' : Fbar g →*₀ ℂ} {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι (ZMod g)}
    (hM : M.det ≠ 0) {x x' : Fbar g} (h : ∀ y : Fbar g, y ^ (g ^ Fintype.card ι - 1) = 1 →
      labelChar ω' (Fintype.card ι) x y = labelChar ω (Fintype.card ι) x' y) : cuspVal ω' x M = cuspVal ω x' M := by
  unfold cuspVal
  split_ifs with hh
  · obtain ⟨p, k, hp, hk⟩ := hh
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [h y (root_pow hM hp hk (by simpa using hy))]
  · rfl

def Tr (β : Fbar g ≃* Fbar g) (f f' : (ZMod g)[X]) : Prop :=
  f'.Monic ∧ rootsBar f' = (rootsBar f).map β

theorem Tr.mul {β : Fbar g ≃* Fbar g} {f f' h h' : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0)
    (h1 : Tr β f f') (h2 : Tr β h h') : Tr β (f * h) (f' * h') :=
  ⟨h1.1.mul h2.1, by
    rw [rootsBar_mul h1.1.ne_zero h2.1.ne_zero, rootsBar_mul hf hh, h1.2, h2.2, Multiset.map_add]⟩

theorem Tr.unique {β : Fbar g ≃* Fbar g} {f f' f'' : (ZMod g)[X]} (h1 : Tr β f f') (h2 : Tr β f f'') : f' = f'' :=
  eq_of_rootsBar h1.1 h2.1 (h1.2.trans h2.2.symm)

theorem Tr.symm {β : Fbar g ≃* Fbar g} {f f' : (ZMod g)[X]} (hf : f.Monic) (h1 : Tr β f f') : Tr β.symm f' f :=
  ⟨hf, by rw [h1.2, Multiset.map_map]; simp⟩

theorem Tr.natDegree {β : Fbar g ≃* Fbar g} {f f' : (ZMod g)[X]} (h1 : Tr β f f') : f'.natDegree = f.natDegree := by
  rw [← card_rootsBar, h1.2, Multiset.card_map, card_rootsBar]

theorem tr_minpoly (β : Fbar g ≃* Fbar g) (x : Fbar g) : Tr β (minpoly (ZMod g) x) (minpoly (ZMod g) (β x)) := by
  refine ⟨minpoly.monic (isInt _), ?_⟩
  rw [Multiset.Nodup.ext (nodup_minpoly _) ((nodup_minpoly x).map β.injective)]
  intro y
  rw [mem_roots_minpoly, Multiset.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨x ^ g ^ i, mem_roots_minpoly.2 ⟨i, rfl⟩, map_pow _ _ _⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨i, rfl⟩ := mem_roots_minpoly.1 hz
    exact ⟨i, map_pow _ _ _⟩

theorem tr_one (β : Fbar g ≃* Fbar g) : Tr β 1 1 := ⟨monic_one, by simp [rootsBar]⟩

theorem tr_prod (β : Fbar g ≃* Fbar g) (s : Finset ℕ) (φ φ' : ℕ → (ZMod g)[X]) (h0 : ∀ c ∈ s, (φ c).Monic)
    (h : ∀ c ∈ s, Tr β (φ c) (φ' c)) : Tr β (∏ c ∈ s, φ c) (∏ c ∈ s, φ' c) := by
  induction s using Finset.induction_on with
  | empty => simpa using tr_one β
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Tr.mul (h0 a (by simp)).ne_zero (monic_prod_of_monic _ _ fun c hc => h0 c (by simp [hc])).ne_zero
      (h a (by simp)) (ih (fun c hc => h0 c (by simp [hc])) fun c hc => h c (by simp [hc]))

theorem exists_tr (β : Fbar g ≃* Fbar g) (n : ℕ) :
    ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → ∃ f', Tr β f f' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn
    by_cases h1 : f = 1
    · exact ⟨1, h1 ▸ tr_one β⟩
    · have hu : ¬ IsUnit f := fun hu => h1 (hf.isUnit_iff.1 hu)
      obtain ⟨P, hPm, hP, h, rfl⟩ := exists_monic_irreducible_factor f hu
      have hh : h.Monic := hPm.of_mul_monic_left hf
      have hd : h.natDegree < n := by
        rw [← hn, hPm.natDegree_mul hh]
        have := hP.natDegree_pos
        omega
      obtain ⟨h', hh'⟩ := ih _ hd h hh rfl
      obtain ⟨x, rfl⟩ := exists_minpoly hPm hP
      exact ⟨_, (tr_minpoly β x).mul hPm.ne_zero hh.ne_zero hh'⟩

theorem Tr.dvd {β : Fbar g ≃* Fbar g} {f f' q q' : (ZMod g)[X]} (hf : f.Monic) (hq : q.Monic) (h : Tr β f f')
    (h' : Tr β q q') (hd : q ∣ f) : q' ∣ f' := by
  obtain ⟨t, rfl⟩ := hd
  have ht := hq.of_mul_monic_left hf
  obtain ⟨t', ht'⟩ := exists_tr β _ t ht rfl
  exact ⟨t', h.unique (h'.mul hq.ne_zero ht.ne_zero ht')⟩

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.coeff_zero_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    f.coeff 0 ≠ 0 ↔ (0 : _root_.Formalism.CyclotomicNorms.Fbar g) ∉ _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, ← aeval_def,
    ← coeff_zero_eq_aeval_zero', map_eq_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.squarefree_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    Squarefree f ↔ (_root_.Formalism.CyclotomicNorms.rootsBar f).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (IsAlgClosed.splits _), separable_map,
    PerfectField.separable_iff_squarefree]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.primeToPart_map (β : _root_.Formalism.CyclotomicNorms.Fbar g ≃* _root_.Formalism.CyclotomicNorms.Fbar g) (l : ℕ) (x : _root_.Formalism.CyclotomicNorms.Fbar g) :
    _root_.Formalism.CyclotomicNorms.primeToPart l (β x) = β (_root_.Formalism.CyclotomicNorms.primeToPart l x) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [MulEquiv.orderOf_eq, map_pow]

theorem isGood_tr {N : ℕ} {P J : Type} (β : P → Fbar g ≃* Fbar g) {f f' : P → (ZMod g)[X]} {χ χ' : P → J → (ZMod g)ˣ}
    (h : ∀ v, Tr (β v) (f v) (f' v))
    (hχ : ∀ v j, algebraMap (ZMod g) (Fbar g) (χ' v j) = β v (algebraMap (ZMod g) (Fbar g) (χ v j)))
    (H : IsGood N g f χ) : IsGood N g f' χ' := by
  obtain ⟨h1, h2, h3, h4, h5, v, q, hq, hqd, h6⟩ := H
  refine ⟨fun v => ⟨(h v).1, (h v).natDegree.trans (h1 v).2.1, ?_⟩, fun v => ?_, ?_, ?_, ?_, ?_⟩
  · rw [coeff_zero_iff (h v).1.ne_zero, (h v).2, Multiset.mem_map]
    rintro ⟨z, hz, h0⟩
    rw [map_eq_zero] at h0
    exact (coeff_zero_iff (h1 v).1.ne_zero).1 (h1 v).2.2 (h0 ▸ hz)
  · rw [squarefree_iff (h v).1.ne_zero, (h v).2]
    exact ((squarefree_iff (h1 v).1.ne_zero).1 (h2 v)).map (β v).injective
  · intro l hl hb v x hx y hy hxy
    rw [(h v).2, Multiset.mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [primeToPart_map, primeToPart_map] at hxy
    rw [h3 l hl hb v x hx y hy ((β v).injective hxy)]
  · intro l hl hb v j x hx hxy
    rw [(h v).2, Multiset.mem_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    rw [hχ, primeToPart_map, primeToPart_map] at hxy
    exact h4 l hl hb v j x hx ((β v).injective hxy)
  · intro a ha hb
    obtain ⟨v, hv⟩ := h5 a ha hb
    refine ⟨v, ?_⟩
    rintro ⟨q, hq, rfl⟩
    have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero (h v).1.ne_zero hq
    have hm := monic_normalize hq0
    obtain ⟨q', hq'⟩ := exists_tr (β v).symm _ _ hm rfl
    refine hv ⟨q', Tr.dvd (h v).1 hm ((h v).symm (h1 v).1) hq' (normalize_dvd_iff.2 hq), ?_⟩
    rw [hq'.natDegree]
    exact natDegree_eq_of_degree_eq (degree_normalize)
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Fbar g) q (degree_pos_of_irreducible hq).ne'
    have e1 := minpoly.eq_of_irreducible hq hx
    have e2 : (minpoly (ZMod g) (β v x)).natDegree = q.natDegree := by
      rw [(tr_minpoly (β v) x).natDegree, ← e1, natDegree_mul_leadingCoeff_inv _ hq.ne_zero]
    refine ⟨v, minpoly (ZMod g) (β v x), minpoly.irreducible (isInt _),
      Tr.dvd (h1 v).1 (minpoly.monic (isInt x)) (h v) (tr_minpoly _ x) ((minpoly.dvd _ _ hx).trans hqd), ?_⟩
    rw [e2]
    exact h6

theorem blkSize_eq {r : ℕ} (b : Fin r → ℕ) (c : ℕ) : blkSize b c = Fintype.card {a : Fin r // b a = c} :=
  (Fintype.card_subtype _).symm

theorem card_blk_pos {r : ℕ} {b : Fin r → ℕ} {c : ℕ} (hc : c ∈ Finset.univ.image b) :
    0 < Fintype.card {a : Fin r // b a = c} := by
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hc
  exact Fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩

theorem det_blkMat_ne {r : ℕ} (b : Fin r → ℕ) (c : ℕ) (p : blockTri (κ := ZMod g) b) : (blkMat b c p).det ≠ 0 :=
  (blkDet b c p).ne_zero

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_minpoly {φ : (ZMod g)[X]} (hm : φ.Monic)
    (hi : Irreducible φ) {x : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ _root_.Formalism.CyclotomicNorms.rootsBar φ) : φ = minpoly (ZMod g) x :=
  minpoly.eq_of_irreducible_of_monic hi
    ((_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hm.ne_zero).mp hx) hm

theorem root_ne_zero {s : Finset ℕ} {φ : ℕ → (ZMod g)[X]} (h0 : (∏ c ∈ s, φ c).coeff 0 ≠ 0) {c : ℕ} (hc : c ∈ s)
    (hm : (φ c).Monic) {x : Fbar g} (hx : x ∈ rootsBar (φ c)) : x ≠ 0 := by
  rintro rfl
  rw [coeff_zero_prod] at h0
  exact (coeff_zero_iff hm.ne_zero).1 (Finset.prod_ne_zero_iff.1 h0 c hc) hx

theorem isTypeChar_tr {ω ω' : Fbar g →*₀ ℂ} {β : Fbar g ≃* Fbar g}
    (hβ : ∀ d, 0 < d → ∀ x y : Fbar g, x ^ (g ^ d - 1) = 1 → y ^ (g ^ d - 1) = 1 →
      labelChar ω' d x y = labelChar ω d (β x) y) {r : ℕ} {f f' : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) (hf : Tr β f f')
    {ch : GL (Fin r) (ZMod g) → ℂ} (h : IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar ω' f ch) : IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar ω f' ch := by
  obtain ⟨b, φ, x, n, ρ, h1, rfl, h3, h4, h5⟩ := h
  have e : ∀ c ∈ Finset.univ.image b, φ c = minpoly (ZMod g) (x c) := fun c hc =>
    eq_minpoly (h1 c hc).1 (h1 c hc).2.1 (h1 c hc).2.2.2
  refine ⟨b, fun c => minpoly (ZMod g) (β (x c)), fun c => β (x c), n, ρ, fun c hc => ⟨minpoly.monic (isInt _),
    minpoly.irreducible (isInt _), ?_, mem_roots_minpoly.2 ⟨0, by simp⟩⟩, ?_, h3, fun p => ?_, h5⟩
  · rw [(tr_minpoly β (x c)).natDegree, ← e c hc, (h1 c hc).2.2.1]
  · exact hf.unique (tr_prod β _ _ _ (fun c hc => (h1 c hc).1) fun c hc => e c hc ▸ tr_minpoly β (x c))
  · rw [h4]
    refine Finset.prod_congr rfl fun c hc => cuspVal_congr (det_blkMat_ne b c p) fun y hy =>
      hβ _ (card_blk_pos hc) _ _ ?_ hy
    rw [← (h1 c hc).2.2.1, e c hc]
    exact pow_dg (root_ne_zero h0 hc (h1 c hc).1 (h1 c hc).2.2.2)

def Ext (ι : (Fbar g)ˣ →* ℂˣ) (ω : Fbar g →*₀ ℂ) : Prop := ∀ u : (Fbar g)ˣ, ((ι u : ℂˣ) : ℂ) = ω u

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_ext {ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ}
    (hι : Function.Injective ι) :
    ∃ ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ, Function.Injective ω ∧ _root_.GlobalTheory.GoodCharsCompare.Ext ι ω := by
  classical
  let f : _root_.Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if h : x = 0 then 0 else ((ι (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((ι (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  refine ⟨ω, ?_, ?_⟩
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have := hι (Units.ext hab)
      simpa using congrArg Units.val this
  · intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]

theorem label_iff {ι : (Fbar g)ˣ →* ℂˣ} {ω : Fbar g →*₀ ℂ} (he : Ext ι ω) (θ : (ZMod g)ˣ → ℂ) (a : (ZMod g)ˣ) :
    IsCharLabel ι θ a ↔ IsTameLabel ω θ a := by
  unfold IsCharLabel IsTameLabel
  simp only [he _, rootOfOne_eq, Units.coe_map, MonoidHom.coe_coe]
  constructor
  · intro h z
    obtain ⟨m, hm⟩ := exists_log ω one_pos (unit_pow z)
    rw [h z m hm, labelChar_eq ω one_pos (unit_pow a) hm]
  · intro h z m hm
    rw [h z, labelChar_eq ω one_pos (unit_pow a) hm]

theorem label_unique {ω : Fbar g →*₀ ℂ} (hω : Function.Injective ω) {θ : (ZMod g)ˣ → ℂ} {a a' : (ZMod g)ˣ}
    (h : IsTameLabel ω θ a) (h' : IsTameLabel ω θ a') : a = a' := by
  obtain ⟨y, hy, hy'⟩ := exists_preimage hω one_pos (rootC_prim (g := g) one_pos).pow_eq_one
  obtain ⟨z, rfl⟩ := exists_unit_of_pow hy
  have e := (h z).symm.trans (h' z)
  rw [← pow_one (rootC _)] at hy'
  rw [labelChar_eq ω one_pos (unit_pow a) hy', labelChar_eq ω one_pos (unit_pow a') hy', pow_one, pow_one] at e
  exact Units.ext ((algebraMap (ZMod g) (Fbar g)).injective (hω e))

theorem label_inv {ω : Fbar g →*₀ ℂ} {θ : (ZMod g)ˣ → ℂ} {a : (ZMod g)ˣ}
    (h : IsTameLabel ω θ a) : IsTameLabel ω (fun z => (θ z)⁻¹) a⁻¹ := by
  intro z
  obtain ⟨m, hm⟩ := exists_log ω one_pos (unit_pow z)
  show (θ z)⁻¹ = _
  rw [h z, labelChar_eq ω one_pos (unit_pow a) hm, labelChar_eq ω one_pos (unit_pow a⁻¹) hm,
    Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, inv_pow]

theorem exists_block {r : ℕ} (b : Fin r → ℕ) (y : ℕ → Fbar g)
    (hy : ∀ c ∈ Finset.univ.image b, y c ^ (g ^ Fintype.card {a : Fin r // b a = c} - 1) = 1) :
    ∃ p : blockTri (κ := ZMod g) b, ∀ c ∈ Finset.univ.image b,
      minpoly (ZMod g) (blkMat b c p) = minpoly (ZMod g) (y c) := by
  have h1 : ∀ c, ∃ M : Matrix {a : Fin r // b a = c} {a : Fin r // b a = c} (ZMod g),
      c ∈ Finset.univ.image b → minpoly (ZMod g) M = minpoly (ZMod g) (y c) := by
    intro c
    by_cases hc : c ∈ Finset.univ.image b
    · obtain ⟨M, hM⟩ := exists_matrix (card_blk_pos hc) (hy c hc)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose M hM using h1
  let A : Matrix (Fin r) (Fin r) (ZMod g) := fun i j => if h : b j = b i then M (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0
  have hA : A.BlockTriangular b := fun i j h => dif_neg (ne_of_lt h)
  have hB : ∀ c, A.toSquareBlock b c = M c := by
    intro c
    ext ⟨i, rfl⟩ ⟨j, hj⟩
    exact dif_pos hj
  have hdet : A.det ≠ 0 := by
    rw [hA.det]
    refine Finset.prod_ne_zero_iff.2 fun c hc => ?_
    obtain ⟨k, hk⟩ := charpoly_eq_pow _ (hM c hc)
    have hy0 : y c ≠ 0 := by
      intro h
      have := hy c hc
      rw [h, zero_pow (g_pow_sub_pos (card_blk_pos hc)).ne'] at this
      exact zero_ne_one this
    rw [hB, Matrix.det_eq_sign_charpoly_coeff, hk, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ (minpoly.coeff_zero_ne_zero (isInt _) hy0))
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, hA⟩, fun c hc => ?_⟩
  rw [← hM c hc, ← hB]
  rfl

theorem torus_coef_ne {d e : ℕ} (he : 0 < e) :
    ((-1 : ℂ) ^ (d - d / e) * ∏ i ∈ Finset.Ico 1 (d / e), ((g : ℂ) ^ (e * i) - 1)) ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (by simp)) (Finset.prod_ne_zero_iff.2 fun i hi => ?_)
  have h1 : 1 < g ^ (e * i) := Nat.one_lt_pow (Nat.mul_pos he (Finset.mem_Ico.1 hi).1).ne' (Fact.out : g.Prime).one_lt
  rw [sub_ne_zero]
  exact_mod_cast h1.ne'

def CuspidalCharacterFormula : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (ω : Fbar g →*₀ ℂ), Function.Injective ω → ∀ (r : ℕ) (b : Fin r → ℕ) (n : ℕ)
    (σ : Representation ℂ (blockTri (κ := ZMod g) b) (Fin n → ℂ)), IsCuspDatum b σ →
    ∃ x : ℕ → Fbar g, (∀ c ∈ Finset.univ.image b, x c ≠ 0 ∧
        (minpoly (ZMod g) (x c)).natDegree = Fintype.card {a : Fin r // b a = c}) ∧
      ∀ p, σ.character p = ∏ c ∈ Finset.univ.image b, cuspVal ω (x c) (blkMat b c p)

theorem typeChar_full_of_torus (H : CuspidalCharacterFormula) {ι : (Fbar g)ˣ →* ℂˣ} {ω : Fbar g →*₀ ℂ}
    (hω : Function.Injective ω) (he : Ext ι ω) {r : ℕ} {f : (ZMod g)[X]} {ch : GL (Fin r) (ZMod g) → ℂ}
    (h : IndefiniteRowSideFullHecke.TameCharacterTorusValues.IsTypeChar ι f ch) : IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar ω f ch := by
  classical
  obtain ⟨b, φ, n, σ, hL, rfl, h5⟩ := h
  obtain ⟨x₀, hx₀, hch⟩ := H g ω hω r b n σ hL.cusp
  refine ⟨b, φ, x₀, n, σ, fun c₀ hc₀ => ⟨hL.monic _ hc₀, hL.irred _ hc₀, by rw [hL.degree _ hc₀, blkSize_eq], ?_⟩,
    rfl, hL.cusp, hch, h5⟩
  have h1 : ∀ c, ∃ x : (Fbar g)ˣ, c ∈ Finset.univ.image b → φ c = minpoly (ZMod g) (x : Fbar g) := by
    intro c
    by_cases hc : c ∈ Finset.univ.image b
    · obtain ⟨x, hx⟩ := exists_minpoly (hL.monic c hc) (hL.irred c hc)
      have : x ≠ 0 := by
        rintro rfl
        exact hL.ne_X c hc (by rw [hx, minpoly.zero])
      exact ⟨Units.mk0 x this, fun _ => hx⟩
    · exact ⟨1, fun h => absurd h hc⟩
  choose x hx using h1
  have hxp : ∀ c ∈ Finset.univ.image b, (x c : Fbar g) ^ (g ^ Fintype.card {a : Fin r // b a = c} - 1) = 1 := by
    intro c hc
    rw [← blkSize_eq, ← hL.degree c hc, hx c hc]
    exact pow_dg (x c).ne_zero
  have hx₀p : ∀ c ∈ Finset.univ.image b, x₀ c ^ (g ^ Fintype.card {a : Fin r // b a = c} - 1) = 1 := by
    intro c hc
    rw [← (hx₀ c hc).2]
    exact pow_dg (hx₀ c hc).1
  have hd := card_blk_pos hc₀
  obtain ⟨j, hj⟩ := mem_orbit_of_sums (g := g) (z := ω (x c₀)) (w := ω (x₀ c₀)) hd (by
    intro m₀
    obtain ⟨y₀, hy₀, hy₀'⟩ := exists_preimage hω hd (z := rootC (g ^ Fintype.card {a : Fin r // b a = c₀} - 1) ^ m₀)
      (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := g) hd).pow_eq_one, one_pow])
    have hy00 : y₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow (g_pow_sub_pos hd).ne'] at hy₀
      exact zero_ne_one hy₀
    let y : ℕ → (Fbar g)ˣ := fun c => if c = c₀ then Units.mk0 y₀ hy00 else 1
    let m : ℕ → ℕ := fun c => if c = c₀ then m₀ else 0
    have hm : ∀ c, ω (y c) = rootC (g ^ Fintype.card {a : Fin r // b a = c} - 1) ^ m c := by
      intro c
      by_cases hc : c = c₀
      · subst hc
        simpa [y, m] using hy₀'
      · simp [y, m, hc]
    obtain ⟨p, hp⟩ := exists_block b (fun c => (y c : Fbar g)) (by
      intro c _
      by_cases hc : c = c₀
      · subst hc
        simpa [y] using hy₀
      · simp [y, hc])
    have e1 := hL.value x y m p (fun c hc => by rw [hx c hc]; exact minpoly.aeval _ _) hp
      (fun c _ => by rw [he, hm, rootOfOne_eq, blkSize_eq])
    rw [hch, Finset.prod_congr rfl (fun c hc => cuspVal_eq_torusValue ω (card_blk_pos hc) _ (hx₀p c hc) (hp c hc) (hm c)),
      ← Finset.mul_prod_erase _ _ hc₀, ← Finset.mul_prod_erase _ _ hc₀] at e1
    simp only [blkSize_eq, he _] at e1
    have e2 : ∀ z : ℕ → ℂ, ∏ c ∈ (Finset.univ.image b).erase c₀,
        torusValue g (Fintype.card {a : Fin r // b a = c}) (dg (y c : Fbar g)) (z c) (m c) =
        ∏ c ∈ (Finset.univ.image b).erase c₀,
        torusValue g (Fintype.card {a : Fin r // b a = c}) (dg (y c : Fbar g)) 1 0 := by
      intro z
      refine Finset.prod_congr rfl fun c hc => ?_
      simp [torusValue, m, Finset.ne_of_mem_erase hc]
    rw [e2 (fun c => ω (x₀ c)), e2 (fun c => ω (x c))] at e1
    have e3 := mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun c _ => by
      refine mul_ne_zero (torus_coef_ne (dg_pos _)) ?_
      simpa using (dg_pos _).ne') e1
    have e4 := mul_left_cancel₀ (torus_coef_ne (dg_pos _)) e3
    have hyc : (y c₀ : Fbar g) = y₀ := by simp [y]
    have hmc : m c₀ = m₀ := by simp [m]
    rw [hyc, hmc] at e4
    obtain ⟨k, hk⟩ := exists_dg_mul hd hy₀
    have s1 := sum_period (period_of ω hd (hxp _ hc₀) hy₀') k
    have s2 := sum_period (period_of ω hd (hx₀p _ hc₀) hy₀') k
    rw [← hk] at s1 s2
    rw [s1, s2, e4])
  rw [hx _ hc₀]
  exact mem_roots_minpoly.2 ⟨j, hω (by rw [hj, map_pow])⟩

end GlobalTheory.GoodCharsCompare
end
end
