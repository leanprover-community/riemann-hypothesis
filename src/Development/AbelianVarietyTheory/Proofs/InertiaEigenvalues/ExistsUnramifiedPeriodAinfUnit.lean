import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiltRootOfUnity

section
namespace GlobalTheory.ProofStatement

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.ProofStatement
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_pow_eq_one_of_algClosure_zmod (l : ℕ) [hl : Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  first
  | exact @_root_.GlobalTheory.ProofStatement.main
  | exact _root_.GlobalTheory.ProofStatement.main
  | (apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProofStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProofStatement.main ..)

theorem exists_isPrimitiveRoot_tilt (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ e : Per.Fl l, IsPrimitiveRoot e m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  obtain ⟨e, he, hex⟩ := exists_tilt_root_of_unity l x m hm hlm hx.pow_eq_one
  refine ⟨e, he, fun d hd => hx.dvd_of_pow_eq_one d ?_⟩
  have h1 : e.untilt ^ d = 1 := by rw [← map_pow, hd, map_one]
  have h2 : (x : ℂ_[l]) ^ d = 1 := by
    rw [← hex]
    exact_mod_cast congrArg Subtype.val h1
  apply (algebraMap (Om l) ℂ_[l]).injective
  rw [map_pow, map_one]
  exact h2

theorem nonempty_algClosure_zmod_to_tilt :
    ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  intro l hl
  haveI : IsDomain (Per.Fl l) := inferInstance
  haveI : CharP (Per.Fl l) l := inferInstance
  let Ω := AlgebraicClosure (FractionRing (Per.Fl l))
  let j : Per.Fl l →+* Ω :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).comp (algebraMap (Per.Fl l) (FractionRing (Per.Fl l)))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω l := charP_of_injective_ringHom hj l
  letI : Algebra (ZMod l) Ω := ZMod.algebra Ω l
  let f₀ : AlgebraicClosure (ZMod l) →ₐ[ZMod l] Ω := IsAlgClosed.lift
  have hr : ∀ a, (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a ∈ j.range := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    obtain ⟨m, hm, hlm, ham⟩ := exists_pow_eq_one_of_algClosure_zmod l a ha
    obtain ⟨e, he⟩ := exists_isPrimitiveRoot_tilt l m hm hlm
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := (he.map_of_injective hj).eq_pow_of_pow_eq_one
      (ξ := (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a) (by rw [← map_pow, ham, map_one])
    exact ⟨e ^ i, by rw [map_pow, hi]⟩
  let E : Per.Fl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  exact ⟨E.symm.toRingHom.comp ((f₀ : AlgebraicClosure (ZMod l) →+* Ω).codRestrict j.range hr)⟩

end GlobalTheory.Per
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closure_hom_tilt_field : ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  first | exact @GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | exact GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | (intros; apply GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem σC_root_of_unity {m n : ℕ} {g : GQ l} (hm : 0 < m) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n)
    {x : ℂ_[l]} (hx : x ^ m = 1) : Per.σC g x = x ^ n := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' := hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hx
  have h1 : (ζ ^ i) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (ζ ^ i)) = algebraMap (Om l) ℂ_[l] (g (ζ ^ i)) :=
    GlobalTheory.RingBasics.σC_coe g (ζ ^ i)
  rw [← map_pow, h2, hg _ h1, map_pow]

theorem tilt_root_eq_one {c : Per.Fl l} {m : ℕ} (hlm : ¬ l ∣ m) (hc : c ^ m = 1)
    (h0 : PreTilt.coeff 0 c = 1) : c = 1 := by
  have : IsDomain (Per.Fl l) := inferInstance
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, c ^ i) * (c - 1) = 0 := by rw [geom_sum_mul, hc, sub_self]
  have h2 : (∑ i ∈ Finset.range m, c ^ i) = 0 :=
    (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (PreTilt.coeff (O := Per.OC l) (p := l) 0) h2
  simp only [map_sum, map_pow, h0, one_pow, Finset.sum_const, Finset.card_range, map_zero,
    nsmul_eq_mul, mul_one] at h3
  exact hlm ((CharP.cast_eq_zero_iff _ l m).1 h3)

theorem tilt_root_inj {a b : Per.Fl l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : a.untilt = b.untilt) : a = b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hb' : b * b ^ k = 1 := by rw [← pow_succ', hb]
  have h0 : PreTilt.coeff 0 a = PreTilt.coeff 0 b := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, ← PreTilt.mk_untilt_eq_coeff_zero, h]
  have h1 : a * b ^ k = 1 := by
    refine tilt_root_eq_one hlm ?_ ?_
    · rw [mul_pow, ha, ← pow_mul, mul_comm k, pow_mul, hb, one_pow, one_mul]
    · rw [map_mul, h0, ← map_mul, hb', map_one]
  calc a = a * (b * b ^ k) := by rw [hb', mul_one]
    _ = (a * b ^ k) * b := by ring
    _ = b := by rw [h1, one_mul]

theorem σF_root_of_unity (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l) (hm : 0 < m)
    (hlm : ¬ l ∣ m) (he : e ^ m = 1) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n) :
    Per.σF g e = e ^ n := by
  refine tilt_root_inj hm hlm ?_ ?_ ?_
  · rw [← map_pow, he, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · rw [GlobalTheory.RingBasics.untilt_σF, map_pow]
    have h1 : e.untilt ^ m = 1 := by rw [← map_pow, he, map_one]
    have h2 : ((e.untilt : Per.OC l) : ℂ_[l]) ^ m = 1 := by
      simpa using congrArg Subtype.val h1
    exact Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g _).trans
      ((σC_root_of_unity hm hg h2).trans (by simp)))

end GlobalTheory.MemLoc
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_galois_action_root_of_unity_coprime : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l), 0 < m → ¬ l ∣ m → e ^ m = 1 → (∀ x : Om l, x ^ m = 1 → g x = x ^ n) → Per.σF g e = e ^ n := by
  atlas_forward_decl GlobalTheory.MemLoc.σF_root_of_unity
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_pow_eq_one_algClosure_coprime (l : ℕ) [Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  have hint : IsIntegral (ZMod l) a := Algebra.IsIntegral.isIntegral a
  let K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l)))
  haveI : FiniteDimensional (ZMod l) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  let b : K := ⟨a, IntermediateField.mem_adjoin_simple_self _ a⟩
  have hb : b ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · intro hd
    have h0 : ((Fintype.card K - 1 : ℕ) : K) = 0 := by
      obtain ⟨c, hc⟩ := hd
      have hl : ((l : ℕ) : K) = 0 := by
        rw [← map_natCast (algebraMap (ZMod l) K), ZMod.natCast_self, map_zero]
      rw [hc, Nat.cast_mul, hl, zero_mul]
    rw [Nat.cast_sub h1.le, FiniteField.cast_card_eq_zero] at h0
    simp at h0
  · have := congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one b hb)
    simpa [b] using this

theorem exists_unit_frobenius_eq_mul (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [IsAlgClosed k]
    (u : WittVector l k) (hu : IsUnit u) :
    ∃ w : WittVector l k, IsUnit w ∧ WittVector.frobenius w = u * w := by
  have h1 : (1 : WittVector l k).coeff 0 ≠ 0 := by simp
  have h2 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := k))).ne_zero
  refine ⟨WittVector.frobeniusRotation l h1 h2, ?_, ?_⟩
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    simpa [WittVector.frobeniusRotation, WittVector.frobeniusRotationCoeff] using
      WittVector.RecursionBase.solution_nonzero l h1 h2
  · have := WittVector.frobenius_frobeniusRotation l h1 h2
    rwa [mul_one, mul_comm] at this

private theorem padicInt_ringHom_ext (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  refine sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : R)}) R) _ fun n => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = c * (l : ℤ_[l]) ^ n + (x.appr n : ℤ_[l]) := by rw [hc]; ring
  have h : f x - g x = (f c - g c) * (l : R) ^ n := by
    rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  intro l _ F hF u
  obtain ⟨f⟩ := GlobalTheory.T.nonempty_closure_hom_tilt_field l
  let u' : WittVector l (AlgebraicClosure (ZMod l)) :=
    WittVector.map (ZMod.castHom (dvd_refl l) _) (WittVector.fromPadicInt l u)
  have hu' : IsUnit u' := (u.isUnit.map _).map _
  obtain ⟨w₀, hw₀, hφ⟩ := exists_unit_frobenius_eq_mul l _ u' hu'
  have hfu : WittVector.map f u' = Per.zA l u := by
    exact RingHom.congr_fun (padicInt_ringHom_ext l (R := Per.Ainf l)
      ((WittVector.map f).comp ((WittVector.map (ZMod.castHom (dvd_refl l) _)).comp
        (WittVector.fromPadicInt l))) (Per.zA l)) u
  have hact : ∀ (g : GQ l) (n : ℕ), n ≠ 0 →
      (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → g x = x ^ n) →
      ∀ a, Per.σF g (f a) = f a ^ n := by
    intro g n hn hg a
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero, zero_pow hn]
    · obtain ⟨m, hm, hl, ham⟩ := exists_pow_eq_one_algClosure_coprime l a ha
      exact GlobalTheory.T.tilt_galois_action_root_of_unity_coprime l (f a) m n g hm hl (by rw [← map_pow, ham, map_one])
        fun x hx => hg x m hm hl hx
  have hφA : Per.φA l (WittVector.map f w₀) = Per.zA l u * WittVector.map f w₀ := by
    rw [← hfu, ← map_mul, ← hφ]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.phiA_coeff]
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]
  refine ⟨WittVector.map f w₀, hw₀.map _, fun g hg => ?_, ?_, hφA⟩
  · refine WittVector.ext fun n => ?_
    have := hact g 1 one_ne_zero (fun x m hm hl hx => by
      rw [pow_one]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
        (IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, hx⟩)) (w₀.coeff n)
    rw [pow_one] at this
    rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff]
    exact this
  · rw [← hφA]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff]
    exact hact F l (Fact.out : l.Prime).ne_zero hF (w₀.coeff n)

end GlobalTheory.MemLoc
end
