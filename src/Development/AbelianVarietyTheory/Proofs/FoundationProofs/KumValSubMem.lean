import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqTrue
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataCyclotomicAlgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImage

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycDvd

theorem apply_eq_pow (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t ^ ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
    simp [cycMod, cycZ]
  rw [h2] at h1
  exact h1

theorem exists_Ine_apply_eq (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) {z μ : Ω} (hz : IsPrimitiveRoot z (l ^ n))
    (hμ : IsPrimitiveRoot μ (l ^ n)) : ∃ s ∈ Ine (F := ℚ) A, s z = μ := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨i, hi, hcop, rfl⟩ := (hz.isPrimitiveRoot_iff).1 hμ
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)
  refine ⟨s, hs, ?_⟩
  have hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop := hsu
  rw [apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

theorem cyclotomic_dvd : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  intro l _ Ω _ _ _ A hO n z hz R hR
  classical
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hl⟩ := hO
    have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
    simpa using h1
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  let f : fixA A →+* Ω := A.subtype.comp (fixA A).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have h0 : Polynomial.eval₂ f (z : Ω) R = 0 := by
    have := Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z
    rw [← Polynomial.aeval_def, hR, map_zero] at this
    exact this.symm
  have hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0 := by
    intro μ hμ
    obtain ⟨s, hs, rfl⟩ := exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)
    have e := Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)
    have e2 : (s : Ω →+* Ω).comp f = f := RingHom.ext fun a => a.2 s hs
    rw [h0, map_zero, e2] at e
    rw [Polynomial.eval_map]
    exact e.symm
  rw [← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
  · intro μ hμ
    exact Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)

end GlobalTheory.RecOne.CycDvd
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  first | (exact @GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (exact GlobalTheory.RecOne.CycDvd.cyclotomic_dvd) | (intros; apply GlobalTheory.RecOne.CycDvd.cyclotomic_dvd  <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne.ZetaDer

open Polynomial

section Gen
variable {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]

theorem exists_der_one (z : S) (μ : M)
    (hwd : ∀ Q : R[X], aeval z Q = 0 → aeval z (derivative Q) • μ = 0) :
    ∃ D : S → M, IsDerOn (Algebra.adjoin R {z}) D ∧ D z = μ := by
  classical
  let e : R[X] → S := fun Q => aeval z Q
  let D : S → M := fun x => aeval z (derivative (Function.invFun e x)) • μ
  have key : ∀ f : R[X], D (aeval z f) = aeval z (derivative f) • μ := by
    intro f
    have h1 : e (Function.invFun e (e f)) = e f := Function.invFun_eq ⟨f, rfl⟩
    have h2 := hwd (Function.invFun e (e f) - f) (by rw [map_sub]; exact sub_eq_zero.2 h1)
    rw [derivative_sub, map_sub, sub_smul, sub_eq_zero] at h2
    exact h2
  have hm : ∀ x ∈ Algebra.adjoin R {z}, ∃ f : R[X], aeval z f = x := by
    intro x hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact hx
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_add, key, key, key, derivative_add, map_add, add_smul]
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := hm x hx
    obtain ⟨g, rfl⟩ := hm y hy
    rw [← map_mul, key, key, key, derivative_mul, map_add, add_smul, map_mul, map_mul, smul_smul, smul_smul,
      add_comm, mul_comm (aeval z (derivative f))]
  · intro a
    have : algebraMap R S a = aeval z (C a) := by simp
    rw [this, key]
    simp
  · have : z = aeval z (X : R[X]) := by simp
    conv_lhs => rw [this]
    rw [key]
    simp

end Gen

variable {Ω : Type} [Field Ω]

theorem frac_smul_mk {A : ValuationSubring Ω} (s : A) (x : Ω) :
    s • (Submodule.Quotient.mk x : FracA A) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero {A : ValuationSubring Ω} (s : A) :
    (Submodule.Quotient.mk (s : Ω) : FracA A) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_rel [CharZero Ω] {p : ℕ} [hp : Fact p.Prime] {A : ValuationSubring Ω} {R : Type} [CommRing R] [Algebra R A]
    (m : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ (m + 1))) :
    (aeval z (derivative (cyclotomic (p ^ (m + 1)) R))) •
      (Submodule.Quotient.mk ((z : Ω) * p / (p : Ω) ^ (m + 1)) : FracA A) = 0 := by
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hzA : IsPrimitiveRoot z (p ^ (m + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := A.subtype) hz Subtype.val_injective
  have hξ : IsPrimitiveRoot ((z : Ω) ^ p ^ m) p := by
    have := hz.pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this
  set gS : A := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ((z : Ω) ^ p ^ m) ^ j := by
    simp [gS]
  have hg : (gS : Ω) * ((z : Ω) ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp
  have hroot : aeval z (cyclotomic (p ^ (m + 1)) R) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hzA.isRoot_cyclotomic hpos
  have hid := congrArg (fun f => aeval z (derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one R p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add, map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  rw [frac_smul_mk]
  set F := aeval z (derivative (cyclotomic (p ^ (m + 1)) R))
  have hζ1 : (z : Ω) ^ p ^ (m + 1) = 1 := hz.pow_eq_one
  have hF : (F : Ω) * ((z : Ω) ^ p ^ m - 1) * z = (p : Ω) ^ (m + 1) := by
    have h2 : F * (z ^ p ^ m - 1) = (p : A) ^ (m + 1) * z ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    have h3 : (F : Ω) * ((z : Ω) ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * (z : Ω) ^ (p ^ (m + 1) - 1) := by
      have := congrArg (A.subtype) h2
      simpa using this
    rw [h3, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : (z : Ω) ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : (F : Ω) * ((z : Ω) * p / (p : Ω) ^ (m + 1)) = ((-gS : A) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

theorem exists_root_succ [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (n : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ n)) :
    ∃ w : A, IsPrimitiveRoot (w : Ω) (p ^ (n + 1)) ∧ w ^ p = z := by
  have hpos : 0 < p ^ (n + 1) := pow_pos hp.out.pos _
  haveI : NeZero (p ^ (n + 1)) := ⟨hpos.ne'⟩
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos _).ne'⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : Ω) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (n + 1))
  have h1 : IsPrimitiveRoot (ζ ^ p) (p ^ n) := hζ.pow hpos (by rw [pow_succ'])
  obtain ⟨i, -, hi, hiz⟩ := h1.isPrimitiveRoot_iff.1 hz

  obtain ⟨j, hj, hjz⟩ : ∃ j : ℕ, j.Coprime (p ^ (n + 1)) ∧ (ζ ^ p) ^ j = z := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, Nat.coprime_one_left _, ?_⟩
      have a1 : ζ ^ p = 1 := by simpa using h1.pow_eq_one
      have a2 : (z : Ω) = 1 := by simpa using hz.pow_eq_one
      rw [a1, a2, one_pow]
    · refine ⟨i, ?_, hiz⟩
      rw [Nat.coprime_pow_right_iff hn] at hi
      exact hi.pow_right _
  have hw : IsPrimitiveRoot (ζ ^ j) (p ^ (n + 1)) := hζ.pow_of_coprime j hj
  have hmem : ζ ^ j ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hw.pow_eq_one]; exact A.one_mem)
  refine ⟨⟨ζ ^ j, hmem⟩, hw, Subtype.ext ?_⟩
  rw [← hjz]
  show (ζ ^ j) ^ p = _
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem exists_seq [CharZero Ω] [IsAlgClosed Ω] {p : ℕ} [hp : Fact p.Prime] (A : ValuationSubring Ω)
    (N : ℕ) (z : A) (hz : IsPrimitiveRoot (z : Ω) (p ^ N)) :
    ∃ zs : ℕ → A, zs 0 = z ∧ (∀ k, IsPrimitiveRoot (zs k : Ω) (p ^ (N + k))) ∧ ∀ k, zs (k + 1) ^ p = zs k := by
  choose f hf hf' using exists_root_succ (p := p) A
  let s : (k : ℕ) → {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))} := fun k =>
    Nat.rec (motive := fun k => {w : A // IsPrimitiveRoot (w : Ω) (p ^ (N + k))}) ⟨z, hz⟩
      (fun k w => ⟨f (N + k) w.1 w.2, hf (N + k) w.1 w.2⟩) k
  exact ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k => hf' (N + k) (s k).1 (s k).2⟩

end GlobalTheory.RecOne.ZetaDer

namespace GlobalTheory.RecOne

open ZetaDer Polynomial

theorem zeta_derivation_cyc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) →
    ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧
      D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  intro p hp Ω _ _ hc A hO N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨zs, hz0, hprim, hpow⟩ := exists_seq A N z hz
  let B : ℕ → Subalgebra (fixA A) A := fun m => Algebra.adjoin (fixA A) {zs (m + 1)}
  have hmem1 : ∀ m, zs (m + 1) ∈ B m := fun m => Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem0 : ∀ m, zs m ∈ B m := fun m => by rw [← hpow m]; exact pow_mem (hmem1 m) _
  have hle1 : ∀ m, B m ≤ B (m + 1) := fun m =>
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (hmem0 (m + 1)))
  have hlev : ∀ m : ℕ, ∃ D : A → FracA A, IsDerOn (B m) D ∧
      D (zs (m + 1)) = Submodule.Quotient.mk ((zs (m + 1) : Ω) * p / (p : Ω) ^ (N + m + 1)) := by
    intro m
    refine exists_der_one (zs (m + 1)) _ fun Q hQ => ?_
    obtain ⟨R, rfl⟩ := GlobalTheory.T.cyclotomic_dvd_of_aeval_primitive_root_inertia_fixed p Ω A hO (N + m + 1) (zs (m + 1)) (hprim (m + 1)) Q hQ
    have hzA : IsPrimitiveRoot (zs (m + 1)) (p ^ (N + m + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim (m + 1)) Subtype.val_injective
    have hroot : aeval (zs (m + 1)) (cyclotomic (p ^ (N + m + 1)) (fixA A)) = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
      exact hzA.isRoot_cyclotomic (pow_pos hp.out.pos _)
    rw [derivative_mul, map_add, map_mul, map_mul, hroot, zero_mul, add_zero, mul_comm, mul_smul,
      cyc_rel (N + m) (zs (m + 1)) (hprim (m + 1)), smul_zero]
  choose D hD hDz using hlev
  have hval : ∀ m, D m (zs m) = Submodule.Quotient.mk ((zs m : Ω) * p / (p : Ω) ^ (N + m)) := by
    intro m
    have hc1 : ((zs m : A) : Ω) = (zs (m + 1) : Ω) ^ p := by rw [← hpow m]; rfl
    rw [hc1]
    conv_lhs => rw [← hpow m]
    rw [(hD m).pow_der (hmem1 m) hp.out.pos, hDz m, ZetaDer.frac_smul_mk]
    congr 1
    push_cast
    rw [← pow_sub_one_mul hp.out.ne_zero (zs (m + 1) : Ω)]
    field_simp
    ring
  have hcompat : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zs (m + 1)}) ((hD (m + 1)).mono' (hle1 m)) (hD m) ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx, hval (m + 1), hDz m]
    rfl
  have hmono : Monotone B := monotone_nat_of_le_succ hle1
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (fixA A) A (FracA A) B hmono D hD hcompat
  have hle : cycAlg p A ≤ ⨆ m, B m := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨n, hx⟩
    haveI : NeZero (p ^ (N + n)) := ⟨(pow_pos hp.out.pos _).ne'⟩
    have hzA : IsPrimitiveRoot (zs n) (p ^ (N + n)) :=
      IsPrimitiveRoot.of_map_of_injective (f := A.subtype) (hprim n) Subtype.val_injective
    obtain ⟨i, -, rfl⟩ := hzA.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_add, mul_comm, pow_mul, hx, one_pow])
    exact (le_iSup B n) (pow_mem (hmem0 n) i)
  refine ⟨D', hD'.mono' hle, ?_⟩
  rw [← hz0, hD'eq 0 _ (hmem0 0), hval 0]
  rfl

end GlobalTheory.RecOne
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ D : A → FracA A, IsDerOn (cycAlg l A) D ∧ D z = Submodule.Quotient.mk ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
  first | (exact @GlobalTheory.RecOne.zeta_derivation_cyc) | (exact GlobalTheory.RecOne.zeta_derivation_cyc) | (intros; apply GlobalTheory.RecOne.zeta_derivation_cyc  <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem pow_four_mul_mem_of_smul_dA_eq_zero : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  intro l _ hl2 Ω _ _ _ A hA N z hz a hrel
  have hlΩ : (l : Ω) ≠ 0 := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hpos : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  have hz1 : (z : Ω) ^ (l ^ N) = 1 := hz.pow_eq_one
  have hzA : z ^ (l ^ N) = 1 := Subtype.ext (by simpa using hz1)
  have hzT : z ∈ cycAlg l A := mem_cycAlg_of_pow hzA
  have hrel' : ∑ i : Fin 1, (fun _ => a) i •
      KaehlerDifferential.D (fixA A) A ((fun _ => z) i) = 0 := by
    simpa using hrel
  obtain ⟨F, hF⟩ := kaehler_rel_local (fixA A) A 1 _ _ hrel'
  obtain ⟨C, tr, m, α, β, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA F
  obtain ⟨D, hD, hDv⟩ := GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra l Ω A hA N z hz
  obtain ⟨D', hD', hD'v⟩ := exists_derOn_ext (fixA A) A (FracA A) (cycAlg l A) C tr m α β _ htr D hD
  have h := hF C hFC (fun _ => htr.le hzT) (FracA A) D' hD'
  rw [Fin.sum_univ_one, hD'v _ hzT, hDv, smul_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  have ht' : (t : Ω) = (a : Ω) * (l : Ω) ^ 3 * ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
    simpa [Algebra.smul_def] using ht
  refine ⟨((t * z ^ (l ^ N - 1) : A) : Ω), (t * z ^ (l ^ N - 1)).2, ?_⟩
  have hzz : (z : Ω) * (z : Ω) ^ (l ^ N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, hz1]
  push_cast
  rw [ht']
  field_simp
  linear_combination (-((a : Ω))) * hzz

end GlobalTheory.RecOne
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  atlas_forward_decl GlobalTheory.RecOne.pow_four_mul_mem_of_smul_dA_eq_zero
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

section Gen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def evMul (l : ℕ) (A : ValuationSubring Ω) : Submodule A (KaehlerDifferential (fixA A) A) where
  carrier := {ω | ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) →
    ω ∈ Submodule.span A {dA A z}}
  add_mem' := by
    rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, fun N hN z hz =>
      add_mem (h₁ N (le_trans (le_max_left _ _) hN) z hz) (h₂ N (le_trans (le_max_right _ _) hN) z hz)⟩
  zero_mem' := ⟨0, fun _ _ _ _ => zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨N₁, h₁⟩
    exact ⟨N₁, fun N hN z hz => Submodule.smul_mem _ c (h₁ N hN z hz)⟩

theorem dA_mem_evMul (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) {x : A} {n : ℕ}
    (hx : x ^ (l ^ n) = 1) : dA A x ∈ evMul l A := by
  refine ⟨n, fun N hN z hz => ?_⟩
  have : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (x : Ω) ^ (l ^ N) = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h0 : (x : Ω) ^ (l ^ n) = 1 := by
      have := congrArg (fun t : A => (t : Ω)) hx
      simpa using this
    rw [pow_add, pow_mul, h0, one_pow]
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one h1
  have h2 : x = z ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hi]
  rw [h2, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Gen

theorem l_sq_smul_dA_eq_smul : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  intro l _ hl2 Ω _ _ _ A hA v
  have hder : ∀ B : Subalgebra (fixA A) A, IsDerOn B (fun x => dA A x) := fun B =>
    ⟨fun x _ y _ => map_add (dA A) x y, fun x _ y _ => Derivation.leibniz (dA A) x y,
      fun a => (dA A).map_algebraMap a⟩
  obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA {v}
  have h1 := GlobalTheory.AlmostEt.derOn_mem_span_of_trData (fixA A) A _ (cycAlg l A) C tr k a b _ htr
    (fun x => dA A x) (hder C) v (hF (by simp))
  have h2 : Submodule.span A ((fun x => dA A x) '' (cycAlg l A : Set A)) ≤ evMul l A := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h3 := GlobalTheory.AlmostEt.derOn_adjoin_mem_span (fixA A) A _ {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}
      (fun x => dA A x) (hder _) x hx
    refine Submodule.span_le.2 ?_ h3
    rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
    exact dA_mem_evMul l A hn
  obtain ⟨N₀, h⟩ := h2 h1
  refine ⟨N₀, fun N hN z hz => ?_⟩
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.1 (h N hN z hz)
  exact ⟨y, by rw [pow_two]; exact hy.symm⟩

end GlobalTheory.RecOne
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  atlas_forward_decl GlobalTheory.RecOne.l_sq_smul_dA_eq_smul
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

noncomputable section

namespace GlobalTheory.RecOne

def decRingHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω)
    (hs : s ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨s x, (apply_mem_iff_of_mem_Dec hs (x : Ω)).2 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def TwDiff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (_τ : A →+* A) : Type :=
  KaehlerDifferential (fixA A) A

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    AddCommGroup (TwDiff A τ) :=
  inferInstanceAs (AddCommGroup (KaehlerDifferential (fixA A) A))

instance {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : A →+* A) :
    Module A (TwDiff A τ) :=
  Module.compHom (KaehlerDifferential (fixA A) A) τ

theorem transp_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω),
    s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b →
    (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  intro Ω _ _ A s hs a b a' b' c d c' d' hc hd hc' hd' h
  set τ := decRingHom A s (Ine_le_Dec A hs) with hτ
  have hτc : τ a = c := Subtype.ext hc.symm
  have hτd : τ b = d := Subtype.ext hd.symm
  have hτc' : τ a' = c' := Subtype.ext hc'.symm
  have hτd' : τ b' = d' := Subtype.ext hd'.symm
  obtain ⟨T, hT⟩ := kaehler_rel_local (fixA A) A 2 ![a, -a'] ![b, b']
    (by simp [Fin.sum_univ_two, h])
  let D : A → TwDiff A τ := fun x => (dA A (τ x) : KaehlerDifferential (fixA A) A)
  have hD : IsDerOn (⊤ : Subalgebra (fixA A) A) D :=
    { add := fun x _ y _ => by
        show dA A (τ (x + y)) = dA A (τ x) + dA A (τ y)
        rw [map_add, map_add]
      mul := fun x _ y _ => by
        show dA A (τ (x * y)) = τ x • dA A (τ y) + τ y • dA A (τ x)
        rw [map_mul, Derivation.leibniz]
      alg := fun r => by
        show dA A (τ (algebraMap (fixA A) A r)) = 0
        have e : τ (algebraMap (fixA A) A r) = algebraMap (fixA A) A r :=
          Subtype.ext (r.2 s hs)
        rw [e, Derivation.map_algebraMap] }
  have key := hT ⊤ (by simp) (by simp) (TwDiff A τ) D hD
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
  change τ a • dA A (τ b) + τ (-a') • dA A (τ b') = (0 : KaehlerDifferential (fixA A) A) at key
  rw [map_neg, hτc, hτd, hτc', hτd', neg_smul, ← sub_eq_add_neg, sub_eq_zero] at key
  exact key

end GlobalTheory.RecOne
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (s : G ℚ Ω), s ∈ Ine (F := ℚ) A → ∀ a b a' b' c d c' d' : A, (c : Ω) = s a → (d : Ω) = s b → (c' : Ω) = s a' → (d' : Ω) = s b' → a • dA A b = a' • dA A b' → c • dA A d = c' • dA A d' := by
  first | (exact @GlobalTheory.RecOne.transp_rel) | (exact GlobalTheory.RecOne.transp_rel) | (intros; apply GlobalTheory.RecOne.transp_rel  <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecOne

section Der

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]

theorem smul_der_pow (d : Derivation R S M) (x : S) (n : ℕ) : x • d (x ^ n) = ((n : S) * x ^ n) • d x := by
  rcases n with _ | n
  · simp
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    rw [Nat.add_sub_cancel]; ring

theorem rel_one (d : Derivation R S M) (e V Z p y : S) (L n : ℕ) (h1 : e • d V = y • d Z)
    (h2 : d (V ^ L) = p • d (Z ^ n)) :
    ((L : S) * V ^ L * Z * y - e * V * p * n * Z ^ n) • d Z = 0 := by
  have a1 := smul_der_pow d V L
  have a2 := smul_der_pow d Z n
  linear_combination (norm := module) (-((L : S) * V ^ L * Z)) • h1 - (e * Z) • a1 + (e * Z * V) • h2 +
    (e * V * p) • a2

theorem rel_two (d : Derivation R S M) (e V Z y y' : S) (n k c : ℕ) (h1 : e • d V = y • d Z)
    (h2 : e • d ((Z ^ n) ^ k * V) = y' • d (Z ^ c)) :
    (y' * c * Z ^ c - Z * (Z ^ n) ^ k * y - e * V * k * n * (Z ^ n) ^ k) • d Z = 0 := by
  have a1 := smul_der_pow d Z c
  have a2 := smul_der_pow d Z (n * k)
  rw [pow_mul, Nat.cast_mul] at a2
  rw [Derivation.leibniz] at h2
  linear_combination (norm := module) (Z * (Z ^ n) ^ k) • h1 - y' • a1 - Z • h2 + (e * V) • a2

end Der

theorem field_step {F : Type*} [Field F] (l L α u V Z ζ K p y y' Z' w w' w₂ k t c e : F) (hL : L ≠ 0) (hα : α ≠ 0)
    (hu : u ≠ 0) (hV : V ≠ 0) (hK : K ≠ 0)
    (h1 : l ^ 4 * (L * u * Z * y - l ^ 2 * V * p * (α * L) * ζ) = α * L * L * w)
    (h1' : l ^ 4 * (L * u * Z' * y' - l ^ 2 * (K * V) * p * (α * L) * ζ) = α * L * L * w')
    (h2 : l ^ 4 * (y' * c * Z' - Z * K * y - l ^ 2 * V * k * (α * L) * K) = α * L * L * w₂)
    (hc : c = 1 + t * L + e * L * L) :
    l ^ 6 * k - (l ^ 6 * (t * (ζ * p / u)) + (w' * u⁻¹ * (K * V)⁻¹ - w * u⁻¹ * V⁻¹)) =
      L * (l ^ 6 * e * (ζ * p * u⁻¹) + (t + e * L) * (w' * u⁻¹ * (K⁻¹ * V⁻¹)) - w₂ * (K⁻¹ * V⁻¹)) := by
  have h3 : (α * L * L) * (l ^ 6 * k * u * K * V - l ^ 6 * t * ζ * p * K * V - w' + w * K) =
      (α * L * L) * (L * (l ^ 6 * e * ζ * p * K * V + (t + e * L) * w' - w₂ * u)) := by
    subst hc
    linear_combination (-(L * u)) * h2 + (1 + t * L + e * L * L) * h1' - K * h1
  have h4 := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hα hL) hL) h3
  field_simp
  linear_combination h4

theorem kummer_eq_dlog_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  intro l hl hl2
  refine ⟨6, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hu hu' hu0
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hpos : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hlp.pos j
  haveI : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨(hpos j).ne'⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, A.zero_mem, fun s _ _ k t _ _ => ⟨0, A.zero_mem, ?_⟩⟩
    have hk : k.val = 0 := by have := ZMod.val_lt k; simpa using this
    have ht : t.val = 0 := by have := ZMod.val_lt t; simpa using this
    rw [hk, ht]; simp
  set φ : fixA A →+* Ω := A.subtype.comp (fixA A).subtype with hφ
  obtain ⟨Q, rfl⟩ : ∃ Q : Polynomial (fixA A), Q.map φ = P := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h0 : P.coeff n = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨h1, h2⟩ := hP _ (Polynomial.coeff_mem_coeffs h0)
      exact ⟨⟨⟨P.coeff n, h1⟩, h2⟩, rfl⟩
  have hev : ∀ (R : Polynomial (fixA A)) (x : A), ((Polynomial.aeval x R : A) : Ω) = (R.map φ).eval (x : Ω) := by
    intro R x
    rw [Polynomial.eval_map, Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype x
  have hsev : ∀ s ∈ Ine (F := ℚ) A, ∀ (R : Polynomial (fixA A)) (x : Ω),
      s ((R.map φ).eval x) = (R.map φ).eval (s x) := by
    intro s hs R x
    rw [Polynomial.eval_map, Polynomial.eval_map]
    have h := Polynomial.hom_eval₂ R φ (s : Ω →+* Ω) x
    have e : (s : Ω →+* Ω).comp φ = φ := RingHom.ext fun a => a.2 s hs
    rw [e] at h
    exact h
  rw [Polynomial.derivative_map]
  set u := (Q.map φ).eval ζ with hudef
  set p := ((Polynomial.derivative Q).map φ).eval ζ with hpdef
  obtain ⟨V, hV⟩ := IsAlgClosed.exists_pow_nat_eq u (hpos m)
  have hV0 : V ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hV, zero_pow (hpos m).ne'])
  have hVA : V ∈ A := mem_of_pow_mem A (hpos m).ne' (hV ▸ hu)
  have hVA' : V⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hV]; exact hu')
  obtain ⟨α, hα⟩ := GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity l hl2 Ω A hA ⟨V, hVA⟩
  obtain ⟨Z, hZ⟩ := IsAlgClosed.exists_pow_nat_eq ζ' (hpos α)
  have hZζ : Z ^ l ^ (α + m) = ζ := by rw [pow_add, pow_mul, hZ, hζ']
  have hZp : IsPrimitiveRoot Z (l ^ (α + m + m)) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : ¬ Z ^ l ^ (α + (m' + 1) + m') = 1 := by
      rw [pow_add, pow_mul, hZζ]
      exact hζ.pow_ne_one_of_pos_of_lt (hpos m').ne' (Nat.pow_lt_pow_right hlp.one_lt (by omega))
    have h2 : Z ^ l ^ (α + (m' + 1) + m' + 1) = 1 := by
      rw [add_assoc (α + (m' + 1)), pow_add, pow_mul, hZζ, hζ.pow_eq_one]
    have h3 := orderOf_eq_prime_pow h1 h2
    have h4 := IsPrimitiveRoot.orderOf Z
    rwa [h3] at h4
  have hZA : Z ∈ A := mem_of_pow_mem A (hpos (α + m + m)).ne' (by rw [hZp.pow_eq_one]; exact A.one_mem)
  have hζA : ζ ∈ A := hZζ ▸ pow_mem hZA _
  have hζA' : ζ⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hζ.pow_eq_one, inv_one]; exact A.one_mem)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (hpos m).ne'
  set VA : A := ⟨V, hVA⟩
  set ZA : A := ⟨Z, hZA⟩
  obtain ⟨y, hy⟩ := hα (α + m + m) (by omega) ZA hZp
  have hZAζ : ((ZA ^ l ^ (α + m) : A) : Ω) = ζ := by simpa using hZζ
  set pA : A := Polynomial.aeval (ZA ^ l ^ (α + m)) (Polynomial.derivative Q) with hpA
  have hpAp : (pA : Ω) = p := by rw [hpA, hev, hZAζ]
  have hpmem : p ∈ A := hpAp ▸ pA.2
  have hVu : VA ^ l ^ m = Polynomial.aeval (ZA ^ l ^ (α + m)) Q := by
    apply Subtype.ext
    rw [hev, hZAζ]
    simpa using hV
  have hd : dA A (VA ^ l ^ m) = pA • dA A (ZA ^ l ^ (α + m)) := by
    rw [hVu, Derivation.map_aeval]
  obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_one (dA A) _ VA ZA pA y _ _ hy hd)
  have hw1 : (l : Ω) ^ 4 * ((l : Ω) ^ m * u * Z * y - (l : Ω) ^ 2 * V * p * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w := by
    rw [← hV, ← hpAp, ← hZζ, ← pow_add, ← pow_add, ← hw]
    push_cast
    rfl
  refine ⟨w * u⁻¹ * V⁻¹, mul_mem (mul_mem hwA hu') hVA', ?_⟩
  rintro s hs hcyc k t ⟨v, hv, hsv⟩ hst
  have hsA : ∀ x ∈ A, s x ∈ A := fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).2 hx
  have hsζ : s ζ = ζ := GlobalTheory.Col.fix_of_cycMod le_rfl hcyc hζ.pow_eq_one
  have hsu : s u = u := by rw [hudef, hsev s hs, hsζ]
  have hsp : s p = p := by rw [hpdef, hsev s hs, hsζ]
  have hsV : s V = ζ ^ k.val * V := by
    have h1 : (v / V) ^ l ^ m = 1 := by rw [div_pow, hv, hV, div_self hu0]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
    have h2 : v = ζ ^ j * V := by rw [hj]; field_simp
    rw [h2, map_mul, map_pow, hsζ] at hsv
    exact mul_left_cancel₀ (pow_ne_zero j hζ0) (by rw [hsv]; ring)
  obtain ⟨c, -, hc⟩ := hZp.eq_pow_of_pow_eq_one (ξ := s Z) (by rw [← map_pow, hZp.pow_eq_one, map_one])
  have htr := GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants Ω A s hs ((l : A) ^ 2) VA y ZA ((l : A) ^ 2) ((ZA ^ l ^ (α + m)) ^ k.val * VA)
    ⟨s y, hsA _ y.2⟩ (ZA ^ c) (by simp) (by push_cast; rw [hZζ]; exact hsV.symm) rfl (by simpa using hc) hy
  obtain ⟨w₂, hw₂A, hw₂⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_two (dA A) _ VA ZA y _ _ _ _ hy htr)
  have hw2 : (l : Ω) ^ 4 * (s y * (c : Ω) * s Z - Z * ζ ^ k.val * y -
      (l : Ω) ^ 2 * V * (k.val : Ω) * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ ^ k.val) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w₂ := by
    rw [← hc, ← hZζ, ← pow_add, ← pow_add, ← hw₂]
    push_cast
    rfl
  have hw1' := congrArg s hw1
  simp only [map_mul, map_sub, map_pow, map_natCast, hsu, hsp, hsζ, hsV] at hw1'
  obtain ⟨e, he⟩ : ∃ e : ℤ, (c : Ω) = 1 + (t.val : Ω) * (l : Ω) ^ m + (e : Ω) * (l : Ω) ^ m * (l : Ω) ^ m := by
    have h1 : Z ^ (c * l ^ α) = Z ^ (l ^ (α + m) * t.val + l ^ α) := by
      rw [pow_mul, hc, ← map_pow, hZ, hst, pow_add, pow_mul, hZζ, hZ]
    rw [(hZp.isOfFinOrder (hpos _).ne').pow_eq_pow_iff_modEq, ← hZp.eq_orderOf, Nat.modEq_iff_dvd] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨-e, ?_⟩
    have h2 := congrArg (Int.cast : ℤ → Ω) he
    push_cast at h2
    apply mul_left_cancel₀ (pow_ne_zero α hl0)
    push_cast
    linear_combination -h2
  have hfin := field_step (l : Ω) ((l : Ω) ^ m) ((l : Ω) ^ α) u V Z ζ (ζ ^ k.val) p y (s y) (s Z) w (s w) w₂
    (k.val : Ω) (t.val : Ω) (c : Ω) (e : Ω) (pow_ne_zero _ hl0) (pow_ne_zero _ hl0) hu0 hV0 (pow_ne_zero _ hζ0)
    hw1 hw1' hw2 he
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hKV : (ζ ^ k.val)⁻¹ * V⁻¹ ∈ A := mul_mem (by rw [← inv_pow]; exact pow_mem hζA' _) hVA'
  refine ⟨_, ?_, by rw [map_mul, map_mul, map_inv₀, map_inv₀, hsu, hsV]; exact hfin⟩
  refine sub_mem (add_mem (mul_mem (mul_mem (pow_mem hlA _) (intCast_mem A e)) (mul_mem (mul_mem hζA hpmem) hu'))
    (mul_mem (add_mem (natCast_mem A _) (mul_mem (intCast_mem A e) (pow_mem hlA _)))
      (mul_mem (mul_mem (hsA w hwA) hu') hKV))) (mul_mem hw₂A hKV)

end GlobalTheory.RecOne
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  atlas_forward_decl GlobalTheory.RecOne.kummer_eq_dlog_one
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecConj

open Polynomial

theorem apply_root {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {m : ℕ} (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ m) = 1) : s t = t ^ (cycMod ℚ Ω l m s : ZMod (l ^ m)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht

theorem nat_cg {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {L a b : ℕ} (h : (a : ZMod L) = (b : ZMod L)) :
    ∃ z ∈ A, (a : Ω) - b = (L : Ω) * z := by
  obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff a b L).1 h).symm
  refine ⟨(q : Ω), intCast_mem A q, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hq
  push_cast at this
  exact this

def fixSub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) : Subring Ω where
  carrier := {x | x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x}
  mul_mem' := fun ha hb => ⟨A.mul_mem _ _ ha.1 hb.1, fun s hs => by rw [map_mul, ha.2 s hs, hb.2 s hs]⟩
  one_mem' := ⟨A.one_mem, fun s _ => map_one s⟩
  add_mem' := fun ha hb => ⟨A.add_mem _ _ ha.1 hb.1, fun s hs => by rw [map_add, ha.2 s hs, hb.2 s hs]⟩
  zero_mem' := ⟨A.zero_mem, fun s _ => map_zero s⟩
  neg_mem' := fun ha => ⟨A.neg_mem _ ha.1, fun s hs => by rw [map_neg, ha.2 s hs]⟩

theorem eval_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P : Polynomial Ω) (hP : ∀ i, P.coeff i ∈ A) {y : Ω}
    (hy : y ∈ A) : P.eval y ∈ A := by
  rw [eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hP i) (pow_mem hy i)

theorem recip_conj : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∀ (τ : G ℚ Ω) (b : (ZMod (l ^ m))ˣ), τ ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m τ = b⁻¹ →
  ∃ x ∈ A, ζ ^ (b : ZMod (l ^ m)).val * (Polynomial.derivative P).eval (ζ ^ (b : ZMod (l ^ m)).val) / P.eval (ζ ^ (b : ZMod (l ^ m)).val) ∈ A ∧
    ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) (τ * s * τ⁻¹) k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ ^ (b : ZMod (l ^ m)).val * (Polynomial.derivative P).eval (ζ ^ (b : ZMod (l ^ m)).val) / P.eval (ζ ^ (b : ZMod (l ^ m)).val))) + (s x - x)) := by
  intro l _ hl
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity l hl
  refine ⟨c, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hPA hPi hP0 τ b hτ hb
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have : NeZero (l ^ m) := ⟨hpos.ne'⟩
  set n := (b : ZMod (l ^ m)).val with hn
  set N := ((b⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val with hN
  have hτi : τ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hτ
  have hτD := Ine_le_Dec A hτi
  have hζ1 : ζ ^ (l ^ m) = 1 := hζ.pow_eq_one
  have hτζ : τ⁻¹ ζ = ζ ^ n := by
    rw [apply_root τ⁻¹ hζ1, map_inv, hb, inv_inv]
  have hco : ∀ i, P.coeff i ∈ fixSub A := by
    intro i
    by_cases h : P.coeff i = 0
    · rw [h]; exact zero_mem _
    · exact hP _ (coeff_mem_coeffs h)
  have hτP : τ⁻¹ (P.eval ζ) = P.eval (ζ ^ n) := by
    rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hτζ, (hco i).2 _ hτi]
  have hζA : ζ ∈ A := by
    rw [← A.valuation_le_one_iff]
    have h1 : A.valuation ζ ^ (l ^ m) = 1 := by rw [← map_pow, hζ1, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' hpos.ne').1 h1).le
  have hQ1 : P.eval (ζ ^ n) ∈ A := hτP ▸ (apply_mem_iff_of_mem_Dec hτD _).2 hPA
  have hQ2 : (P.eval (ζ ^ n))⁻¹ ∈ A := by
    rw [← hτP, ← map_inv₀]; exact (apply_mem_iff_of_mem_Dec hτD _).2 hPi
  have hQ3 : P.eval (ζ ^ n) ≠ 0 := by
    rw [← hτP]; exact (_root_.map_ne_zero _).2 hP0
  have hg : ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n) ∈ A := by
    rw [div_eq_mul_inv]
    refine mul_mem (mul_mem (pow_mem hζA n) (eval_mem A _ (fun i => ?_) (pow_mem hζA n))) hQ2
    rw [coeff_derivative]
    exact mul_mem (hco _).1 (add_mem (natCast_mem A i) (one_mem A))
  have hQe : (P.comp (X ^ n)).eval ζ = P.eval (ζ ^ n) := by simp [eval_comp]
  have hQc : ∀ x ∈ (P.comp (X ^ n)).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x := by
    obtain ⟨P₀, hP₀⟩ : P ∈ lifts (fixSub A).subtype :=
      (lifts_iff_coeff_lifts P).2 fun i => ⟨⟨_, hco i⟩, rfl⟩
    have e : P.comp (X ^ n) = (P₀.comp (X ^ n)).map (fixSub A).subtype := by
      rw [Polynomial.map_comp, ← hP₀]; simp
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.1 hx
    rw [e, coeff_map]
    exact ((P₀.comp (X ^ n)).coeff i).2
  have hD : ζ * (derivative (P.comp (X ^ n))).eval ζ / (P.comp (X ^ n)).eval ζ
      = (n : Ω) * (ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n)) := by
    have e : ζ * ((n : Ω) * ζ ^ (n - 1)) = n * ζ ^ n := by
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]; ring
    rw [hQe, derivative_comp, derivative_X_pow, eval_mul, eval_comp, eval_mul, eval_C, eval_pow, eval_pow, eval_X,
      ← mul_assoc, e]
    ring
  obtain ⟨x, hxA, hx⟩ := hc Ω A hA m ζ ζ' hζ hζ' (P.comp (X ^ n)) hQc (hQe ▸ hQ1) (hQe ▸ hQ2) (hQe ▸ hQ3)
  refine ⟨(N : Ω) * x, mul_mem (natCast_mem A N) hxA, hg, ?_⟩
  intro s hs hs1 k t hk ht
  obtain ⟨v, hv, hsv⟩ := hk
  have hk' : GlobalTheory.Col.KumVal m ζ ((P.comp (X ^ n)).eval ζ) s ((b : ZMod (l ^ m)) * k) := by
    refine ⟨τ⁻¹ v, by rw [← map_pow, hv, hτP, hQe], ?_⟩
    have e1 : s (τ⁻¹ v) = τ⁻¹ ((τ * s * τ⁻¹) v) := by
      have e : s * τ⁻¹ = τ⁻¹ * (τ * s * τ⁻¹) := by group
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ⁻¹, e]
    rw [e1, hsv, map_mul, map_pow, hτζ, ← pow_mul, ZMod.val_mul, ← hn]
    congr 1
    conv_lhs => rw [← Nat.mod_add_div (n * k.val) (l ^ m), pow_add, pow_mul, hζ1, one_pow, mul_one]
  obtain ⟨z, hzA, hz⟩ := hx s hs hs1 _ t hk' ht
  rw [hD] at hz
  obtain ⟨z1, hz1A, hz1⟩ := nat_cg A (L := l ^ m) (a := k.val) (b := N * ((b : ZMod (l ^ m)) * k).val) (by
    push_cast
    rw [hN, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← mul_assoc, Units.inv_mul, one_mul])
  obtain ⟨z2, hz2A, hz2⟩ := nat_cg A (L := l ^ m) (a := N * n) (b := 1) (by
    push_cast
    rw [hN, hn, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.inv_mul])
  push_cast at hz1 hz2
  set g := ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n) with hgdef
  refine ⟨(l : Ω) ^ c * z1 + N * z + (l : Ω) ^ c * t.val * g * z2, ?_, ?_⟩
  · exact add_mem (add_mem (mul_mem (pow_mem (natCast_mem A l) c) hz1A) (mul_mem (natCast_mem A N) hzA))
      (mul_mem (mul_mem (mul_mem (pow_mem (natCast_mem A l) c) (natCast_mem A _)) hg) hz2A)
  · rw [map_mul, map_natCast]
    linear_combination (l : Ω) ^ c * hz1 + (N : Ω) * hz + (l : Ω) ^ c * t.val * g * hz2

end GlobalTheory.RecConj
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

noncomputable section

namespace GlobalTheory.LambdaValuationPowers.LocGlue

open GlobalTheory.LambdaValuationPowers.HTCoUniq ReciprocityTheory.Neutral.Cmp

theorem uniq_fix : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∃ c₂ : ℕ, ∀ (m : ℕ) (D : Qbar l) (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω),
    (∀ i, ‖o i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) →
    (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m (D * GlobalTheory.LambdaValuationPowers.lamv l m s) (∑ i, o i * (j (s (w i)) - j (w i)))) →
    Cg (m - c₂) D 0 := by
  intro l _ hl2 Ω _ _ _ A c j _ hj
  have hj' : Compat l A j := hj
  have hp1 := norm_natCast_lt_one (l := l)
  obtain ⟨c', hc'⟩ := uniq_true hl2
  obtain ⟨c₁, hc₁⟩ := core (K := Qbar l) c.O (fun a ha => norm_le_one_of_mem ha)
    (fun φ a => norm_le_one_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map φ))
    natCast_ne_zero hp1 c'
  refine ⟨c₁, ?_⟩
  intro m D q o w how hyp
  have hx : ‖∑ i, o i * j (w i)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (how i).1 (norm_nonneg _) (how i).2.2
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj') m
  have hd : ‖D‖ ≤ 1 := by
    have h1 : (∑ i, o i * (j (s₀ (w i)) - j (w i))) ∈ ball ((l : Qbar l) ^ 0) := by
      refine sum_mem fun i _ => mul_mem_ball (how i).1 (sub_mem ?_ ?_)
      · simpa [mem_ball] using (hj _).1 ((apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs₀) _).2 ((hj _).2 (how i).2.2))
      · simpa [mem_ball] using (how i).2.2
    have h2 := add_mem (ball_pow_mono hp1 (Nat.zero_le m) (mem_ball.2 (hyp s₀ hs₀ hm₀))) h1
    simpa [mem_ball, hu₀] using h2
  obtain ⟨t, rfl⟩ := exists_grp hj' hs₀ hm₀
  have key := hc₁ (grp A j m) (fun g x => norm_map_GK j g.1 x) (fun g a => smul_algebraMap g.1 a)
    (fun σ => lamv l m (res j σ.1)) m m le_rfl (fun σ => norm_lamv_le_one σ.2.2)
    (fun g σ => smul_lamv g.1 σ.2.2) (fun s t => by simpa using lamv_add_mem s.2.2 t.2.2) t hu₀
    (fun k hk T X hT hX hh => hc' Ω A j hj' m k hk T X hT hX hh) D _ hd hx fun σ hσ => ?_
  · simpa [Cg, mem_ball] using key
  have hine : ∀ x : Qbar l, ‖x‖ ≤ 1 → ‖σ.1 x - x‖ < 1 := by
    intro x hx1
    obtain ⟨a, ha, hxa⟩ := exists_approx hj' 1 hx1
    have h1 : ‖x - j a‖ < 1 := lt_of_le_of_lt (mem_ball.1 hxa) (by simpa using hp1)
    have h2 : ‖j (res j σ.1 a - a)‖ < 1 :=
      (hj'.valuation_lt_one_iff _).1 (σ.2.1.2 a ((A.valuation_le_one_iff a).2 ha))
    have e : σ.1 x - x = σ.1 (x - j a) + (j (res j σ.1 a - a) + -(x - j a)) := by
      rw [map_sub, map_sub, res_spec]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (by rwa [norm_map_GK]) ?_)
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 (by rwa [norm_neg]))
  have hfix : ∀ i, σ.1 (o i) = o i := fun i => (how i).2.1 (σ.1.restrictScalars ℚ_[l]) hσ hine
  have e : σ • (∑ i, o i * j (w i)) - ∑ i, o i * j (w i) = ∑ i, o i * (j (res j σ.1 (w i)) - j (w i)) := by
    show σ.1 _ - _ = _
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hfix, res_spec]; ring
  rw [e]
  exact hyp _ σ.2.1 σ.2.2

theorem exists_kumVal {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {m : ℕ} {ζ u v : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hu : u ≠ 0) (hv : v ^ (l ^ m) = u) {s : G ℚ Ω} (hs : s u = u) :
    ∃ k : ZMod (l ^ m), s v = ζ ^ k.val * v := by
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have h1 : (s v / v) ^ (l ^ m) = 1 := by rw [div_pow, ← map_pow, hv, hs, div_self hu]
  obtain ⟨k, hk, e⟩ := hζ.eq_pow_of_pow_eq_one h1
  exact ⟨(k : ZMod (l ^ m)), by rw [ZMod.val_cast_of_lt hk, e]; field_simp⟩

theorem kumVal_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {m c₀ : ℕ} (hc : c₀ ≤ m) {ζ u : Ω}
    (hζ : IsPrimitiveRoot (ζ ^ l ^ c₀) (l ^ (m - c₀))) (hu : u ≠ 0) {s : G ℚ Ω} (hs : s ζ = ζ) {k : ZMod (l ^ m)}
    {k' : ZMod (l ^ (m - c₀))} (hk : GlobalTheory.Col.KumVal m ζ u s k) (hk' : GlobalTheory.Col.KumVal (m - c₀) (ζ ^ l ^ c₀) u s k') :
    (k'.val : Qbar l) - k.val ∈ ball ((l : Qbar l) ^ (m - c₀)) := by
  obtain ⟨v, hv, hsv⟩ := hk
  have h1 : GlobalTheory.Col.KumVal (m - c₀) (ζ ^ l ^ c₀) u s ((k.val : ℕ) : ZMod (l ^ (m - c₀))) := by
    refine ⟨v ^ l ^ c₀, by rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hc, hv], ?_⟩
    rw [map_pow, hsv, mul_pow, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm k.val]
  have h2 := GlobalTheory.Col.kumVal_unique hζ (by rw [map_pow, hs]) hu hk' h1
  have h3 : (k.val : Qbar l) = k'.val + ((k.val / l ^ (m - c₀) : ℕ) : Qbar l) * (l : Qbar l) ^ (m - c₀) := by
    rw [h2, ZMod.val_natCast]
    exact_mod_cast congrArg (Nat.cast : ℕ → Qbar l) (Nat.mod_add_div' k.val (l ^ (m - c₀))).symm
  rw [h3, sub_add_cancel_left]
  exact neg_mem (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one _ _) (mem_ball.2 le_rfl))

theorem htv_coeff : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (cf : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∀ (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ), c₀ ≤ m →
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x, Z m (s * t) x = Z m s x + (ν s : Qbar l) * Z m t (x * (cycMod ℚ Ω l m s)⁻¹)) →
  ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A cf m c₀ Z ζ P o →
  ∀ y : (ZMod (l ^ m))ˣ, ∃ x : ι → Ω, (∀ i, x i ∈ A) ∧ ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
    Cg (m - c₀) ((l : Qbar l) ^ c * Z m s y)
      ((l : Qbar l) ^ c * htv j ζ P o (y : ZMod (l ^ m)).val * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o i * (j (s (x i)) - j (x i))) := by
  intro l _ hl2
  obtain ⟨c, hc⟩ := GlobalTheory.RecConj.recip_conj l hl2
  refine ⟨c, ?_⟩
  intro Ω _ _ _ A cf j hA hj ν Z m c₀ hm hν hZ ζ ι _ P o hP y
  have hj' : Compat l A j := hj
  have hp1 := norm_natCast_lt_one (l := l)
  have hpc : ‖(l : Qbar l) ^ c‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  obtain ⟨hζ, hco, -, hP0, hζ0, -, hu, ho, hK⟩ := hP
  obtain ⟨⟨τ, hτ⟩, hτy⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A (valuation_lt_one hj') m y⁻¹
  have hτy' : cycMod ℚ Ω l m τ = y⁻¹ := hτy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ', hζ'⟩ := IsAlgClosed.exists_pow_nat_eq ζ hpos
  choose x hxA hgA hx using fun i => hc Ω A hA m ζ ζ' hζ hζ' (P i) (hco i) (hu i).1 (hu i).2.2 (hP0 i) τ y hτ hτy'
  refine ⟨x, hxA, fun s hs hs1 => ?_⟩
  have hs' : τ * s * τ⁻¹ ∈ Ine (F := ℚ) A := mul_mem (mul_mem hτ hs) (inv_mem hτ)
  have hs1' : cycMod ℚ Ω l m (τ * s * τ⁻¹) = 1 := by rw [map_mul, map_mul, hs1, map_inv, mul_one, mul_inv_cancel]
  have hfix : ∀ {g : G ℚ Ω}, cycMod ℚ Ω l m g = 1 → g ζ = ζ := fun hg => by
    haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
      haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
      inferInstance
    exact GlobalTheory.Col.fix_of_cycMod le_rfl hg hζ.pow_eq_one
  have hconj : Z m (τ * s * τ⁻¹) 1 = Z m s y := by
    have h1 := hZ τ (Ine_le_Dec A hτ) s (Ine_le_Dec A hs) 1
    have h2 := hZ _ (Ine_le_Dec A hs') τ (Ine_le_Dec A hτ) 1
    rw [hν τ hτ, hτy', inv_inv, one_mul, Units.val_one, one_mul] at h1
    rw [hν _ hs', hs1', inv_one, one_mul, Units.val_one, one_mul, inv_mul_cancel_right, h1, add_comm] at h2
    exact (add_right_cancel h2).symm
  obtain ⟨k', hk', hZk⟩ := hK _ hs' hs1' (by rw [map_pow, hfix hs1'])
  rw [hconj] at hZk
  have hPfix : ∀ i, (τ * s * τ⁻¹) ((P i).eval ζ) = (P i).eval ζ := by
    intro i
    rw [Polynomial.eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, hfix hs1']
    by_cases h : (P i).coeff n = 0
    · rw [h, map_zero]
    · rw [(hco i _ (Polynomial.coeff_mem_coeffs h)).2 _ hs']
  have hk : ∀ i, ∃ k : ZMod (l ^ m), GlobalTheory.Col.KumVal m ζ ((P i).eval ζ) (τ * s * τ⁻¹) k := by
    intro i
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((P i).eval ζ) hpos
    obtain ⟨k, hk⟩ := exists_kumVal hζ (hP0 i) hv (hPfix i)
    exact ⟨k, v, hv, hk⟩
  choose k hk using hk
  obtain ⟨t, ht⟩ := exists_kumVal hζ (hζ.ne_zero hpos.ne') hζ' (hfix hs1)
  have hlam : (t.val : Qbar l) - lamv l m s ∈ ball ((l : Qbar l) ^ m) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact sub_mem (by simpa [mem_ball] using IsUltrametricDist.norm_natCast_le_one (Qbar l) t.val)
        (by simpa [mem_ball] using norm_lamv_le_one hs1)
    · have hprim : IsPrimitiveRoot ζ' (l ^ (m + m)) := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        have h1 : ¬ ζ' ^ l ^ (n + 1 + n) = 1 := by
          rw [pow_add l (n + 1) n, pow_mul, hζ']
          exact hζ.pow_ne_one_of_pos_of_lt (pow_pos (Fact.out : l.Prime).pos n).ne'
            (Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n))
        have h2 : ζ' ^ l ^ (n + 1 + n + 1) = 1 := by
          rw [add_assoc (n + 1), pow_add l (n + 1) (n + 1), pow_mul, hζ', hζ.pow_eq_one]
        have h3 := orderOf_eq_prime_pow h1 h2
        rw [show n + 1 + (n + 1) = n + 1 + n + 1 from rfl, ← h3]
        exact IsPrimitiveRoot.orderOf ζ'
      exact kummer_sub_lamv hprim hs1 (by rw [hζ']; exact ht)
  have hterm : ∀ i, (l : Qbar l) ^ c * (o i * ((k' i).val : Qbar l)) -
      ((l : Qbar l) ^ c * (o i * j (ζ ^ (y : ZMod (l ^ m)).val * (Polynomial.derivative (P i)).eval (ζ ^ (y : ZMod (l ^ m)).val) /
        (P i).eval (ζ ^ (y : ZMod (l ^ m)).val))) * lamv l m s + o i * (j (s (x i)) - j (x i))) ∈
      ball ((l : Qbar l) ^ (m - c₀)) := by
    intro i
    have h1 := kumVal_sub_mem hm hζ0 (hP0 i) (hfix hs1') (hk i) (hk' i)
    have h2 := (cgA_iff hj' _ _ _).1 (hx i s hs hs1 _ t (hk i) ht)
    have h3 := (hj _).1 (hgA i)
    generalize ζ ^ (y : ZMod (l ^ m)).val * (Polynomial.derivative (P i)).eval (ζ ^ (y : ZMod (l ^ m)).val) /
        (P i).eval (ζ ^ (y : ZMod (l ^ m)).val) = g at h2 h3 ⊢
    simp only [map_mul, map_add, map_sub, map_pow, map_natCast] at h2
    have h4 := mul_mem_ball (ho i) (add_mem (add_mem (mul_mem_ball hpc h1) (ball_pow_mono hp1 (Nat.sub_le m c₀) h2))
      (mul_mem_ball hpc (mul_mem_ball h3 (ball_pow_mono hp1 (Nat.sub_le m c₀) hlam))))
    convert h4 using 1
    ring
  have h5 := add_mem (mul_mem_ball hpc (mem_ball.2 hZk)) (sum_mem fun i (_ : i ∈ Finset.univ) => hterm i)
  refine mem_ball.1 ?_
  convert h5 using 1
  rw [htv, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem localGlue : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
    (j : Ω →+* Qbar l), OverL l A → (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
  ∃ c₁ : ℕ, ∀ (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ), c₀ + c₁ ≤ m →
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) →
    (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x, Z m (s * t) x = Z m s x + (ν s : Qbar l) * Z m t (x * (cycMod ℚ Ω l m s)⁻¹)) →
  ∀ (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (h : (ZMod (l ^ m))ˣ → Qbar l),
    HTPresNuOfPolys A c m c₀ Z ζ P o → (∀ y, GlobalTheory.LambdaValuationPowers.HTCoL A c j Z m c₀ y (h y)) →
    ∀ y : (ZMod (l ^ m))ˣ, Cg (m - c₀ - c₁) (htv j ζ P o (y : ZMod (l ^ m)).val) (h y) := by
  intro l _ hl Ω _ _ _ A c j hA hj
  obtain ⟨cA, hcA⟩ := htv_coeff l hl
  obtain ⟨c₂, hc₂⟩ := uniq_fix l hl Ω A c j hA hj
  refine ⟨cA + c₂, ?_⟩
  intro ν Z m c₀ hm hν hZ ζ ι _ P o h hP hh y
  obtain ⟨x, hxA, hx⟩ := hcA Ω A c j hA hj ν Z m c₀ (by omega) hν hZ ζ ι P o hP y
  obtain ⟨q, o', w', ho', hw'⟩ := hh y
  have hl0 : (l : Qbar l) ≠ 0 := GlobalTheory.LambdaValuationPowers.natCast_ne_zero
  have hl1 : ‖(l : Qbar l)‖ < 1 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one
  have hlpos : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 hl0
  set H := htv j ζ P o (y : ZMod (l ^ m)).val with hH
  let e := Fintype.equivFin ι
  let n := Fintype.card ι
  let o'' : Fin (q + n) → Qbar l :=
    Fin.append (fun i => (l : Qbar l) ^ cA * o' i) (fun i => -((l : Qbar l) ^ c₀ * o (e.symm i)))
  let w'' : Fin (q + n) → Ω := Fin.append w' (fun i => x (e.symm i))
  have hsum : ∀ s : G ℚ Ω, ∑ i, o'' i * (j (s (w'' i)) - j (w'' i)) =
      (l : Qbar l) ^ cA * ∑ i, o' i * (j (s (w' i)) - j (w' i)) -
        (l : Qbar l) ^ c₀ * ∑ i, o i * (j (s (x i)) - j (x i)) := by
    intro s
    rw [Fin.sum_univ_add]
    simp only [o'', w'', Fin.append_left, Fin.append_right]
    rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [← e.symm.sum_comp (fun i => -((l : Qbar l) ^ c₀ * (o i * (j (s (x i)) - j (x i)))))]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hoi : ∀ i, o i ∈ c.O := hP.2.2.1
  have hB : ∀ i, ‖o'' i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (o'' i) ∧ ‖j (w'' i)‖ ≤ 1 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [o'', w'', Fin.append_left]
      obtain ⟨h1, h2, h3⟩ := ho' i
      refine ⟨?_, fun σ hσ hσ' => ?_, h3⟩
      · rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _) h1
      · rw [map_mul, map_pow, map_natCast, h2 σ hσ hσ']
    · simp only [o'', w'', Fin.append_right]
      refine ⟨?_, fun σ hσ _ => ?_, (hj _).1 (hxA _)⟩
      · rw [norm_neg, norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hoi _))
      · rw [map_neg, map_mul, map_pow, map_natCast, hσ _ (hoi _)]
  have key := hc₂ m ((l : Qbar l) ^ (cA + c₀) * (H - h y)) (q + n) o'' w'' hB (by
    intro s hs hs1
    rw [hsum s]
    have h1 := hx s hs hs1
    have h2 := hw' s hs hs1
    unfold Cg at h1 h2 ⊢
    have e1 : (l : Qbar l) ^ (cA + c₀) * (H - h y) * GlobalTheory.LambdaValuationPowers.lamv l m s -
        ((l : Qbar l) ^ cA * ∑ i, o' i * (j (s (w' i)) - j (w' i)) -
          (l : Qbar l) ^ c₀ * ∑ i, o i * (j (s (x i)) - j (x i))) =
        (-(l : Qbar l) ^ c₀) * ((l : Qbar l) ^ cA * Z m s y -
          ((l : Qbar l) ^ cA * H * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o i * (j (s (x i)) - j (x i)))) +
        (l : Qbar l) ^ cA * ((l : Qbar l) ^ c₀ * Z m s y -
          ((l : Qbar l) ^ c₀ * h y * GlobalTheory.LambdaValuationPowers.lamv l m s + ∑ i, o' i * (j (s (w' i)) - j (w' i)))) := by
      ring
    rw [e1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_neg, norm_pow, norm_pow]
      calc ‖(l : Qbar l)‖ ^ c₀ * ‖_‖ ≤ ‖(l : Qbar l)‖ ^ c₀ * ‖(l : Qbar l)‖ ^ (m - c₀) :=
            mul_le_mul_of_nonneg_left (by simpa [norm_pow] using h1) (by positivity)
        _ = ‖(l : Qbar l)‖ ^ m := by rw [← pow_add]; congr 1; omega
    · rw [norm_mul, norm_pow, norm_pow]
      calc ‖(l : Qbar l)‖ ^ cA * ‖_‖ ≤ 1 * ‖(l : Qbar l)‖ ^ m :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hl1.le) (by simpa [norm_pow] using h2) (norm_nonneg _) zero_le_one
        _ = ‖(l : Qbar l)‖ ^ m := one_mul _)
  unfold Cg at key ⊢
  rw [sub_zero, norm_mul, norm_pow, norm_pow] at key
  rw [norm_pow]
  have e2 : ‖(l : Qbar l)‖ ^ (m - c₂) = ‖(l : Qbar l)‖ ^ (cA + c₀) * ‖(l : Qbar l)‖ ^ (m - c₀ - (cA + c₂)) := by
    rw [← pow_add]; congr 1; omega
  rw [e2] at key
  exact le_of_mul_le_mul_left key (pow_pos hlpos _)

end GlobalTheory.LambdaValuationPowers.LocGlue
end
end
