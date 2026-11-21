import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClassStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import BuildAid.ForwardExisting
import Formalism.LocalRingCardinality.ConjSqrtMinusD

section
section
noncomputable section

namespace GlobalTheory.Mem.RayEx

open NumberField IsDedekindDomain

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)

def S : Submonoid (Ideal R) where
  carrier := {I | IsCoprime I m}
  mul_mem' := fun ha hb => IsCoprime.mul_left ha hb
  one_mem' := isCoprime_one_left

def Rel (I J : Ideal R) : Prop :=
  ∃ a b : R, a - 1 ∈ m ∧ b - 1 ∈ m ∧ Ideal.span {a} * I = Ideal.span {b} * J

variable {m}

theorem mul_sub_one_mem {a b : R} (ha : a - 1 ∈ m) (hb : b - 1 ∈ m) : a * b - 1 ∈ m := by
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  exact m.add_mem (m.mul_mem_left _ hb) ha

theorem ne_zero_of_sub_one_mem (hm : m ≠ ⊤) {a : R} (ha : a - 1 ∈ m) : a ≠ 0 := by
  rintro rfl
  apply hm
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem ha

theorem ne_bot_of_isCoprime (hm : m ≠ ⊤) {I : Ideal R} (h : IsCoprime I m) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at h
  exact hm h

theorem exists_mem_sub_one {I : Ideal R} (h : IsCoprime I m) : ∃ a ∈ I, a - 1 ∈ m := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  refine ⟨a, ha, ?_⟩
  have : a - 1 = -b := by rw [← hab]; ring
  rw [this]
  exact m.neg_mem hb

theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m := by
  refine Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩

theorem Rel.refl (I : Ideal R) : Rel m I I := ⟨1, 1, by simp, by simp, rfl⟩

theorem Rel.symm {I J : Ideal R} (h : Rel m I J) : Rel m J I := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  exact ⟨b, a, hb, ha, h.symm⟩

theorem Rel.mul {I J I' J' : Ideal R} (h : Rel m I J) (h' : Rel m I' J') : Rel m (I * I') (J * J') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨a * c, b * d, mul_sub_one_mem ha hc, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, h, h', mul_mul_mul_comm]

theorem Rel.trans {I J L : Ideal R} (h : Rel m I J) (h' : Rel m J L) : Rel m I L := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨c * a, b * d, mul_sub_one_mem hc ha, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_assoc, h, mul_left_comm, h', mul_assoc]

variable (m) in

def con : Con (S m) where
  r I J := Rel m I.1 J.1
  iseqv := ⟨fun I => Rel.refl _, Rel.symm, Rel.trans⟩
  mul' := fun h h' => Rel.mul h h'

theorem isUnit_quot (x : (con m).Quotient) : IsUnit x := by
  obtain ⟨⟨I, hI⟩, rfl⟩ := Con.mk'_surjective (c := con m) x
  obtain ⟨a, haI, ha⟩ := exists_mem_sub_one hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr haI
  have hJ' : IsCoprime J m := by
    have := isCoprime_span ha
    rw [hJ] at this
    exact this.of_mul_left_right
  refine IsUnit.of_mul_eq_one ((con m).mk' ⟨J, hJ'⟩) ?_
  rw [← map_mul, ← map_one (con m).mk']
  refine (Con.eq _).mpr ?_
  refine ⟨1, a, by simp, ha, ?_⟩
  simp [hJ]

theorem exists_good {I J : Ideal R} (hI : IsCoprime I m) (hJ : IsCoprime J m) {x y : R} (hy : y ≠ 0)
    (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ b : R, IsCoprime (Ideal.span {b}) m ∧ Rel m I (Ideal.span {b} * J) := by
  obtain ⟨a, haJ, ha⟩ := exists_mem_sub_one hJ
  have h1 : y * a ∈ Ideal.span {x} * I := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ
  obtain ⟨b, -, hb⟩ := Ideal.mem_span_singleton_mul.mp h1
  have h2 : Ideal.span {a} * I = Ideal.span {b} * J := by
    have hy' : (Ideal.span {y} : Ideal R) ≠ 0 := by simpa using hy
    apply mul_left_cancel₀ hy'
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, mul_comm b x]
  refine ⟨b, ?_, a, 1, ha, by simp, by simp [h2]⟩
  have := (isCoprime_span ha).mul_left hI
  rw [h2] at this
  exact this.of_mul_left_left

theorem rel_span {b c : R} (hb : IsCoprime (Ideal.span {b}) m) (h : b - c ∈ m) :
    Rel m (Ideal.span {b}) (Ideal.span {c}) := by
  obtain ⟨a, haI, ha⟩ := exists_mem_sub_one hb
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp haI
  refine ⟨u * c, u * b, ?_, ha, ?_⟩
  · have : u * c - 1 = (u * b - 1) - u * (b - c) := by ring
    rw [this]
    exact m.sub_mem ha (m.mul_mem_left _ h)
  · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    congr 2
    ring

theorem finite_quot (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] : Finite (con m).Quotient := by
  let cl : S m → ClassGroup R := fun I =>
    ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero (ne_bot_of_isCoprime hm I.2)⟩
  have key : ∀ I : S m, ∃ b : R, IsCoprime (Ideal.span {b}) m ∧
      Rel m I.1 (Ideal.span {b} * (Function.invFun cl (cl I)).1) := by
    intro I
    have h : cl I = cl (Function.invFun cl (cl I)) := (Function.invFun_eq ⟨I, rfl⟩).symm
    obtain ⟨x, y, -, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good I.2 (Function.invFun cl (cl I)).2 hy hxy
  choose b hb hrel using key
  let F : (con m).Quotient → ClassGroup R × (R ⧸ m) := fun x =>
    (cl (Quotient.out x), Ideal.Quotient.mk m (b (Quotient.out x)))
  refine Finite.of_injective F ?_
  intro x y hxy
  obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
  rw [Ideal.Quotient.eq] at h2
  refine Quotient.out_equiv_out.mp ?_
  have h3 := hrel (Quotient.out y)
  rw [← h1] at h3
  exact ((hrel _).trans ((rel_span (hb _) h2).mul (Rel.refl _))).trans h3.symm

theorem exists_group (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] :
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (φ : S m →* G), Function.Surjective φ ∧
      ∀ I J, φ I = φ J ↔ Rel m I.1 J.1 := by
  haveI : Finite (con m).Quotient := finite_quot hm
  exact ⟨(con m).Quotient, commGroupOfIsUnit isUnit_quot, Fintype.ofFinite _, (con m).mk',
    Con.mk'_surjective, fun I J => Con.eq _⟩

theorem map_mul_mk {G : Type} [CommGroup G] (φ : S m →* G) {I J : Ideal R} (hI : IsCoprime I m)
    (hJ : IsCoprime J m) : φ ⟨I * J, hI.mul_left hJ⟩ = φ ⟨I, hI⟩ * φ ⟨J, hJ⟩ := by
  have h : (⟨I * J, hI.mul_left hJ⟩ : S m) = (⟨I, hI⟩ : S m) * (⟨J, hJ⟩ : S m) :=
    Subtype.ext (Submonoid.coe_mul (S m) ⟨I, hI⟩ ⟨J, hJ⟩).symm
  rw [h, map_mul]

end General

open Classical in

theorem nonempty_rayData (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : 2 ≤ M) : Nonempty (RayData K M) := by
  set m : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with hmdef
  have hm0 : m ≠ ⊥ := by
    rw [hmdef, Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hm : m ≠ ⊤ := by
    rw [hmdef, Ne, Ideal.span_singleton_eq_top]
    intro h
    have h' : IsUnit (algebraMap ℤ (𝓞 K) (M : ℤ)) := by simpa using h
    have := (isUnit_map_iff (algebraMap ℤ (𝓞 K)) _).mp h'
    rw [Int.isUnit_iff] at this
    omega
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm0
  obtain ⟨G, _, _, φ, hs, he⟩ := exists_group hm
  refine ⟨{ G := G
            cls := fun I => if h : IsCoprime I m then φ ⟨I, h⟩ else 1
            cls_mul := ?_, cls_surj := ?_, cls_eq := ?_ }⟩
  · intro I J hI hJ _ _
    rw [dif_pos hI, dif_pos hJ, dif_pos (hI.mul_left hJ)]
    exact map_mul_mk φ hI hJ
  · intro c
    obtain ⟨⟨I, hI⟩, rfl⟩ := hs c
    exact ⟨I, hI, ne_bot_of_isCoprime hm hI, dif_pos hI⟩
  · intro I J hI hJ _ _
    rw [dif_pos hI, dif_pos hJ, he]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨a, b, ne_zero_of_sub_one_mem hm ha, ne_zero_of_sub_one_mem hm hb, ha, hb, h⟩
    · rintro ⟨a, b, -, -, ha, hb, h⟩
      exact ⟨a, b, ha, hb, h⟩

end GlobalTheory.Mem.RayEx

end
end

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_data_nonempty : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → Nonempty (RayData K M) := by
  atlas_forward_decl GlobalTheory.Mem.RayEx.nonempty_rayData
end

section
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem.NormPrimes

theorem norm_nonneg_of_imag_quadratic (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (x : 𝓞 K) : 0 ≤ Algebra.norm ℤ x := by
  classical
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 h)
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, h2]
  have huniv : (Finset.univ : Finset (K →+* ℂ)) = {ComplexEmbedding.conjugate φ, φ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f (x : K)) (fun σ => σ (x : K))
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), huniv, Finset.prod_pair hne,
    ComplexEmbedding.conjugate_coe_eq, mul_comm, Complex.mul_conj, ← Algebra.coe_norm_int] at h1
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℝ) = Complex.normSq (φ x) := by
    apply Complex.ofReal_injective
    rw [← h1]; simp
  have h4 : (0 : ℝ) ≤ ((Algebra.norm ℤ x : ℤ) : ℝ) := h3 ▸ Complex.normSq_nonneg _
  exact_mod_cast h4

theorem exists_prime_norm_of_two_le (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (M : ℕ) (hM : 2 ≤ M) (a : 𝓞 K) (ha : IsCoprime a (M : 𝓞 K)) (N : ℕ) :
    ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  obtain ⟨D⟩ := GlobalTheory.T.ray_data_nonempty K M hM
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hu : IsUnit ((M : ℕ) : 𝓞 K) := isCoprime_zero_left.1 ha
    have h1 := hu.map (Algebra.norm ℤ)
    have h3 : Algebra.norm ℤ ((M : ℕ) : 𝓞 K) = (M : ℤ) ^ 2 := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (M : ℤ)
      rw [RingOfIntegers.rank, h2] at this
      simpa using this
    rw [h3, isUnit_pow_iff two_ne_zero, Int.isUnit_iff] at h1
    omega
  have hac : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 ha
  obtain ⟨v, hc, hp, hN⟩ := GlobalTheory.T.infinitely_many_primes_in_ray_class K h2 M hM D (D.cls (Ideal.span {a})) N
  obtain ⟨x, y, hx0, hy0, hx, hy, hxy⟩ := (D.cls_eq _ _ v.2 hac v.1.ne_bot
    (by simpa using ha0)).1 hc
  rw [Ideal.span_singleton_mul_span_singleton] at hxy
  have hdvd : x ∣ y * a := by
    rw [← Ideal.mem_span_singleton]
    have : y * a ∈ Ideal.span {x} * v.1.asIdeal := by
      rw [hxy]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left this
  obtain ⟨π, hπ⟩ := hdvd
  have hv : v.1.asIdeal = Ideal.span {π} := by
    rw [hπ, ← Ideal.span_singleton_mul_span_singleton] at hxy
    exact mul_left_cancel₀ (by simpa using hx0) hxy
  refine ⟨π, Ideal.absNorm v.1.asIdeal, hp, hN, ?_, ?_⟩
  · rw [hv, Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg (norm_nonneg_of_imag_quadratic K h2 π)]
  · have : π - a = (y - 1) * a - (x - 1) * π := by linear_combination -hπ
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_right _ _ hx)

theorem exists_prime_norm : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  intro K _ _ _ h2 M hM a ha N
  rcases Nat.lt_or_ge M 2 with h | h
  · obtain rfl : M = 1 := by omega
    obtain ⟨π, p, hp, hN, hn, -⟩ := exists_prime_norm_of_two_le K h2 2 le_rfl 1 isCoprime_one_left N
    exact ⟨π, p, hp, hN, hn, by simp⟩
  · exact exists_prime_norm_of_two_le K h2 M h a ha N

end GlobalTheory.Mem.NormPrimes
end

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_element_congruent : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  atlas_forward_decl GlobalTheory.Mem.NormPrimes.exists_prime_norm
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.NormPrime

theorem norm_eq_mul_conj {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = φ x * starRingEnd ℂ (φ x) := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have hne : φ.toRatAlgHom ≠ (ComplexEmbedding.conjugate φ).toRatAlgHom := by
    intro he
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk φ)
    apply InfinitePlace.isComplex_mk_iff.mp hc
    rw [ComplexEmbedding.isReal_iff]
    ext y
    exact (congrArg (fun f : K →ₐ[ℚ] ℂ => f y) he).symm
  have hu : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) =
      {φ.toRatAlgHom, (ComplexEmbedding.conjugate φ).toRatAlgHom} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, AlgHom.card, h2]
  rw [hu, Finset.prod_pair hne] at h
  exact h

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem finrank_K (H : Host R) : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

theorem norm_K (H : Host R) (x : H.K) :
    (x : H.E) * H.conj (x : H.E) = ((Algebra.norm ℚ x : ℚ) : H.E) := by
  have := isTotallyComplex_K H
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj (x : H.E)) = starRingEnd ℂ (H.φ₀ (x : H.E)) :=
    H.toHostAx.conjE_apply _ _
  rw [map_mul, h1, map_ratCast,
    norm_eq_mul_conj (finrank_K H) (H.φ₀.comp (algebraMap H.K H.E)) x]
  rfl

theorem dvd_of_eq_mul_integral {E : Type} [Field E] [NumberField E] {M : ℕ} (hM : M ≠ 0) {n : ℤ} {y : E}
    (hy : IsIntegral ℤ y) (h : (n : E) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
  have hM'' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have e : y = algebraMap ℚ E ((n : ℚ) / M) := by
    rw [map_div₀, map_intCast, map_natCast, h]; field_simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hy
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  refine ⟨k, ?_⟩
  have : (n : ℚ) = M * k := by
    have hk' : (k : ℚ) = n / M := by simpa using hk
    rw [hk']; field_simp
  exact_mod_cast this

theorem exists_norm_prime : ∀ (R : Ranks) (H : Host R) (M a N : ℕ), M ≠ 0 → Nat.Coprime a M →
    ∃ (π : 𝓞 H.E) (p : ℕ), p.Prime ∧ N < p ∧ (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ π - (a : 𝓞 H.E) ∈ Ideal.span {(M : 𝓞 H.E)} ∧
      p ≡ a ^ 2 [MOD M] := by
  intro R H M a N hM haM
  have := isTotallyComplex_K H
  obtain ⟨π, p, hp, hN, hn, hc⟩ := GlobalTheory.T.exists_prime_element_congruent H.K (finrank_K H) M hM (a : 𝓞 H.K)
    (Nat.Coprime.cast haM) N
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hc
  have hπ : ((algebraMap (𝓞 H.K) (𝓞 H.E) π : 𝓞 H.E) : H.E) = ((π : H.K) : H.E) := rfl
  have hnorm : ((π : H.K) : H.E) * H.conj ((π : H.K) : H.E) = (p : H.E) := by
    rw [norm_K, ← Algebra.coe_norm_int, hn]
    simp
  have hx' : algebraMap (𝓞 H.K) (𝓞 H.E) x * (M : 𝓞 H.E) =
      algebraMap (𝓞 H.K) (𝓞 H.E) π - (a : 𝓞 H.E) := by
    have := congrArg (algebraMap (𝓞 H.K) (𝓞 H.E)) hx
    rwa [map_mul, map_sub, map_natCast, map_natCast] at this
  refine ⟨algebraMap (𝓞 H.K) (𝓞 H.E) π, p, hp, hN, ?_, ?_, Ideal.mem_span_singleton'.mpr ⟨_, hx'⟩, ?_⟩
  · rw [hπ]; exact (π : H.K).2
  · rw [hπ]; exact hnorm
  · set y : 𝓞 H.E := algebraMap (𝓞 H.K) (𝓞 H.E) x
    have hy : IsIntegral ℤ (y : H.E) := y.isIntegral_coe
    have hcy : IsIntegral ℤ (H.conj (y : H.E)) := hy.map (H.conj.toAlgHom.restrictScalars ℤ)
    have e : ((π : H.K) : H.E) = a + M * (y : H.E) := by
      have := congrArg (algebraMap (𝓞 H.E) H.E) hx'
      rw [map_mul, map_sub, map_natCast, map_natCast] at this
      rw [← hπ]
      linear_combination -this
    rw [e, map_add, map_mul, map_natCast, map_natCast] at hnorm
    have hd : (M : ℤ) ∣ (p : ℤ) - (a : ℤ) ^ 2 := by
      apply dvd_of_eq_mul_integral (E := H.E) hM
        (y := a * (y : H.E) + a * H.conj (y : H.E) + M * ((y : H.E) * H.conj (y : H.E)))
      · have ha : IsIntegral ℤ (a : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (a : ℤ)))
        have hMi : IsIntegral ℤ (M : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (M : ℤ)))
        exact ((ha.mul hy).add (ha.mul hcy)).add (hMi.mul (hy.mul hcy))
      · push_cast
        linear_combination -hnorm
    apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd]
    exact_mod_cast hd

end GlobalTheory.Mem.NormPrime
end
