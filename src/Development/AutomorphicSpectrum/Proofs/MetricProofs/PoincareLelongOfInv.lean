import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import BuildAid.ForwardExisting
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBCMult
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CArint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition

section
section
namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add, map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

theorem not_sq_eq_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (b : ℚ)
    (h : (p : ℚ) = q * b ^ 2) : False := by
  haveI := Fact.mk hq
  have hb : b ≠ 0 := by
    rintro rfl
    have h0 : (p : ℚ) = 0 := by rw [h]; ring
    exact hp.ne_zero (by exact_mod_cast h0)
  have h1 := congrArg (padicValRat q) h
  rw [padicValRat.mul (by exact_mod_cast hq.ne_zero) (pow_ne_zero 2 hb), padicValRat.pow b,
    padicValRat.self hq.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd] at h1
  · push_cast at h1
    omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd).symm

theorem false_of_sq_eq {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (x : E) (hx : x ^ 2 = -(q : E)) (a b : ℚ)
    (h : (algebraMap ℚ E a + algebraMap ℚ E b * x) ^ 2 = -(p : E)) : False := by
  have hφ : Function.Injective (algebraMap ℚ E) := (algebraMap ℚ E).injective
  have key : algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) + algebraMap ℚ E (2 * a * b) * x = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination h - algebraMap ℚ E b ^ 2 * hx
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  by_cases hab : 2 * a * b = 0
  · rw [hab, map_zero, zero_mul, add_zero, map_eq_zero_iff _ hφ] at key
    rcases mul_eq_zero.mp hab with h2a | hb
    · have ha : a = 0 := by linarith
      subst ha
      exact not_sq_eq_of_prime hp hq hpq b (by linear_combination key)
    · subst hb
      nlinarith [sq_nonneg a]
  · have hne : algebraMap ℚ E (2 * a * b) ≠ 0 := (map_ne_zero _).mpr hab
    have hx' : x = -algebraMap ℚ E (a ^ 2 - q * b ^ 2 + p) / algebraMap ℚ E (2 * a * b) :=
      eq_div_of_mul_eq hne (by linear_combination key)
    rw [← map_neg, ← map_div₀] at hx'
    rw [hx', ← map_pow, show -(q : E) = algebraMap ℚ E (-(q : ℚ)) by rw [map_neg, map_natCast]] at hx
    have h2 := hφ hx
    nlinarith [sq_nonneg (-(a ^ 2 - q * b ^ 2 + p) / (2 * a * b))]

theorem finite_primes_of_finiteDimensional (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)}.Finite := by
  classical
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField ℚ E).mp
      ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key : ∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : E, x ^ 2 = -(p : E) → y ^ 2 = -(q : E) →
      IntermediateField.adjoin ℚ {x} = IntermediateField.adjoin ℚ {y} → p = q := by
    intro p q hp hq x y hx hy he
    by_contra hpq
    have hmem : x ∈ IntermediateField.adjoin ℚ {y} := by
      rw [← he]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    obtain ⟨a, b, hab⟩ :=
      exists_eq_add_mul_of_mem_adjoin y (-(q : ℚ)) (by rw [hy, map_neg, map_natCast]) hmem
    exact false_of_sq_eq hp hq hpq y hy a b (by rw [← hab]; exact hx)
  have hinj : Function.Injective (fun p : {p : ℕ | p.Prime ∧ ∃ x : E, x ^ 2 = -(p : E)} =>
      IntermediateField.adjoin ℚ {Classical.choose p.2.2}) := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ he
    exact Subtype.ext (key p q hp.1 hq.1 _ _ (Classical.choose_spec hp.2) (Classical.choose_spec hq.2) he)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ hinj)

theorem finite_primes_field (F : Type*) [Field F] [CharZero F] [Algebra ℚ F]
    [Algebra.EssFiniteType ℚ F] : {p : ℕ | p.Prime ∧ ∃ x : F, x ^ 2 = -(p : F)}.Finite := by
  have hfd := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType ℚ F
  refine (@finite_primes_of_finiteDimensional (algebraicClosure ℚ F) _ _ (algebraicClosure ℚ F).algebra' hfd).subset ?_
  rintro p ⟨hp, x, hx⟩
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C (-(p : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, by simp [hx]⟩
  have hmem : x ∈ algebraicClosure ℚ F := mem_algebraicClosure_iff'.mpr hint
  exact ⟨hp, ⟨x, hmem⟩, Subtype.ext (by simp [hx])⟩

theorem finite_primes_of_isFractionRing (A F : Type*) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] [Field F] [Algebra A F] [IsFractionRing A F] :
    {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective A F)
  haveI : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ A F
  haveI : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  refine (finite_primes_field F).subset ?_
  rintro p ⟨hp, a, b, hb, hab⟩
  have hb' : algebraMap A F b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A F (by rw [h0, map_zero]))
  refine ⟨hp, algebraMap A F a / algebraMap A F b, ?_⟩
  have e := congrArg (algebraMap A F) hab
  simp only [map_add, map_mul, map_pow, map_natCast, map_zero] at e
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hb')]
  linear_combination e

theorem finite_primes_neg_sq : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  intro σ _ A _ _ _ f hf
  haveI : Algebra.FiniteType ℤ A := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    refine Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr
      ⟨n, MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i))), ?_⟩
    have hcomp : ((MvPolynomial.aeval (R := ℤ) (fun i : Fin n => f (MvPolynomial.X (e.symm i)))).toRingHom).comp
        (MvPolynomial.rename (R := ℤ) e).toRingHom = f := by
      apply MvPolynomial.ringHom_ext'
      · exact RingHom.ext_int _ _
      · intro s
        simp
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨MvPolynomial.rename (R := ℤ) e p, RingHom.congr_fun hcomp p⟩
  exact finite_primes_of_isFractionRing A (FractionRing A)

end GlobalTheory.CompanionTheory.QuadFin
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_primes_sum_squares_zero : ∀ (σ : Type) [Finite σ] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (f : MvPolynomial σ ℤ →+* A), Function.Surjective f → {p : ℕ | p.Prime ∧ ∃ a b : A, b ≠ 0 ∧ a ^ 2 + (p : A) * b ^ 2 = 0}.Finite := by
  atlas_forward_decl GlobalTheory.CompanionTheory.QuadFin.finite_primes_neg_sq
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem exists_root_field {D : Type} [CommRing D] [IsDomain D] (p : ℕ)
    (h : ∀ a b : D, a ^ 2 + (p : D) * b ^ 2 = 0 → b = 0) :
    ∃ (E : Type) (_ : Field E) (i : D →+* E) (s : E), s ^ 2 = -(p : E) ∧
      ∀ u v : D, i u + i v * s = 0 → u = 0 ∧ v = 0 := by
  classical
  let F := FractionRing D
  let g : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (p : F)
  have hmonic : g.Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : g.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hinjF : Function.Injective (algebraMap D F) := IsFractionRing.injective D F
  have hnr : ∀ r : F, r ^ 2 + (p : F) ≠ 0 := by
    intro r hr
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) r
    have hb0 : algebraMap D F b ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero hb (hinjF (by simpa using h0))
    have h1 : algebraMap D F (a ^ 2 + (p : D) * b ^ 2) = 0 := by
      simp only [map_add, map_mul, map_pow, map_natCast]
      have e : algebraMap D F a ^ 2 + (p : F) * algebraMap D F b ^ 2 =
          ((algebraMap D F a / algebraMap D F b) ^ 2 + (p : F)) * algebraMap D F b ^ 2 := by
        rw [div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hb0)]
      rw [e, hr, zero_mul]
    have h2 : a ^ 2 + (p : D) * b ^ 2 = 0 := hinjF (by simpa using h1)
    exact hb0 (by rw [h a b h2, map_zero])
  have hirr : Irreducible g := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    have := (Polynomial.mem_roots'.mp hr).2
    simp [g, Polynomial.IsRoot] at this
    exact hnr r this
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  refine ⟨AdjoinRoot g, inferInstance, (AdjoinRoot.of g).comp (algebraMap D F), AdjoinRoot.root g, ?_, ?_⟩
  · have h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C (p : F)) = 0 := AdjoinRoot.mk_self
    rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_natCast] at h0
    linear_combination h0
  · intro u v huv
    have h1 : AdjoinRoot.mk g (Polynomial.C (algebraMap D F u) +
        Polynomial.C (algebraMap D F v) * Polynomial.X) = 0 := by
      simpa using huv
    rw [AdjoinRoot.mk_eq_zero] at h1
    have h2 := Polynomial.eq_zero_of_dvd_of_degree_lt h1 (by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
      compute_degree
      exact_mod_cast (by norm_num : 1 < 2))
    have hu := congrArg (fun t => Polynomial.coeff t 0) h2
    have hv := congrArg (fun t => Polynomial.coeff t 1) h2
    simp at hu hv
    exact ⟨hu, hv⟩

theorem twist_isPrime (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) (hN : NoRoot p W) : (twist p W).IsPrime := by
  classical
  haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
  have hD : ∀ a b : MRing ι ⧸ W, a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0 → b = 0 := by
    intro a b h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hN a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h
  obtain ⟨E, _, i, s, hs, hind⟩ := exists_root_field p hD
  let φ : MRing (Tb ι) →+* Polynomial E :=
    (aeval (fun q : Σ o, Tb ι o => match q with
      | ⟨none, j⟩ => if j = (0 : Fin 2) then Polynomial.C s * Polynomial.X else Polynomial.X
      | ⟨some k, l⟩ => Polynomial.C (i (Ideal.Quotient.mk W (X ⟨k, l⟩)))) :
        MRing (Tb ι) →ₐ[ℤ] Polynomial E).toRingHom
  have hinc : ∀ f : MRing ι, φ (inc f) = Polynomial.C (i (Ideal.Quotient.mk W f)) := by
    intro f
    have : (φ.comp inc) = (Polynomial.C.comp (i.comp (Ideal.Quotient.mk W))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [φ, inc]
      · intro l; simp [φ, inc, oldIdx]
    exact congrArg (fun g => g f) this
  have hx : φ xN = Polynomial.C s * Polynomial.X := by
    simp only [φ, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_pos rfl
  have hy : φ yN = Polynomial.X := by
    simp only [φ, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
  have hCp : φ (C (p : ℤ)) = (p : Polynomial E) := by
    simp [φ]
  have hle : twist p W ≤ RingHom.ker φ := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, hinc, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      simp
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show quad p ∈ RingHom.ker φ
      rw [RingHom.mem_ker]
      simp only [quad, map_add, map_mul, map_pow, hx, hy, hCp]
      have hs' : (Polynomial.C s) ^ 2 = -(p : Polynomial E) := by
        rw [← map_pow, hs]; simp
      linear_combination (Polynomial.X ^ 2 : Polynomial E) * hs'
  let φ' : (MRing (Tb ι) ⧸ twist p W) →+* Polynomial E :=
    Ideal.Quotient.lift _ φ (fun a ha => hle ha)
  let mk' := Ideal.Quotient.mk (twist p W)
  have hWle : ∀ a ∈ W, (mk'.comp inc) a = 0 := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  let τ : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Ideal.Quotient.lift W (mk'.comp inc) hWle
  let σ : Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Polynomial.eval₂RingHom τ (mk' yN)
  have hσC : ∀ d, σ (Polynomial.C d) = τ d := fun d => by simp [σ]
  have hσX : σ Polynomial.X = mk' yN := by simp [σ]
  have hxx : mk' xN * mk' xN = σ (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2) := by
    have hq : mk' (quad p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp only [quad, map_add, map_mul, map_pow] at hq
    have hc : mk' (C (p : ℤ)) = (p : MRing (Tb ι) ⧸ twist p W) := by simp [mk']
    rw [hc] at hq
    simp only [map_mul, map_neg, map_natCast, map_pow, hσX]
    linear_combination hq
  have hform : ∀ f : MRing (Tb ι), ∃ a b : Polynomial (MRing ι ⧸ W),
      mk' f = σ a + σ b * mk' xN := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n =>
      refine ⟨(n : Polynomial (MRing ι ⧸ W)), 0, ?_⟩
      simp [mk']
    | add f g hf hg =>
      obtain ⟨a, b, h1⟩ := hf
      obtain ⟨a', b', h2⟩ := hg
      exact ⟨a + a', b + b', by rw [map_add, h1, h2, map_add, map_add]; ring⟩
    | mul_X f q hf =>
      obtain ⟨a, b, h1⟩ := hf
      rw [map_mul, h1]
      obtain ⟨o, l⟩ := q
      cases o with
      | none =>
        have aux : ∀ l : Fin 2, (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = xN ∨
            (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = yN := by
          intro l
          fin_cases l
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases aux l with hl | hl
        · rw [hl]
          refine ⟨b * (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2), a, ?_⟩
          rw [map_mul σ b, ← hxx]
          ring
        · rw [hl]
          refine ⟨a * Polynomial.X, b * Polynomial.X, ?_⟩
          rw [map_mul, map_mul, hσX]
          ring
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)),
          b * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)), ?_⟩
        have hτ : τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (X ⟨some k, l⟩) := by
          rw [show τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (inc (X ⟨k, l⟩)) from Ideal.Quotient.lift_mk _ _ _]
          simp [inc, oldIdx]
        rw [map_mul, map_mul, hσC, hτ]
        ring
  have hφ' : ∀ f, φ' (mk' f) = φ f := fun f => Ideal.Quotient.lift_mk _ _ _
  have hτ' : ∀ d, τ (Ideal.Quotient.mk W d) = mk' (inc d) := fun d => Ideal.Quotient.lift_mk _ _ _
  have hσ : ∀ a, φ' (σ a) = a.map (i : (MRing ι ⧸ W) →+* E) := by
    have : (φ'.comp σ) = Polynomial.mapRingHom i := by
      apply Polynomial.ringHom_ext
      · intro d
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
        show φ' (σ (Polynomial.C _)) = (Polynomial.C _).map i
        rw [hσC, hτ', hφ', hinc, Polynomial.map_C]
      · show φ' (σ Polynomial.X) = Polynomial.X.map i
        rw [hσX, hφ', hy, Polynomial.map_X]
    exact fun a => congrArg (fun g => g a) this
  have hφx : φ' (mk' xN) = Polynomial.C s * Polynomial.X := by
    rw [hφ', hx]
  have hinj : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, h1⟩ := hform f
    change φ' (mk' f) = 0 at hq
    change mk' f = 0
    rw [h1] at hq ⊢
    rw [map_add, map_mul, hσ, hσ, hφx] at hq
    have hcoef : ∀ n, (a.coeff (n + 1) = 0 ∧ b.coeff n = 0) := by
      intro n
      have := congrArg (fun t => Polynomial.coeff t (n + 1)) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff (n + 1) =
          i (b.coeff n) * s := by
        rw [← mul_assoc, Polynomial.coeff_mul_X, mul_comm, Polynomial.coeff_C_mul,
          Polynomial.coeff_map, mul_comm]
      rw [e] at this
      exact hind _ _ this
    have ha0 : a.coeff 0 = 0 := by
      have := congrArg (fun t => Polynomial.coeff t 0) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff 0 = 0 := by
        rw [← mul_assoc, Polynomial.coeff_mul_X_zero]
      rw [e, add_zero] at this
      have h3 := hind (a.coeff 0) 0 (by simpa using this)
      exact h3.1
    have ha : a = 0 := by
      ext n
      cases n with
      | zero => simpa using ha0
      | succ n => simpa using (hcoef n).1
    have hb : b = 0 := by
      ext n
      simpa using (hcoef n).2
    rw [ha, hb]; simp
  haveI : IsDomain (MRing (Tb ι) ⧸ twist p W) := hinj.isDomain φ'
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end GlobalTheory.CompanionTheory.Ar.Tw
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → NoRoot p W → (twist p W).IsPrime := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def baseD (p : ℕ) (W : Ideal (MRing ι)) : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Ideal.Quotient.lift W ((Ideal.Quotient.mk (twist p W)).comp inc) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

def baseP (p : ℕ) (W : Ideal (MRing ι)) :
    Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Polynomial.eval₂RingHom (baseD p W) (Ideal.Quotient.mk (twist p W) yN)

def quadP (p : ℕ) (W : Ideal (MRing ι)) : Polynomial (Polynomial (MRing ι ⧸ W)) :=
  Polynomial.X ^ 2 + Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)

theorem quadraticPolynomial_monic (p : ℕ) (W : Ideal (MRing ι)) : (quadP p W).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

theorem quadraticPolynomial_natDegree (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] : (quadP p W).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_add_C

def coordA (p : ℕ) (W : Ideal (MRing ι)) : (Σ o, Tb ι o) → AdjoinRoot (quadP p W)
  | ⟨none, j⟩ => (![AdjoinRoot.root _, AdjoinRoot.of _ Polynomial.X] : Fin 2 → _) j
  | ⟨some k, i⟩ => AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩)))

def toA (p : ℕ) (W : Ideal (MRing ι)) : MRing (Tb ι) →+* AdjoinRoot (quadP p W) :=
  (aeval (coordA p W) : MRing (Tb ι) →ₐ[ℤ] AdjoinRoot (quadP p W)).toRingHom

theorem toA_inc (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    toA p W (inc f) = AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W f)) := by
  have h : (toA p W).comp inc =
      (AdjoinRoot.of (quadP p W)).comp (Polynomial.C.comp (Ideal.Quotient.mk W)) := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · intro i
      simp only [RingHom.comp_apply, toA, inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        aeval_X]
      rfl
  exact RingHom.congr_fun h f

theorem toA_xN (p : ℕ) (W : Ideal (MRing ι)) : toA p W xN = AdjoinRoot.root _ := by
  simp only [toA, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_yN (p : ℕ) (W : Ideal (MRing ι)) : toA p W yN = AdjoinRoot.of _ Polynomial.X := by
  simp only [toA, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_quad (p : ℕ) (W : Ideal (MRing ι)) : toA p W (quad p) = 0 := by
  have h : AdjoinRoot.mk (quadP p W) (Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_intCast,
    Int.cast_natCast, map_natCast] at h
  have hC : toA p W (MvPolynomial.C (p : ℤ)) = (p : AdjoinRoot (quadP p W)) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quad, map_add, map_mul, map_pow, toA_xN, toA_yN, hC]
  linear_combination h

theorem twist_le_ker_toA (p : ℕ) (W : Ideal (MRing ι)) : twist p W ≤ RingHom.ker (toA p W) := by
  unfold twist
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, toA_inc, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero,
      map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 (toA_quad p W)

def quotA (p : ℕ) (W : Ideal (MRing ι)) : (MRing (Tb ι) ⧸ twist p W) →+* AdjoinRoot (quadP p W) :=
  Ideal.Quotient.lift _ (toA p W) fun _ ha => twist_le_ker_toA p W ha

theorem quotA_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing (Tb ι)) :
    quotA p W (Ideal.Quotient.mk _ f) = toA p W f := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseD_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    baseD p W (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (inc f) := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseP_C (p : ℕ) (W : Ideal (MRing ι)) (a : MRing ι ⧸ W) :
    baseP p W (Polynomial.C a) = baseD p W a := by
  simp [baseP]

theorem baseP_X (p : ℕ) (W : Ideal (MRing ι)) :
    baseP p W Polynomial.X = Ideal.Quotient.mk _ yN := by
  simp [baseP]

theorem quotA_baseP (p : ℕ) (W : Ideal (MRing ι)) (g : Polynomial (MRing ι ⧸ W)) :
    quotA p W (baseP p W g) = AdjoinRoot.of _ g := by
  have h : (quotA p W).comp (baseP p W) = AdjoinRoot.of (quadP p W) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [RingHom.comp_apply, baseP_C, baseD_mk, quotA_mk, toA_inc]
    · rw [RingHom.comp_apply, baseP_X, quotA_mk, toA_yN]
  exact RingHom.congr_fun h g

theorem baseMap_injective (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] :
    Function.Injective (baseP p W) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h0 : AdjoinRoot.of (quadP p W) g = 0 := by
    rw [← quotA_baseP, hg, map_zero]
  rw [← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at h0
  obtain ⟨q, hq⟩ := h0
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, Polynomial.C_eq_zero] at hq
    exact hq
  · have h1 := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_C, (quadraticPolynomial_monic p W).natDegree_mul' hq0, quadraticPolynomial_natDegree] at h1
    omega

theorem mk_quad_eq_zero (p : ℕ) (W : Ideal (MRing ι)) :
    Ideal.Quotient.mk (twist p W) (quad p) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem baseMap_isIntegralElem_xN (p : ℕ) (W : Ideal (MRing ι)) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) xN) := by
  refine ⟨quadP p W, quadraticPolynomial_monic p W, ?_⟩
  rw [← mk_quad_eq_zero p W]
  have hp : (Ideal.Quotient.mk (twist p W)) (MvPolynomial.C (p : ℤ)) =
      (p : MRing (Tb ι) ⧸ twist p W) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quadP, quad, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_add, baseP_X, map_intCast,
    Int.cast_natCast, hp, map_natCast, Polynomial.eval₂_natCast]

theorem baseMap_isIntegralElem_X (p : ℕ) (W : Ideal (MRing ι)) (q : Σ o, Tb ι o) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) (X q)) := by
  obtain ⟨o, j⟩ := q
  cases o with
  | none =>
    revert j
    change ∀ j : Fin 2, _
    intro j
    fin_cases j
    · exact baseMap_isIntegralElem_xN p W
    · have h := RingHom.isIntegralElem_map (baseP p W) (x := Polynomial.X)
      rw [baseP_X] at h
      exact h
  | some k =>
    have h : Ideal.Quotient.mk (twist p W) (X ⟨some k, j⟩ : MRing (Tb ι)) =
        baseP p W (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, j⟩))) := by
      rw [baseP_C, baseD_mk]
      simp [inc, oldIdx]
    rw [h]
    exact RingHom.isIntegralElem_map _

theorem baseMap_isIntegral (p : ℕ) (W : Ideal (MRing ι)) (b : MRing (Tb ι) ⧸ twist p W) :
    (baseP p W).IsIntegralElem b := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction f using MvPolynomial.induction_on
  · rw [eq_intCast MvPolynomial.C, map_intCast, ← map_intCast (baseP p W)]
    exact RingHom.isIntegralElem_map _
  · rw [map_add]
    exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  · rw [map_mul]
    exact RingHom.IsIntegralElem.mul _ ‹_› (baseMap_isIntegralElem_X p W _)

theorem ringKrullDim_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  haveI : W.IsPrime := hW
  haveI : Nontrivial (MRing ι ⧸ W) := inferInstance
  haveI : IsNoetherianRing (MRing ι) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial ((k : K) × ι k) ℤ))
  letI : Algebra (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) := (baseP p W).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) :=
    ⟨fun b => baseMap_isIntegral p W b⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (baseMap_injective p W),
    Polynomial.ringKrullDim_of_isNoetherianRing]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_twist_succ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply hinj m' ⟨k, i⟩

theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_isMultiHomogIdeal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), IsMultiHomogIdeal W → IsMultiHomogIdeal (twist p W) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Abstract

variable {R R' : Type*} [CommRing R] [CommRing R']

theorem length_cut_of_flat (φ : R →+* R') (q : R') (J W : Ideal R) [W.IsPrime]
    (W' : Ideal R') [W'.IsPrime] (hW' : W' = W.map φ ⊔ Ideal.span {q}) (hc : W'.comap φ = W)
    (hflat : ((Ideal.Quotient.mk (Ideal.span {q})).comp φ).Flat) :
    Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (R' ⧸ (J.map φ ⊔ Ideal.span {q}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  let I : Ideal R' := Ideal.span {q}
  let π : R' →+* R' ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let ψ : R →+* R' ⧸ I := π.comp φ
  have hker : RingHom.ker π = I := Ideal.mk_ker
  have hIW : I ≤ W' := hW' ▸ le_sup_right
  let P : Ideal (R' ⧸ I) := W'.map π
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective hπ (by rw [hker]; exact hIW)
  have hPc : W' = P.comap π := by
    show W' = (W'.map π).comap π
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hIW]
  have hPψ : W = P.comap ψ := by
    have h : P.comap ψ = (P.comap π).comap φ := (Ideal.comap_comap φ π).symm
    rw [h, ← hPc, hc]
  have hPmap : W.map ψ = P := by
    show W.map (π.comp φ) = W'.map π
    rw [hW', Ideal.map_sup, ← Ideal.map_map]
    have : (Ideal.span {q} : Ideal R').map π = ⊥ := Ideal.map_quotient_self I
    rw [this, sup_bot_eq]
  let L := Localization.localRingHom W P ψ hPψ
  have hLflat : L.Flat := RingHom.Flat.localRingHom hflat P W hPψ
  have hcomp : L.comp (algebraMap R (Localization.AtPrime W)) =
      (algebraMap (R' ⧸ I) (Localization.AtPrime P)).comp ψ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hPψ z
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map L =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map, hPmap, IsLocalization.AtPrime.map_eq_maximalIdeal P]
  have hJ : (J.map (algebraMap R (Localization.AtPrime W))).map L =
      (J.map ψ).map (algebraMap (R' ⧸ I) (Localization.AtPrime P)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  have hkerE : RingHom.ker ((Ideal.Quotient.mk (J.map ψ)).comp π) = J.map φ ⊔ I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    show ((J.map (π.comp φ))).comap π = _
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker]
  let e : (R' ⧸ (J.map φ ⊔ I)) ≃+* ((R' ⧸ I) ⧸ J.map ψ) :=
    (Ideal.quotEquivOfEq hkerE.symm).trans (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (J.map ψ)).comp π) (Ideal.Quotient.mk_surjective.comp hπ))
  have he : ∀ (s : R') (x : R' ⧸ (J.map φ ⊔ I)), e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J.map ψ) (π (s * y)) =
      Ideal.Quotient.mk (J.map ψ) (π s) * Ideal.Quotient.mk (J.map ψ) (π y)
    rw [map_mul, map_mul]
  rw [GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective π hπ P W' hPc _ _
      e.toAddEquiv he,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ← hJ]
  exact GroundTheory.Heights₂.Heights.Inter.BCMultProof.length_quot_map_of_flat L hLflat hmax _

end Abstract

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toPoly : MRing (Tb ι) →+* Polynomial (Polynomial (MRing ι)) :=
  (aeval (fun q : Σ o, Tb ι o => match q with
    | ⟨none, j⟩ => (![Polynomial.X, Polynomial.C Polynomial.X] : Fin 2 → _) j
    | ⟨some k, i⟩ => Polynomial.C (Polynomial.C (X ⟨k, i⟩))) :
      MRing (Tb ι) →ₐ[ℤ] Polynomial (Polynomial (MRing ι))).toRingHom

def ofPoly : Polynomial (Polynomial (MRing ι)) →+* MRing (Tb ι) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom inc yN) xN

theorem toPoly_xN : toPoly (xN : MRing (Tb ι)) = Polynomial.X := by
  simp only [toPoly, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_yN : toPoly (yN : MRing (Tb ι)) = Polynomial.C Polynomial.X := by
  simp only [toPoly, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_comp_inc : (toPoly.comp inc : MRing ι →+* _) = Polynomial.C.comp Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [toPoly, inc]
  · intro i; simp [toPoly, inc, oldIdx]

theorem toPoly_inc (f : MRing ι) : toPoly (inc f) = Polynomial.C (Polynomial.C f) :=
  congrArg (fun g => g f) (toPoly_comp_inc (ι := ι))

theorem ofPoly_comp_toPoly : (ofPoly.comp toPoly : MRing (Tb ι) →+* _) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [toPoly, ofPoly]
  · rintro ⟨o, i⟩
    cases o with
    | none =>
      change Fin 2 at i
      fin_cases i
      · have : (X ⟨none, (0 : Fin 2)⟩ : MRing (Tb ι)) = xN := rfl
        simp [this, toPoly_xN, ofPoly]
      · have : (X ⟨none, (1 : Fin 2)⟩ : MRing (Tb ι)) = yN := rfl
        simp [this, toPoly_yN, ofPoly]
    | some k =>
      simp [toPoly, ofPoly, inc, oldIdx]

theorem toPoly_comp_ofPoly :
    (toPoly.comp ofPoly : Polynomial (Polynomial (MRing ι)) →+* _) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun f => ?_
      simp [ofPoly, toPoly_inc]
    · simp [ofPoly, toPoly_yN]
  · simp [ofPoly, toPoly_xN]

def polyEquiv : MRing (Tb ι) ≃+* Polynomial (Polynomial (MRing ι)) :=
  RingEquiv.ofRingHom toPoly ofPoly toPoly_comp_ofPoly ofPoly_comp_toPoly

theorem toPoly_quad (p : ℕ) : ∃ s : Polynomial (MRing ι),
    toPoly (quad p : MRing (Tb ι)) = Polynomial.X ^ 2 + Polynomial.C s := by
  refine ⟨Polynomial.C (C (p : ℤ)) * Polynomial.X ^ 2, ?_⟩
  have h : toPoly (C (p : ℤ) : MRing (Tb ι)) =
      Polynomial.C (Polynomial.C (C (p : ℤ) : MRing ι)) := by
    simpa [inc] using toPoly_inc (ι := ι) (C (p : ℤ) : MRing ι)
  simp [quad, toPoly_xN, toPoly_yN, h]

theorem flat_quad (p : ℕ) :
    ((Ideal.Quotient.mk (Ideal.span {quad p})).comp inc :
      MRing ι →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat := by
  obtain ⟨s, hs⟩ := toPoly_quad (ι := ι) p
  let g : Polynomial (Polynomial (MRing ι)) := Polynomial.X ^ 2 + Polynomial.C s
  have hg : g.Monic := Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))
  have : Module.Free (Polynomial (MRing ι)) (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  have h1 : (Polynomial.C : MRing ι →+* Polynomial (MRing ι)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (MRing ι) (Polynomial (MRing ι)))
  have h2 : (AdjoinRoot.of g).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (Polynomial (MRing ι)) (AdjoinRoot g))
  let E : (MRing (Tb ι) ⧸ Ideal.span {quad p}) ≃+* AdjoinRoot g :=
    Ideal.quotientEquiv _ _ (polyEquiv (ι := ι)) (by
      rw [Ideal.map_span, Set.image_singleton]
      show Ideal.span {g} = Ideal.span {toPoly (quad p)}
      rw [hs])
  have h3 : (E.symm : AdjoinRoot g →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat :=
    RingHom.Flat.of_bijective E.symm.bijective
  have hcomp : (Ideal.Quotient.mk (Ideal.span {quad p})).comp inc =
      (E.symm : AdjoinRoot g →+* _).comp ((AdjoinRoot.of g).comp Polynomial.C) := by
    refine RingHom.ext fun f => ?_
    show Ideal.Quotient.mk _ (inc f) = E.symm (AdjoinRoot.of g (Polynomial.C f))
    rw [RingEquiv.eq_symm_apply]
    show Ideal.Quotient.mk _ (toPoly (inc f)) = _
    rw [toPoly_inc]
    rfl
  rw [hcomp]
  exact (h1.comp h2).comp h3

theorem multAt_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (J W : Ideal (MRing ι)) (hW : W ∈ J.minimalPrimes) (hT : (twist p W).IsPrime) :
    multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  have hWp : W.IsPrime := hW.1.1
  unfold multAt
  rw [dif_pos hT, dif_pos hWp]
  exact congrArg ENat.toNat (length_cut_of_flat inc (quad p) J W (twist p W) rfl
    (comap_inc_twist p W) (flat_quad p))

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multAt_twist_quad_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (J W : Ideal (MRing ι)), W ∈ J.minimalPrimes → (twist p W).IsPrime → multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem twist_sup_span_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} (h : P ⊔ Ideal.span {s} ≤ W) :
    twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ twist p W := by
  refine sup_le (sup_le ?_ le_sup_right) ?_
  · exact (Ideal.map_mono (le_sup_left.trans h)).trans le_sup_left
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (h (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self s))))

theorem sup_span_le_comap_inc {K : Type} {ι : K → Type} (p : ℕ) {P : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) :
    P ⊔ Ideal.span {s} ≤ Q.comap inc := by
  refine sup_le ?_ ?_
  · exact Ideal.map_le_iff_le_comap.mp ((le_sup_left.trans le_sup_left).trans h)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem twist_le_of_map_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) (hW : W ≤ Q.comap inc) :
    twist p W ≤ Q :=
  sup_le (Ideal.map_le_iff_le_comap.mpr hW) ((le_sup_right.trans le_sup_left).trans h)

theorem horizontal_divSupp_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (P : Ideal (MRing ι)) (s : MRing ι)
    (hp : ∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) :
    {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} =
      twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  ext W'
  constructor
  · rintro ⟨⟨hmin, hrel⟩, hhor⟩
    have hprime : W'.IsPrime := hmin.1.1
    have hle := hmin.1.2
    have hc : P ⊔ Ideal.span {s} ≤ W'.comap inc := sup_span_le_comap_inc p hle
    have : (W'.comap inc).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨W0, hW0, hW0le⟩ := Ideal.exists_minimalPrimes_le hc
    have hrel0 : IsRelevant W0 := by
      intro k
      obtain ⟨i, hi⟩ := hrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have := hW0le h
      simpa [inc, oldIdx] using this
    have hhor0 : IsHorizontal W0 := by
      rw [IsHorizontal, eq_bot_iff] at hhor ⊢
      intro n hn
      refine hhor ?_
      have h1 : (C n : MRing ι) ∈ W'.comap inc := hW0le hn
      simpa [inc] using h1
    have hmem : W0 ∈ divSupp P s := ⟨hW0, hrel0⟩
    refine ⟨W0, ⟨hmem, hhor0⟩, ?_⟩
    have htw : twist p W0 ≤ W' := twist_le_of_map_le p hle hW0le
    exact le_antisymm htw (hmin.2 ⟨hp W0 hmem hhor0, twist_sup_span_le p hW0.1.2⟩ htw)
  · rintro ⟨W, ⟨⟨hmin, hrel⟩, hhor⟩, rfl⟩
    have hprime : W.IsPrime := hmin.1.1
    refine ⟨⟨⟨⟨hp W ⟨hmin, hrel⟩ hhor, twist_sup_span_le p hmin.1.2⟩, ?_⟩,
      isRelevant_twist p hprime.ne_top hrel⟩, isHorizontal_twist p hhor⟩
    rintro Q ⟨hQ, hQle⟩ hQtw
    have hcomap : Q.comap inc ≤ W := by
      have := Ideal.comap_mono (f := inc) hQtw
      rwa [comap_inc_twist] at this
    have := hQ
    have hW : W ≤ Q.comap inc :=
      hmin.2 ⟨Ideal.comap_isPrime _ _, sup_span_le_comap_inc p hQle⟩ hcomap
    exact twist_le_of_map_le p hQle hW

end GlobalTheory.CompanionTheory.Ar.Tw
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_divSupp_twist_eq_image : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (P : Ideal (MRing ι)) (s : MRing ι), (∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) → {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} = twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conj_contDiff {T : Type} [Fintype T] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : T → ℂ => fun q => starRingEnd ℂ (z q)) :=
  contDiff_pi.2 fun q => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ q)

theorem oldPart_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (basePart₂ : ((Σ o, Tb ι o) → ℂ) → (Σ k, ι k) → ℂ) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℂ _

theorem chi_contDiffOn (p : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi (ι := ι) p) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (0 : Fin 2)⟩) := contDiff_apply ℝ ℂ _
  have hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (1 : Fin 2)⟩) := contDiff_apply ℝ ℂ _
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im) :=
    Complex.imCLM.contDiff.comp (hx.mul (Complex.conjCLE.contDiff.comp hy))
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2) :=
    (hx.norm_sq ℝ).add (hy.norm_sq ℝ)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im /
        (‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
    refine hnum.contDiffOn.div hden.contDiffOn fun u hu => ?_
    have h0 : 0 ≤ ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 := by positivity
    have h1 : 0 ≤ ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 := by positivity
    have key : ∀ j : Fin 2, u ⟨none, j⟩ ≠ 0 →
        ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 ≠ 0 := by
      intro j hj
      have hpos : 0 < ‖u ⟨none, j⟩‖ ^ 2 := by positivity
      have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases hj2 with rfl | rfl <;> exact ne_of_gt (by linarith)
    obtain ⟨i, hi⟩ := hu none
    exact key i hi
  exact (contDiffOn_const.add (contDiffOn_const.mul hq))

theorem chi_conj (p : ℕ) (u : (Σ o, Tb ι o) → ℂ) :
    chi p (fun q => starRingEnd ℂ (u q)) = 1 - chi p u := by
  have him : ((starRingEnd ℂ) (u ⟨none, (0 : Fin 2)⟩) *
      (starRingEnd ℂ) ((starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩))).im =
      -(u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im := by
    rw [Complex.conj_conj, ← Complex.conj_im, map_mul, Complex.conj_conj]
  simp only [chi, RCLike.norm_conj, him]
  ring

theorem chi_vPlus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vPlus p)) = 1 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vPlus p) ⟨none, (0 : Fin 2)⟩ = cRoot p := rfl
  have e1 : glue z (vPlus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, hn, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem chi_vMinus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vMinus p)) = 0 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vMinus p) ⟨none, (0 : Fin 2)⟩ = -cRoot p := rfl
  have e1 : glue z (vMinus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, norm_neg, hn, Complex.neg_im, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem conj_ne {T : Type} {B : T → Type} {u : (Σ o, B o) → ℂ} {o : T} (h : ∃ i, u ⟨o, i⟩ ≠ 0) :
    ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa using hi⟩

theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  exact hA'.comp (s := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (conj_contDiff (T := Σ k, ι k)).contDiffOn fun z hz k => conj_ne (hz k)

theorem twLine_smooth (p : ℕ) (A : HermLine ι) (hA : IsSmoothHerm A) :
    IsSmoothHerm (twLine p A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h (basePart₂ u)) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA' oldPart_contDiff.contDiffOn
      fun _ hu k => oldPart_ne hu k
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h fun q => starRingEnd ℂ (basePart₂ u q))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA'
      (conj_contDiff.comp oldPart_contDiff).contDiffOn
      fun _ hu k => conj_ne (oldPart_ne hu k)
  have l1 := h1.log fun u hu => (A.pos _ (oldPart_ne hu)).ne'
  have l2 := h2.log fun u hu => (A.pos _ fun k => conj_ne (oldPart_ne hu k)).ne'
  have hc := chi_contDiffOn (ι := ι) p
  have hE := (((hc.mul l1).add (((contDiffOn_const (c := (1 : ℝ))).sub hc).mul l2))).exp
  refine ContDiffOn.congr hE fun u hu => ?_
  change twH p A u = _
  have hu' : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 := hu
  rw [twH, if_pos hu']

theorem twLine_conj (p : ℕ) (A : HermLine ι) : IsConjInvariantH (twLine p A) := by
  intro u
  change twH p A (fun q => starRingEnd ℂ (u q)) = twH p A u
  have hsame : (∀ o, ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0) ↔ ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 :=
    forall_congr' fun o => exists_congr fun i => by simp
  by_cases hu : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0
  · rw [twH, twH, if_pos (hsame.mpr hu), if_pos hu, chi_conj]
    have e1 : basePart₂ (fun q => starRingEnd ℂ (u q)) = fun q => starRingEnd ℂ (basePart₂ u q) := rfl
    have e2 : (fun q => starRingEnd ℂ (basePart₂ (fun q => starRingEnd ℂ (u q)) q)) = basePart₂ u := by
      funext q; simp [basePart₂]
    rw [e2, e1]
    congr 1
    ring
  · rw [twH, twH, if_neg (fun h => hu (hsame.mp h)), if_neg hu]

theorem glue_block {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {v : Fin 2 → ℂ}
    (hv : v 1 ≠ 0) : ∀ o, ∃ i, glue z v ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact ⟨(1 : Fin 2), hv⟩
  | some k => exact hz k

theorem twLine_vPlus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vPlus p)) = A.h z := by
  change twH p A _ = _
  have hv : vPlus p 1 ≠ 0 := by simp [vPlus]
  have ho : basePart₂ (glue z (vPlus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vPlus p hp, ho]
  simp only [one_mul, sub_self, zero_mul, add_zero]
  exact Real.exp_log (A.pos z hz)

theorem twLine_vMinus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z := by
  change twH p A _ = A.h fun q => starRingEnd ℂ (z q)
  have hv : vMinus p 1 ≠ 0 := by simp [vMinus]
  have ho : basePart₂ (glue z (vMinus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vMinus p hp, ho]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  exact Real.exp_log (A.pos _ fun k => conj_ne (hz k))

theorem twLine_main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) :=
  fun _ _ _ _ p A hp => ⟨twLine_smooth p A, conjLine_smooth A, twLine_conj p A,
    twLine_vPlus p hp A, twLine_vMinus p hp A⟩

end GlobalTheory.CompanionTheory.Ar.Tw.Lines
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twLine_smooth_conjInvariant_glue : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem arInt_conj : SheetIndepStatement → PtsIndepStatement → GoodProjExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → arInt P s (conjLine A) (fun j => conjLine (L j)) = arInt P s A L :=
  PositivityTheory.UnitarySelfGeneration.c_arint

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem ptsIntegral_conjLine : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  intro hI K _ ι _ Q e L A s hQ hL hA hs
  exact GlobalTheory.CompanionTheory.Ar.Cmp.arInt_conj
    (fun K _ ι _ P e Ψ L A s hP hΨ hL hA hs => sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs) hI
    (fun K _ ι _ P e hP => goodProjExists K ι P e hP) K ι Q e L A s hQ hL hA hs

end GlobalTheory.CompanionTheory.Ar.Tw
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_conjLine_eq : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.ptsIntegral_conjLine
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem oldPart_mem_mcPts {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨fun k => hu.1 (some k), fun f hf => ?_⟩
  have hg : glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
    funext ⟨o, i⟩
    cases o <;> rfl
  have h1 := hu.2 (inc f) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
  have h2 := eval_inc (basePart₂ u) (fun j => u ⟨none, j⟩) f
  rw [hg] at h2
  rw [← h2]
  exact h1

theorem exists_segre_eq_embL [Nonempty K] {p : ℕ} {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    {u : (Σ o, Tb ι o) → ℂ} (hu : u ∈ mcPts (twist p Q)) {v : Fin 2 → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hv : ∀ j : Fin 2, u ⟨none, j⟩ = c * v j) :
    ∃ z ∈ mcPts Q, segre u = embL v (segre z) := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, mcPts_smul hQ (fun k => if k = k0 then c else 1)
    (fun k => by by_cases h : k = k0 <;> simp [h, hc]) (oldPart_mem_mcPts hu), ?_⟩
  funext J
  show ∏ o, u ⟨o, J o⟩ =
    (∏ k, (if k = k0 then c else 1) * basePart₂ u ⟨k, J (some k)⟩) * v (J none)
  rw [Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k0]
  have h1 : u ⟨none, J none⟩ = c * v (J none) := hv (J none)
  rw [h1]
  simp only [Finset.mem_univ, if_true]
  have h2 : ∀ k, basePart₂ u ⟨k, J (some k)⟩ = u ⟨some k, J (some k)⟩ := fun _ => rfl
  simp only [h2]
  ring

theorem new_coords {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ j : Fin 2, u ⟨none, j⟩ = c * vPlus p j) ∨
      (∀ j : Fin 2, u ⟨none, j⟩ = c * vMinus p j)) := by
  have hq : u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
    rw [← eval_quad]
    exact hu.2 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hy : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    intro h0
    rw [h0] at hq
    have hx : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using hq
    obtain ⟨i, hi⟩ := hu.1 none
    have hall : ∀ j : Fin 2, u ⟨none, j⟩ = 0 := by
      intro j
      fin_cases j
      · exact hx
      · exact h0
    exact hi (hall i)
  refine ⟨u ⟨none, (1 : Fin 2)⟩, hy, ?_⟩
  have hf : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = 0 := by
    have : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) =
        u ⟨none, (0 : Fin 2)⟩ ^ 2 - u ⟨none, (1 : Fin 2)⟩ ^ 2 * cRoot p ^ 2 := by ring
    rw [this, cRoot_sq, ← hq]
    ring
  rcases mul_eq_zero.mp hf with h | h
  · left
    intro j
    fin_cases j
    · simpa [vPlus] using sub_eq_zero.mp h
    · simp [vPlus]
  · right
    intro j
    fin_cases j
    · simpa [vMinus] using eq_neg_of_add_eq_zero_left h
    · simp [vMinus]

theorem embL_image_subset {e : ℕ} {p : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) :
    embL v '' fibre Q (pj v Ψ) y ⊆ fibre (twist p Q) Ψ y := by
  rintro _ ⟨w, ⟨z, hz, rfl, hΨ⟩, rfl⟩
  exact ⟨glue z v, glue_mem_mcPts hz hv hv1, segre_glue z v, hΨ⟩

theorem fibre_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (Q : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ),
    p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q →
    fibre (twist p Q) Ψ y =
      embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪
        embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  intro K _ ι _ p Q e Ψ y _ hK hQ
  refine Set.Subset.antisymm ?_ (Set.union_subset
    (embL_image_subset (vPlus_root p) (by simp [vPlus]))
    (embL_image_subset (vMinus_root p) (by simp [vMinus])))
  rintro w ⟨u, hu, rfl, hΨ⟩
  obtain ⟨c, hc, h | h⟩ := new_coords hu
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inl ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vPlus p) (segre z)) = _
    rw [← hs]
    exact hΨ
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inr ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vMinus p) (segre z)) = _
    rw [← hs]
    exact hΨ

end GlobalTheory.CompanionTheory.Ar.Tw.Fib
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_twist_eq_union_embeddings : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ), p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q → fibre (twist p Q) Ψ y = embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪ embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Tw.Fib.fibre_twist
end

section
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Tw.Main
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory

theorem exists_prime_noRoot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (S : Set (Ideal (MRing ι))) (hS : S.Finite) (h : ∀ W ∈ S, W.IsPrime ∧ IsHorizontal W) :
    ∃ p : ℕ, p.Prime ∧ ∀ W ∈ S, NoRoot p W := by
  classical
  have hbad : ∀ W ∈ S, {p : ℕ | p.Prime ∧ ∃ a b : MRing ι ⧸ W, b ≠ 0 ∧ a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0}.Finite := by
    intro W hW
    obtain ⟨hp, hh⟩ := h W hW
    haveI := hp
    haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
    haveI : CharZero (MRing ι ⧸ W) := by
      refine ⟨fun a b hab => ?_⟩
      have h0 : (C (((a : ℤ) - (b : ℤ))) : MRing ι) ∈ W := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [sub_eq_zero] using hab
      have h1 : ((a : ℤ) - (b : ℤ)) ∈ W.comap (C : ℤ →+* MRing ι) := h0
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hh, Ideal.mem_bot] at h1
      omega
    exact GlobalTheory.T.finite_primes_sum_squares_zero _ _ (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective
  have hfin : (⋃ W ∈ S, {p : ℕ | p.Prime ∧ ∃ a b : MRing ι ⧸ W, b ≠ 0 ∧ a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0}).Finite :=
    hS.biUnion hbad
  obtain ⟨p, hp, hpn⟩ := (Nat.infinite_setOf_prime.diff hfin).nonempty
  refine ⟨p, hp, fun W hW a b hab => ?_⟩
  by_contra hb
  apply hpn
  refine Set.mem_biUnion hW ⟨hp, Ideal.Quotient.mk W a, Ideal.Quotient.mk W b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · have := Ideal.Quotient.eq_zero_iff_mem.mpr hab
    simpa using this

theorem isArithVar_twist {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) (hR : NoRoot p Q) :
    IsArithVar (twist p Q) d := by
  obtain ⟨hK, hM, hH, hd⟩ := hQ
  refine ⟨⟨none⟩, ⟨GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p Q hM.1 hR, GlobalTheory.T.twist_isMultiHomogIdeal K ι p Q hM.2.1,
    isRelevant_twist p hM.1.ne_top hM.2.2⟩, isHorizontal_twist p hH, ?_⟩
  haveI := hM.1
  rw [GlobalTheory.T.ringKrullDim_twist_succ K ι p Q hM.1, hd, Fintype.card_option, ← add_assoc]
  push_cast
  rfl

theorem inc_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {s : MRing ι} (hs : s ∉ Q) : inc s ∉ twist p Q := fun h =>
  hs (by rw [← comap_inc_twist p Q]; exact h)

theorem oldIdx_injective {K : Type} {ι : K → Type} : Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  obtain rfl : k = k' := Option.some_injective _ (congrArg Sigma.fst h)
  have : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [this]

theorem isMultiHomog_inc {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (inc s) (fun o => match o with | none => 0 | some k => a k) := by
  classical
  intro m hm o
  simp only [inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hm
  rw [MvPolynomial.support_rename_of_injective oldIdx_injective] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases o with
  | none =>
    show ∑ i, (Finsupp.mapDomain oldIdx m0) ⟨none, i⟩ = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨q, hq⟩
    cases hq
  | some k =>
    show ∑ i, (Finsupp.mapDomain oldIdx m0) ⟨some k, i⟩ = a k
    rw [← hs m0 hm0 k]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply (f := oldIdx (ι := ι)) oldIdx_injective m0 ⟨k, i⟩

theorem isSectionOn_twist {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hs : IsSectionOn Q A s) :
    IsSectionOn (twist p Q) (twLine p A) (inc s) := by
  obtain ⟨a, ha, hh, hn⟩ := hs
  refine ⟨fun o => match o with | none => 0 | some k => a k, fun o => ?_, isMultiHomog_inc hh, inc_notMem hn⟩
  cases o with
  | none => rfl
  | some k => exact ha k

theorem embL_inj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {v : Fin 2 → ℂ}
    (h1 : v 1 = 1) : Function.Injective (embL v : (((k : K) → ι k) → ℂ) → _) := by
  intro w w' h
  funext j
  have := congrFun h (fun o => match o with | none => (1 : Fin 2) | some k => j k)
  simpa [embL, h1] using this

theorem twist_integral (hI : PtsIntegrableStatement) (hD : PtsIndepStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ} (hp : p ≠ 0)
    {Q : Ideal (MRing ι)} {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hQ : IsArithVar Q (e + 1)) (hR : NoRoot p Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn Q A s) :
    ptsIntegral (twist p Q) (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) =
      ptsIntegral Q (pot L) (logNorm A s) +
        ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) := by
  classical
  have hQ' : IsArithVar (twist p Q) (e + 1) := isArithVar_twist hQ hR
  have hKne : Nonempty K := hQ.1
  have hF := fun B : HermLine ι => GlobalTheory.T.twLine_smooth_conjInvariant_glue K ι p B hp
  have hL' : ∀ j, IsSmoothHerm (twLine p (L j)) := fun j => (hF _).1 (hL j)
  have hA' : IsSmoothHerm (twLine p A) := (hF _).1 hA
  have hLc : ∀ j, IsSmoothHerm (conjLine (L j)) := fun j => (hF _).2.1 (hL j)
  have hAc : IsSmoothHerm (conjLine A) := (hF _).2.1 hA
  have hs' : IsSectionOn (twist p Q) (twLine p A) (inc s) := isSectionOn_twist hs
  have hsc : IsSectionOn Q (conjLine A) s := hs
  obtain ⟨Ψ, hΨ⟩ := goodProjExists (Option K) (Tb ι) (twist p Q) e hQ'
  have good : ∀ v : Fin 2 → ℂ, v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0 → v 1 ≠ 0 → IsGoodProj Q (pj v Ψ) := by
    intro v hv hv1 z hz
    have := hΨ _ (glue_mem_mcPts hz hv hv1)
    rw [segre_glue] at this
    exact this
  have v1p : vPlus p 1 = 1 := by simp [vPlus]
  have v1m : vMinus p 1 = 1 := by simp [vMinus]
  have gp := good _ (vPlus_root p) (by rw [v1p]; exact one_ne_zero)
  have gm := good _ (vMinus_root p) (by rw [v1m]; exact one_ne_zero)
  have atOf : ∀ {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι')}
      {Φ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {M : Fin e → HermLine ι'}
      {B : HermLine ι'} {t : MRing ι'}, IsArithVar P (e + 1) → IsGoodProj P Φ →
      (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm B → IsSectionOn P B t →
      ptsIntegral P (pot M) (logNorm B t) = ptsIntegralAt P Φ (pot M) (logNorm B t) := by
    intro K' _ ι' _ P Φ M B t h1 h2 h3 h4 h5
    have hex : ∃ Φ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Φ := ⟨Φ, h2⟩
    unfold ptsIntegral
    rw [dif_pos hex]
    exact hD K' ι' P e _ Φ M B t h1 hex.choose_spec h2 h3 h4 h5
  rw [atOf hQ' hΨ hL' hA' hs', atOf hQ gp hL hA hs, atOf hQ gm hLc hAc hsc]
  have sp := GlobalTheory.T.twist_height_integral_decomposition K ι p Q e Ψ (fun j => twLine p (L j)) (twLine p A) L A s (vPlus p) hp hQ hQ' hΨ hL' hA' hs'
    (Or.inl rfl) (fun j z hz => (hF _).2.2.2.1 z hz.1) (fun z hz => (hF _).2.2.2.1 z hz.1)
  have sm := GlobalTheory.T.twist_height_integral_decomposition K ι p Q e Ψ (fun j => twLine p (L j)) (twLine p A) (fun j => conjLine (L j)) (conjLine A) s
    (vMinus p) hp hQ hQ' hΨ hL' hA' hs' (Or.inr rfl) (fun j z hz => (hF _).2.2.2.2 z hz.1)
    (fun z hz => (hF _).2.2.2.2 z hz.1)
  have hae : ∀ᵐ y, (∑ᶠ w ∈ fibre (twist p Q) Ψ y, sheetDensity (twist p Q) Ψ (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) y w) =
      (∑ᶠ w ∈ fibre Q (pj (vPlus p) Ψ) y, sheetDensity Q (pj (vPlus p) Ψ) (pot L) (logNorm A s) y w) +
      ∑ᶠ w ∈ fibre Q (pj (vMinus p) Ψ) y, sheetDensity Q (pj (vMinus p) Ψ) (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) y w := by
    filter_upwards [sp, sm] with y hpl hmi
    have fpl := fibreFinite K ι Q e _ hQ gp y
    have fmi := fibreFinite K ι Q e _ hQ gm y
    have hdis : Disjoint (embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y)
        (embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', he⟩
      have hc : cRoot p ≠ 0 := by
        simp [cRoot, Real.sqrt_eq_zero', hp, Nat.pos_of_ne_zero hp]
      have hww : w' = w := by
        funext j
        have := congrFun he (fun o => match o with | none => (1 : Fin 2) | some k => j k)
        simpa [embL, v1p, v1m] using this
      subst hww
      have hz : w' = 0 := by
        funext j
        have := congrFun he (fun o => match o with | none => (0 : Fin 2) | some k => j k)
        simp only [embL, vPlus, vMinus, LinearMap.coe_mk, AddHom.coe_mk] at this
        have h2 : w' j * (2 * cRoot p) = 0 := by
          have h3 : w' j * (-cRoot p) = w' j * cRoot p := by simpa using this
          linear_combination -h3
        simpa [hc] using h2
      obtain ⟨z, -, -, h⟩ := hw
      rw [hz, map_zero] at h
      have := congrFun h 0
      simp at this
    rw [GlobalTheory.T.fibre_twist_eq_union_embeddings K ι p Q e Ψ y hp hKne hQ.2.1.2.1, finsum_mem_union hdis (fpl.image _) (fmi.image _),
      finsum_mem_image (embL_inj v1p).injOn, finsum_mem_image (embL_inj v1m).injOn]
    simp only [hpl, hmi]
  unfold ptsIntegralAt
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add
    (hI K ι Q e _ L A s hQ gp hL hA hs) (hI K ι Q e _ _ _ s hQ gm hLc hAc hsc)]

theorem twist_double (hI : PtsIntegrableStatement) (hD : PtsIndepStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ} (hp : p ≠ 0)
    {Q : Ideal (MRing ι)} {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hQ : IsArithVar Q (e + 1)) (hR : NoRoot p Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn Q A s) :
    ptsIntegral (twist p Q) (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) =
      2 * ptsIntegral Q (pot L) (logNorm A s) := by
  rw [twist_integral hI hD hp hQ hR hL hA hs, GlobalTheory.T.ptsIntegral_conjLine_eq hD K ι Q e L A s hQ hL hA hs]
  ring

theorem pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (B : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons B L : Fin (e + 1) → HermLine ι) =
      Fin.cons (fun z => Real.log (B.h z)) (pot L) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem tw_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (p : ℕ)
    (B : HermLine ι) (L : Fin e → HermLine ι) :
    (fun j => twLine p ((Fin.cons B L : Fin (e + 1) → HermLine ι) j)) =
      (Fin.cons (twLine p B) (fun j => twLine p (L j)) : Fin (e + 1) → HermLine (Tb ι)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem logNorm_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (B : HermLine ι) : logNorm (invLine B) 1 = fun z => Real.log (B.h z) := by
  funext z
  simp [logNorm, invLine]

theorem logNorm_tw_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ)
    (B : HermLine ι) : logNorm (twLine p (invLine B)) (inc 1) = fun z => Real.log ((twLine p B).h z) := by
  classical
  funext z
  have hh : (twLine p (invLine B)).h z = ((twLine p B).h z)⁻¹ := by
    show twH p (invLine B) z = (twH p B z)⁻¹
    unfold twH
    split_ifs with h
    · rw [← Real.exp_neg]
      congr 1
      simp only [invLine, Real.log_inv]
      ring
    · simp
  simp [logNorm, hh]

theorem isSectionOn_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRing ι)} (hQ : Q ≠ ⊤) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn Q (invLine B) 1 := by
  refine ⟨0, fun k => by simp [invLine, hB], fun m hm k => ?_, fun h => hQ ((Ideal.eq_top_iff_one _).mpr h)⟩
  have : m = 0 := by
    by_contra h0
    classical
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm h0)] at hm
    exact hm rfl
  simp [this]

theorem isSmooth_inv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (invLine B) :=
  ContDiffOn.inv hB fun z hz => (B.pos z hz).ne'

theorem tw_cons_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {B : HermLine ι} {L : Fin e → HermLine ι} (hB : IsSmoothHerm B) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (e + 1) → HermLine ι) j) := fun j => by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hB
  · exact hL i

theorem poincareLelong_of_inv :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv →
      GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  intro hRK hInv K _ ι _ P n L A B s hP hL hA hB hBa hs
  classical
  have hI : PtsIntegrableStatement := GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hRK
  have hD : PtsIndepStatement := ptsIndep_of (GlobalTheory.T.resolution_exists_of_resolution_statement hRK) resBridge
  have hPp : P.IsPrime := hP.2.1.1
  set H : Set (Ideal (MRing ι)) := {W | W ∈ divSupp P s ∧ IsHorizontal W} with hH
  have hHfin : H.Finite := (divSupp_finite P s).subset fun W h => h.1
  have hHar : ∀ W ∈ H, IsArithVar W (n + 1) := fun W h =>
    (divSuppArith K ι P (n + 1) A s W hP hs h.1).1 h.2
  obtain ⟨p, hp, hpS⟩ := exists_prime_noRoot (insert P H) (hHfin.insert P) (by
    rintro W (rfl | hW)
    · exact ⟨hPp, hP.2.2.1⟩
    · exact ⟨(hHar W hW).2.1.1, hW.2⟩)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hRP : NoRoot p P := hpS P (Set.mem_insert _ _)
  have hRW : ∀ W ∈ H, NoRoot p W := fun W h => hpS W (Set.mem_insert_of_mem _ h)
  have hF := fun C : HermLine ι => GlobalTheory.T.twLine_smooth_conjInvariant_glue K ι p C hp0
  have hP' : IsArithVar (twist p P) (n + 2) := isArithVar_twist hP hRP
  have hInv' := hInv (Option K) (Tb ι) (twist p P) n (fun j => twLine p (L j)) (twLine p A) (twLine p B)
    (inc s) hP' (fun j => (hF _).1 (hL j)) ((hF _).1 hA) ((hF _).1 hB)
    (fun j => (hF _).2.2.1) (hF _).2.2.1 (hF _).2.2.1
    (by funext o; cases o with
        | none => rfl
        | some k => exact congrFun hBa k)
    (isSectionOn_twist hs)

  have e1 := twist_double hI hD hp0 (e := n + 1) (L := Fin.cons B L) (A := A) (s := s) hP hRP
    (tw_cons_smooth hB hL) hA hs
  rw [tw_cons, pot_cons, pot_cons] at e1
  have e3 := twist_double hI hD hp0 (e := n + 1) (L := Fin.cons A L) (A := invLine B) (s := 1) hP hRP
    (tw_cons_smooth hA hL) (isSmooth_inv hB) (isSectionOn_inv_one hPp.ne_top hBa)
  rw [tw_cons, pot_cons, pot_cons, logNorm_inv_one, logNorm_tw_inv_one] at e3
  have e2 : ∀ W ∈ H, ptsIntegral (twist p W) (pot fun j => twLine p (L j))
      (fun z => Real.log ((twLine p B).h z)) = 2 * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    intro W hW
    have hWa := hHar W hW
    have := twist_double hI hD hp0 (e := n) (L := L) (A := invLine B) (s := 1) hWa (hRW W hW) hL
      (isSmooth_inv hB) (isSectionOn_inv_one hWa.2.1.1.ne_top hBa)
    rwa [logNorm_inv_one, logNorm_tw_inv_one] at this
  have hsup : twist p P ⊔ Ideal.span {inc s} =
      (P ⊔ Ideal.span {s}).map inc ⊔ Ideal.span {quad p} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, twist, sup_right_comm]
  have hdiv := GlobalTheory.T.horizontal_divSupp_twist_eq_image K ι p P s (fun W hW hh =>
    GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p W (hHar W ⟨hW, hh⟩).2.1.1 (hRW W ⟨hW, hh⟩))
  have hsum : (∑ᶠ (W') (_ : W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'),
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z))) =
      2 * ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    have h1 : (∑ᶠ (W') (_ : W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'),
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z))) =
        ∑ᶠ W' ∈ {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'},
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z)) := rfl
    have h2 : (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) =
        ∑ᶠ W ∈ H, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := rfl
    rw [h1, h2, hdiv, finsum_mem_image (twist_injective p).injOn, mul_finsum_mem]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [e2 W hW, hsup, GlobalTheory.T.multAt_twist_quad_eq K ι p _ W hW.1.1 (GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p W (hHar W hW).2.1.1 (hRW W hW))]
    ring
  have hInv2 : ptsIntegral (twist p P)
      (Fin.cons (fun z => Real.log ((twLine p B).h z)) (pot fun j => twLine p (L j)))
      (logNorm (twLine p A) (inc s)) = _ := hInv'
  rw [e1, hsum, e3] at hInv2
  linarith

end GlobalTheory.CompanionTheory.Ar.Tw.Main
end
end
