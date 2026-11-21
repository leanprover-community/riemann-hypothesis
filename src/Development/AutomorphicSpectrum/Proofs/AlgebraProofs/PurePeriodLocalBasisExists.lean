import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsIntegralPosDefPerturbation
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.SesquilinearFractions.UltrametricNormProdSubLt
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsOrthogonalLocalBasisExtension
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsUnitValueSkewHermitian
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsRealDifferentGenerator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominator
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferent
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasis
import Development.WeilBound.CoreStatements.SesquilinearFractions.GramSignatureOrthogonalSplit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility

section
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem frame_congr_posDef_on_places : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef :=
  @PositivityTheory.Xgf.exists_integral_posDef_perturbation

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_posDef_perturbation : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places
end

section
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_eq_of_entries_close : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I :=
  @PositivityTheory.Xgf.ultrametric_det_norm_stable

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.norm_det_eq_of_entries_close
end

section
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sylvester

theorem neg_posDef_of_compl_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef :=
  @PositivityTheory.Xgf.negDef_block_of_posDef

end GlobalTheory.CompanionTheory.Ar.Fl.Sylvester
end

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  exact @PositivityTheory.Xgf.exists_orthogonal_local_basis
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis
end

section
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem skewHermitian_congr_diag : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  exact @PositivityTheory.Xgf.skew_hermitian_diagonalizable

end GlobalTheory.CompanionTheory.CommAlg
end

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_diagonalizable : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag
end

section
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem conj_not_trivial_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ m : Ideal (𝓞 E), m.IsMaximal → ∃ a : 𝓞 E, a - bar a ∉ m :=
  PositivityTheory.Xgf.exists_not_mem_sub_conj

end GlobalTheory.CompanionTheory.CommAlg
end

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_not_mem_sub_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ m : Ideal (𝓞 E), m.IsMaximal → ∃ a : 𝓞 E, a - bar a ∉ m := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.conj_not_trivial_mod_maximal
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocR

open NumberField

variable (E : Type) [Field E] [NumberField E]

def locRing (ℓ : Nat.Primes) : Subring E where
  carrier := {x | ∃ (n : ℕ) (a : 𝓞 E), ¬ (ℓ : ℕ) ∣ n ∧ (n : E) * x = a}
  mul_mem' := by
    rintro x y ⟨n, a, hn, ha⟩ ⟨m, b, hm, hb⟩
    refine ⟨n * m, a * b, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul ℓ.2).1 h with h | h
      exacts [hn h, hm h]
    · rw [Nat.cast_mul, show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from map_mul (algebraMap (𝓞 E) E) a b, ← ha, ← hb]
      ring
  one_mem' := ⟨1, 1, by simpa using ℓ.2.one_lt.ne', by simp⟩
  add_mem' := by
    rintro x y ⟨n, a, hn, ha⟩ ⟨m, b, hm, hb⟩
    refine ⟨n * m, (m : 𝓞 E) * a + (n : 𝓞 E) * b, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul ℓ.2).1 h with h | h
      exacts [hn h, hm h]
    · rw [Nat.cast_mul, show (((m : 𝓞 E) * a + (n : 𝓞 E) * b : 𝓞 E) : E) = (m : E) * (a : E) + (n : E) * (b : E) by
        simp [map_add, map_mul (algebraMap (𝓞 E) E)], ← ha, ← hb]
      ring
  zero_mem' := ⟨1, 0, by simpa using ℓ.2.one_lt.ne', by simp⟩
  neg_mem' := by
    rintro x ⟨n, a, hn, ha⟩
    refine ⟨n, -a, hn, ?_⟩
    rw [show ((-a : 𝓞 E) : E) = -(a : E) from map_neg (algebraMap (𝓞 E) E) a, ← ha]
    ring

variable {E}

theorem coe_mem_locRing (ℓ : Nat.Primes) (a : 𝓞 E) : (a : E) ∈ locRing E ℓ :=
  ⟨1, a, by simpa using ℓ.2.one_lt.ne', by simp⟩

theorem inv_natCast_mem_locRing {ℓ : Nat.Primes} {n : ℕ} (hn : ¬ (ℓ : ℕ) ∣ n) :
    ((n : E))⁻¹ ∈ locRing E ℓ := by
  have h0 : (n : E) ≠ 0 := by
    rintro h
    exact hn (by simp [Nat.cast_eq_zero.1 h])
  exact ⟨n, 1, hn, by simp [h0]⟩

variable (E)

def conjLoc [IsCMField E] (ℓ : Nat.Primes) (x : locRing E ℓ) : locRing E ℓ :=
  ⟨IsCMField.complexConj E (x : E), by
    obtain ⟨n, a, hn, ha⟩ := x.2
    refine ⟨n, ⟨IsCMField.complexConj E (a : E), ?_⟩, hn, ?_⟩
    · exact (a.2).map (IsCMField.complexConj E)
    · rw [show ((n : E)) = IsCMField.complexConj E (n : E) from (map_natCast _ n).symm, ← map_mul, ha]
      rfl⟩

instance instStarLocRing [IsCMField E] (ℓ : Nat.Primes) : StarRing (locRing E ℓ) where
  star := conjLoc E ℓ
  star_involutive x := Subtype.ext (IsCMField.complexConj_apply_apply E (x : E))
  star_mul x y := Subtype.ext (by
    change IsCMField.complexConj E ((x : E) * (y : E)) =
      IsCMField.complexConj E (y : E) * IsCMField.complexConj E (x : E)
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add (IsCMField.complexConj E) (x : E) (y : E))

variable {E}

@[simp] theorem coe_star_locRing [IsCMField E] {ℓ : Nat.Primes} (x : locRing E ℓ) :
    ((star x : locRing E ℓ) : E) = IsCMField.complexConj E (x : E) := rfl

def ofInt (ℓ : Nat.Primes) : 𝓞 E →+* locRing E ℓ :=
  (algebraMap (𝓞 E) E).codRestrict (locRing E ℓ) (coe_mem_locRing ℓ)

@[simp] theorem coe_ofInt (ℓ : Nat.Primes) (a : 𝓞 E) : ((ofInt ℓ a : locRing E ℓ) : E) = (a : E) := rfl

theorem isUnit_natCast_loc {ℓ : Nat.Primes} {n : ℕ} (hn : ¬ (ℓ : ℕ) ∣ n) :
    IsUnit ((n : locRing E ℓ)) := by
  have h0 : (n : E) ≠ 0 := fun h => hn (by simp [Nat.cast_eq_zero.1 h])
  refine IsUnit.of_mul_eq_one (⟨(n : E)⁻¹, inv_natCast_mem_locRing hn⟩ : locRing E ℓ) (Subtype.ext ?_)
  simp [h0]

theorem exists_natCast_mul_eq {ℓ : Nat.Primes} (x : locRing E ℓ) :
    ∃ (n : ℕ) (a : 𝓞 E), ¬ (ℓ : ℕ) ∣ n ∧ (n : locRing E ℓ) * x = ofInt ℓ a := by
  obtain ⟨n, a, hn, ha⟩ := x.2
  exact ⟨n, a, hn, Subtype.ext (by simpa using ha)⟩

theorem comap_injective {ℓ : Nat.Primes} {m m' : Ideal (locRing E ℓ)} (hm' : m'.IsPrime) (hm : m.IsPrime)
    (h : m.comap (ofInt ℓ) = m'.comap (ofInt ℓ)) : m ≤ m' := by
  intro x hx
  obtain ⟨n, a, hn, e⟩ := exists_natCast_mul_eq x
  have h1 : a ∈ m.comap (ofInt ℓ) := by
    rw [Ideal.mem_comap, ← e]
    exact m.mul_mem_left _ hx
  rw [h, Ideal.mem_comap, ← e] at h1
  exact (hm'.mem_or_mem h1).resolve_left fun h2 => hm'.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (isUnit_natCast_loc hn))

theorem natCast_mem_comap {ℓ : Nat.Primes} {m : Ideal (locRing E ℓ)} (hm : m.IsPrime)
    (h0 : m.comap (ofInt ℓ) ≠ ⊥) : ((ℓ : ℕ) : 𝓞 E) ∈ m.comap (ofInt ℓ) := by
  haveI : (m.comap (ofInt ℓ)).IsPrime := Ideal.comap_isPrime _ _
  set P := m.comap (ofInt ℓ) with hP
  have hN : Ideal.absNorm P ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨k, n, hn, e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN (ℓ : ℕ) ℓ.2.one_lt.ne'
  have h1 : ((Ideal.absNorm P : ℕ) : 𝓞 E) ∈ P := Ideal.absNorm_mem P
  rw [e, Nat.cast_mul, Nat.cast_pow] at h1
  rcases (inferInstance : P.IsPrime).mem_or_mem h1 with h2 | h2
  · exact (inferInstance : P.IsPrime).mem_of_pow_mem _ h2
  · exfalso
    rw [hP, Ideal.mem_comap, map_natCast] at h2
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (isUnit_natCast_loc hn))

theorem finite_maxSpec (ℓ : Nat.Primes) : Finite (MaximalSpectrum (locRing E ℓ)) := by
  classical
  have hℓ : Ideal.span {((ℓ : ℕ) : 𝓞 E)} ≠ 0 := by
    simpa using ℓ.2.ne_zero
  haveI : Fintype {P : Ideal (𝓞 E) // P ∣ Ideal.span {((ℓ : ℕ) : 𝓞 E)}} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd _ hℓ
  let f : MaximalSpectrum (locRing E ℓ) → Option {P : Ideal (𝓞 E) // P ∣ Ideal.span {((ℓ : ℕ) : 𝓞 E)}} :=
    fun m => if h : m.asIdeal.comap (ofInt ℓ) = ⊥ then none else
      some ⟨m.asIdeal.comap (ofInt ℓ), Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2
        (natCast_mem_comap m.isMaximal.isPrime h))⟩
  refine Finite.of_injective f fun m m' e => ?_
  have hc : m.asIdeal.comap (ofInt ℓ) = m'.asIdeal.comap (ofInt ℓ) := by
    by_cases h : m.asIdeal.comap (ofInt ℓ) = ⊥ <;> by_cases h' : m'.asIdeal.comap (ofInt ℓ) = ⊥
    · rw [h, h']
    · simp [f, h, h'] at e
    · simp [f, h, h'] at e
    · simpa [f, h, h'] using e
  exact MaximalSpectrum.ext (m.isMaximal.eq_of_le m'.isMaximal.ne_top
    (comap_injective m'.isMaximal.isPrime m.isMaximal.isPrime hc))

section Form

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable [IsCMField E]

theorem exists_sub_star_notMem (H : Host E) (ℓ : Nat.Primes) (m : Ideal (locRing E ℓ)) (hm : m.IsMaximal) :
    ∃ a : locRing E ℓ, a - star a ∉ m := by
  haveI : (m.comap (ofInt ℓ)).IsPrime := Ideal.comap_isPrime _ _
  have key : ∃ a : 𝓞 E, a - H.bar a ∉ m.comap (ofInt ℓ) := by
    by_cases h0 : m.comap (ofInt ℓ) = ⊥
    · obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
      obtain ⟨a, ha⟩ := GlobalTheory.T.exists_not_mem_sub_conj E H.bar H.bar_eq H.unram M hM
      refine ⟨a, ?_⟩
      rw [h0, Ideal.mem_bot]
      intro h
      exact ha (h ▸ M.zero_mem)
    · exact GlobalTheory.T.exists_not_mem_sub_conj E H.bar H.bar_eq H.unram _ (Ideal.IsPrime.isMaximal inferInstance h0)
  obtain ⟨a, ha⟩ := key
  refine ⟨ofInt ℓ a, fun h => ha ?_⟩
  rw [Ideal.mem_comap, map_sub]
  convert h using 2
  exact Subtype.ext (H.bar_eq a)

variable {H : Host E}

theorem sesq_zero_left (D : Datum H) (y : D.La) : sesq D 0 y = 0 := by
  have := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1 0 0 y
  simpa using this

theorem sesq_zero_right (D : Datum H) (y : D.La) : sesq D y 0 = 0 := by
  have := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1 0 y 0
  simpa using this

theorem sesq_sum_left (D : Datum H) {ι : Type} (s : Finset ι) (a : ι → 𝓞 E) (x : ι → D.La) (y : D.La) :
    sesq D (∑ i ∈ s, a i • x i) y = ∑ i ∈ s, (a i : E) * sesq D (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_left]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1, ih,
      (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1]

theorem sesq_sum_right (D : Datum H) {ι : Type} (s : Finset ι) (a : ι → 𝓞 E) (x : ι → D.La) (y : D.La) :
    sesq D y (∑ i ∈ s, a i • x i) = ∑ i ∈ s, IsCMField.complexConj E (a i : E) * sesq D y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1, ih,
      (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1]

theorem eq_zero_of_sesq_eq_zero (D : Datum H) (y : D.La) (h : ∀ z, sesq D y z = 0) : y = 0 := by
  apply D.unimod.1
  rw [map_zero]
  ext z
  have := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).1 1 y z
  rw [one_smul, h z] at this
  simpa using this.symm

theorem gram_det_ne_zero (D : Datum H) {I : Type} [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (hx : IsLocBasis (𝓞 E) ℓ x) : (gramE D x).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) v
  choose c hc using hb
  have hb0 : ((b : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero b.2
    exact_mod_cast this
  have hcv : ∀ i, (c i : E) = (b : 𝓞 E) * v i := fun i => by
    have := hc i
    rw [Algebra.smul_def] at this
    exact this
  set y : D.La := ∑ i, c i • x i with hy
  have h1 : ∀ n, sesq D y (x n) = 0 := by
    intro n
    rw [hy, sesq_sum_left]
    have := congrFun hv0 n
    simp only [Matrix.vecMul, dotProduct, gramE, Matrix.of_apply, Pi.zero_apply] at this
    simp only [hcv, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  obtain ⟨hli, N, hN, hspan⟩ := hx
  have hN0 : (N : E) ≠ 0 := fun h => hN (by simp [Nat.cast_eq_zero.1 h])
  have h2 : ∀ w ∈ Submodule.span (𝓞 E) (Set.range x), sesq D y w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨n, rfl⟩ := hw; exact h1 n
    | zero => exact sesq_zero_right D y
    | add u w _ _ hu hw => rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1, hu, hw, add_zero]
    | smul a w _ hw => rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, hw, mul_zero]
  have h3 : y = 0 := by
    refine eq_zero_of_sesq_eq_zero D y fun z => ?_
    have := h2 _ (hspan z)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1] at this
    simpa [hN0] using this
  have h4 := Fintype.linearIndependent_iff.1 hli c h3
  apply hv
  funext i
  have := hcv i
  rw [h4 i] at this
  simpa [hb0] using this.symm

end Form

section Norm

theorem norm_le_one {ℓ : Nat.Primes} (x : locRing E ℓ) (j : E →+* ℂ_[ℓ]) : ‖j (x : E)‖ ≤ 1 :=
  (GlobalTheory.T.padic_integral_iff_denominator E ℓ (x : E)).2 x.2 j

theorem norm_eq_one_of_isUnit {ℓ : Nat.Primes} {u : locRing E ℓ} (hu : IsUnit u) (j : E →+* ℂ_[ℓ]) :
    ‖j (u : E)‖ = 1 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : ‖j (u : E)‖ * ‖j (v : E)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Subring.coe_mul, hv]
    simp
  have h2 := norm_le_one u j
  have h3 := norm_le_one v j
  nlinarith [norm_nonneg (j (u : E)), norm_nonneg (j (v : E))]

theorem isUnit_of_norm_eq_one {ℓ : Nat.Primes} (u : locRing E ℓ) (h0 : (u : E) ≠ 0)
    (h : ∀ j : E →+* ℂ_[ℓ], ‖j (u : E)‖ = 1) : IsUnit u := by
  have h1 : (u : E)⁻¹ ∈ locRing E ℓ := (GlobalTheory.T.padic_integral_iff_denominator E ℓ _).1 fun j => by
    rw [map_inv₀, norm_inv, h j, inv_one]
  exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing E ℓ) (Subtype.ext (by simp [h0]))

theorem exists_common_denom {ℓ : Nat.Primes} {ι : Type} [Fintype ι] (f : ι → locRing E ℓ) :
    ∃ (N : ℕ) (a : ι → 𝓞 E), ¬ (ℓ : ℕ) ∣ N ∧ ∀ i, (N : E) * f i = a i := by
  classical
  choose n a hn ha using fun i => (f i).2
  refine ⟨∏ i, n i, fun i => ((∏ k ∈ Finset.univ.erase i, n k : ℕ) : 𝓞 E) * a i, ?_, fun i => ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Nat.Prime.prime ℓ.2) _).1 h
    exact hn i hi
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), show (((∏ k ∈ Finset.univ.erase i, n k : ℕ) : 𝓞 E) * a i : 𝓞 E).val = ((∏ k ∈ Finset.univ.erase i, n k : ℕ) : E) * (a i : E) by
      simp [RingOfIntegers.coe_eq_algebraMap] , ← ha i]
    push_cast
    ring

end Norm

section Comb

theorem isLocBasis_comb {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] {ι : Type} [Fintype ι]
    [DecidableEq ι] {x : ι → M} {ℓ : ℕ} (hℓ : ℓ.Prime) (A B : Matrix ι ι O) (N : ℕ) (hN : ¬ ℓ ∣ N) (hN0 : (N : O) ≠ 0)
    (hBA : B * A = (N : O) • (1 : Matrix ι ι O)) (hx : IsLocBasis O ℓ x) :
    IsLocBasis O ℓ (fun a => ∑ k, A a k • x k) := by
  obtain ⟨hli, n, hn, hspan⟩ := hx
  have hdet : A.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hBA
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ hN0 this.symm
  refine ⟨?_, n * N, fun h => ?_, fun y => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : ∑ k, (∑ a, c a * A a k) • x k = 0 := by
      rw [← hc]
      simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    have h2 := Fintype.linearIndependent_iff.1 hli _ h1
    have h3 : Matrix.vecMul c A = 0 := by
      funext k
      simpa [Matrix.vecMul, dotProduct] using h2 k
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet h3
    intro i
    exact congrFun this i
  · rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    exacts [hn h, hN h]
  · have h1 : ∀ k, N • x k ∈ Submodule.span O (Set.range fun a => ∑ k, A a k • x k) := by
      intro k
      have h2 : N • x k = ∑ a, B k a • ∑ l, A a l • x l := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul]
        have h3 : ∀ l, ∑ a, B k a * A a l = (B * A) k l := fun l => (Matrix.mul_apply).symm
        simp only [h3, hBA, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        simp [ite_smul, ← Nat.cast_smul_eq_nsmul O]
      rw [h2]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    have h4 : ∀ w ∈ Submodule.span O (Set.range x), N • w ∈ Submodule.span O (Set.range fun a => ∑ k, A a k • x k) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw => obtain ⟨k, rfl⟩ := hw; exact h1 k
      | zero => simp
      | add u w _ _ hu hw => rw [smul_add]; exact Submodule.add_mem _ hu hw
      | smul a w _ hw => rw [smul_comm]; exact Submodule.smul_mem _ a hw
    rw [mul_comm, mul_smul]
    exact h4 _ (hspan y)

end Comb

section Main

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix

variable [IsCMField E]

theorem exists_diag_basis (H : Host E) (D : Datum H) (n : ℕ) (hn : n = D.p + D.q) (ℓ : Nat.Primes) :
    ∃ (x : Fin n → D.La) (δ : 𝓞 E), IsLocBasis (𝓞 E) ℓ x ∧ (δ : E) ≠ 0 ∧
      (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (δ : E)‖ =
        logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧
      (∀ a b, a ≠ b → sesq D (x a) (x b) = 0) ∧
      ∀ a, ∃ u : locRing E ℓ, IsUnit u ∧ (δ : E) * sesq D (x a) (x a) = u := by
  haveI := finite_maxSpec (E := E) ℓ
  haveI := D.fin
  haveI := D.proj
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_local_basis' E D.La (Fin n) (ℓ : ℕ) ℓ.2 (by simp [D.rank, hn])
  obtain ⟨δ, hδ, hδ0, hδc, hδj⟩ := GlobalTheory.T.exists_real_different_generator E H.unram ℓ
  have hδE : (δ : E) ≠ 0 := by exact_mod_cast hδ0
  have hint := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.2 δ hδ
  have hmem : ∀ a b, (δ : E) * sesq D (x a) (x b) ∈ locRing E ℓ := fun a b => by
    obtain ⟨c, hc⟩ := hint (x a) (x b)
    rw [hc]
    exact coe_mem_locRing ℓ c
  let G : Matrix (Fin n) (Fin n) (locRing E ℓ) := Matrix.of fun a b => ⟨_, hmem a b⟩
  have hGc : ∀ a b, ((G a b : locRing E ℓ) : E) = (δ : E) * sesq D (x a) (x b) := fun _ _ => rfl
  have hG : Gᴴ = -G := by
    ext a b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply, coe_star_locRing, hGc, Subring.coe_neg, hGc, map_mul, hδc,
      (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x b) (x a)]
    ring
  have hGdet : ((G.det : locRing E ℓ) : E) = (δ : E) ^ n * (gramE D x).det := by
    have h1 : (locRing E ℓ).subtype.mapMatrix G = (δ : E) • gramE D x := by
      ext a b
      rfl
    have h2 := RingHom.map_det (locRing E ℓ).subtype G
    rw [h1, Matrix.det_smul, Fintype.card_fin] at h2
    exact h2
  have hd0 := gram_det_ne_zero D x ℓ ℓ.2 hx
  have hGu : IsUnit G.det := by
    refine isUnit_of_norm_eq_one _ (by rw [hGdet]; exact mul_ne_zero (pow_ne_zero _ hδE) hd0) fun j => ?_
    have h1 := GlobalTheory.T.gram_determinant_log_different E H D (Fin n) x ℓ hx j
    have h2 := hδj j
    have h3 : 0 < ‖j (δ : E)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hδE)
    have h4 : 0 < ‖j (gramE D x).det‖ := norm_pos_iff.2 ((map_ne_zero j).2 hd0)
    rw [hGdet, map_mul, map_pow, norm_mul, norm_pow]
    refine Real.eq_one_of_pos_of_log_eq_zero (by positivity) ?_
    rw [Real.log_mul (by positivity) h4.ne', Real.log_pow, h1, h2, Fintype.card_fin]
    ring
  obtain ⟨T, hTu, hTd⟩ := GlobalTheory.T.skew_hermitian_diagonalizable _ n G hG hGu (exists_sub_star_notMem H ℓ)
  obtain ⟨N, A, hN, hA⟩ := exists_common_denom (ι := Fin n × Fin n) (fun q => T q.1 q.2)
  obtain ⟨N', B, hN', hB⟩ := exists_common_denom (ι := Fin n × Fin n) (fun q => T⁻¹ q.1 q.2)
  have hN0 : (N : E) ≠ 0 := fun h => hN (by simp [Nat.cast_eq_zero.1 h])
  have hN'0 : (N' : E) ≠ 0 := fun h => hN' (by simp [Nat.cast_eq_zero.1 h])
  let Am : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun a b => A (a, b)
  let Bm : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun a b => B (a, b)
  have hinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hTu
  have hBA : Bm * Am = (((N' * N : ℕ)) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
    ext a b
    have h1 : (((T⁻¹ * T) a b : locRing E ℓ) : E) = ∑ k, ((T⁻¹ a k : locRing E ℓ) : E) * (T k b : E) := by
      rw [Matrix.mul_apply]
      simp
    rw [hinv] at h1
    have h2 : ((Bm * Am) a b : E) = ∑ k, (B (a, k) : E) * (A (k, b) : E) := by
      rw [Matrix.mul_apply]
      simp [Bm, Am, RingOfIntegers.coe_eq_algebraMap]
    rw [h2]
    simp only [← hA, ← hB]
    have h3 : ∑ k, ((N' : E) * ((T⁻¹ a k : locRing E ℓ) : E)) * ((N : E) * (T k b : E)) =
        (N' : E) * N * ∑ k, ((T⁻¹ a k : locRing E ℓ) : E) * (T k b : E) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h3, ← h1]
    by_cases hab : a = b
    · subst hab
      simp [RingOfIntegers.coe_eq_algebraMap]
    · simp [hab, RingOfIntegers.coe_eq_algebraMap]
  have hNN : ¬ (ℓ : ℕ) ∣ N' * N := fun h => by
    rcases (Nat.Prime.dvd_mul ℓ.2).1 h with h | h
    exacts [hN' h, hN h]
  have hNN0 : (((N' * N : ℕ)) : 𝓞 E) ≠ 0 := by
    intro h
    have : (((N' * N : ℕ)) : E) = 0 := by
      simpa [RingOfIntegers.coe_eq_algebraMap] using congrArg (algebraMap (𝓞 E) E) h
    rw [Nat.cast_mul] at this
    exact mul_ne_zero hN'0 hN0 this
  have hx' := isLocBasis_comb ℓ.2 Am Bm (N' * N) hNN hNN0 hBA hx
  set x' : Fin n → D.La := fun a => ∑ k, Am a k • x k with hx'def
  set W := T * G * Tᴴ with hW
  have hconjN : ∀ a b, IsCMField.complexConj E ((Am a b : 𝓞 E) : E) =
      (N : E) * IsCMField.complexConj E ((T a b : locRing E ℓ) : E) := fun a b => by
    have : ((Am a b : 𝓞 E) : E) = (N : E) * (T a b : E) := (hA (a, b)).symm
    rw [this, map_mul, map_natCast]
  have hWc : ∀ a b, (W a b : E) = ∑ l, (∑ k, (T a k : E) * ((δ : E) * sesq D (x k) (x l))) *
      IsCMField.complexConj E ((T b l : locRing E ℓ) : E) := by
    intro a b
    rw [hW, Matrix.mul_apply]
    simp [Matrix.mul_apply, hGc]
  have key : ∀ a b, (δ : E) * sesq D (x' a) (x' b) = (N : E) ^ 2 * (W a b : E) := by
    intro a b
    rw [hWc, hx'def]
    simp only []
    rw [sesq_sum_left]
    simp only [sesq_sum_right, hconjN]
    have hAa : ∀ k, ((Am a k : 𝓞 E) : E) = (N : E) * (T a k : E) := fun k => (hA (a, k)).symm
    simp only [hAa, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdetW : IsUnit W.det := by
    rw [hW, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (hTu.mul hGu).mul hTu.star
  have hWu : ∀ a, IsUnit (W a a) := by
    intro a
    have h1 : W.det = ∏ i, W i i := by
      conv_lhs => rw [← hTd.diagonal_diag]
      rw [Matrix.det_diagonal]
      rfl
    rw [h1] at hdetW
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => W i i) (Finset.mem_univ a)) hdetW
  refine ⟨x', δ, hx', hδE, hδj, fun a b hab => ?_, fun a => ⟨(N : locRing E ℓ) ^ 2 * W a a,
    ((isUnit_natCast_loc hN).pow 2).mul (hWu a), ?_⟩⟩
  · have h1 := key a b
    rw [show (W a b) = 0 from hTd hab] at h1
    simpa [hδE] using h1
  · rw [key a a]
    simp

end Main

section Target

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem exists_locBasis_first_unimodular :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes),
      p + q = D.p + D.q → ∃ x : Fin p ⊕ Fin q → D.La, IsLocBasis (𝓞 E) ℓ x ∧ (gramE D (x ∘ Sum.inl)).det ≠ 0 ∧
        ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inl)).det‖ =
          -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ H D p q ℓ hpq
  obtain ⟨x, δ, hx, hδ0, hδj, hoff, hdiag⟩ := exists_diag_basis H D (p + q) hpq ℓ
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let s : Fin p → E := fun a => sesq D (x (e (.inl a))) (x (e (.inl a)))
  have hg : gramE D ((x ∘ e) ∘ Sum.inl) = Matrix.diagonal s := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [gramE, s]
    · have : e (.inl a) ≠ e (.inl b) := fun h => hab (Sum.inl_injective (e.injective h))
      simp [gramE, hab, hoff _ _ this]
  have hs0 : ∀ a, s a ≠ 0 := by
    intro a
    obtain ⟨u, hu, e1⟩ := hdiag (e (.inl a))
    intro h
    have h1 : (u : E) = 0 := by rw [← e1]; simp [s] at h; simp [h]
    exact hu.ne_zero (Subtype.ext h1)
  have hsj : ∀ (j : E →+* ℂ_[ℓ]) a, Real.log ‖j (s a)‖ = -logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
    intro j a
    obtain ⟨u, hu, e1⟩ := hdiag (e (.inl a))
    have h1 := norm_eq_one_of_isUnit hu j
    rw [← e1, map_mul, norm_mul] at h1
    have h2 : 0 < ‖j (δ : E)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hδ0)
    have h3 : 0 < ‖j (s a)‖ := norm_pos_iff.2 ((map_ne_zero j).2 (hs0 a))
    have h4 := congrArg Real.log h1
    rw [Real.log_mul h2.ne' h3.ne', Real.log_one, hδj j] at h4
    linarith
  refine ⟨x ∘ e, ⟨hx.1.comp e e.injective, ?_⟩, ?_, fun j => ?_⟩
  · obtain ⟨n, hn, hsp⟩ := hx.2
    exact ⟨n, hn, by simpa [Set.range_comp, e.surjective.range_eq] using hsp⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hs0 a
  · rw [hg, Matrix.det_diagonal, map_prod, norm_prod,
      Real.log_prod (fun a _ => (norm_pos_iff.2 ((map_ne_zero j).2 (hs0 a))).ne')]
    simp only [hsj j]
    simp

end Target

end GlobalTheory.CompanionTheory.Ar.Fl.LocR
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_basis_gram_determinant_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes), p + q = D.p + D.q → ∃ x : Fin p ⊕ Fin q → D.La, IsLocBasis (𝓞 E) ℓ x ∧ (gramE D (x ∘ Sum.inl)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inl)).det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.LocR.exists_locBasis_first_unimodular
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.gram_signature_orthogonal_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La), IsTypeFn H p q ty → p + q = D.p + D.q → LinearIndependent (𝓞 E) x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef ∧ (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef) → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsPure hP x := by
  first | exact @PositivityTheory.Xgf.gram_signature_orthogonal_split | exact PositivityTheory.Xgf.gram_signature_orthogonal_split
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_signature_orthogonal_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La), IsTypeFn H p q ty → p + q = D.p + D.q → LinearIndependent (𝓞 E) x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef ∧ (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef) → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsPure hP x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.gram_signature_orthogonal_split
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.SignTau

open GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_type {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ}) (f : Fin g → ℂ)
    (hf : ∀ j, ty j ≠ σ → f j = 0) : ∑ j, f j = ∑ a, f (e a) := by
  classical
  have h1 : ∑ a, f (e a) = ∑ i : {i // ty i = σ}, f i := Equiv.sum_comp e (fun i : {i // ty i = σ} => f i)
  rw [h1, ← Finset.sum_subtype (p := fun j => ty j = σ) (Finset.univ.filter fun j => ty j = σ) (by simp) f,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · exact hf j h

theorem hermForm_tyPart {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (M : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (tyPart ty σ z) (tyPart ty σ w) =
      ∑ a, ∑ b, z (e a) * M (e a) (e b) * star (w (e b)) := by
  classical
  rw [hermForm_eq_sum]
  have h1 : ∀ j, ty j ≠ σ → ∑ k, tyPart ty σ z j * M j k * star (tyPart ty σ w k) = 0 := by
    intro j hj
    apply Finset.sum_eq_zero
    intro k _
    simp [tyPart, hj]
  rw [sum_type ty σ e _ h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ k, ty k ≠ σ → tyPart ty σ z (e a) * M (e a) k * star (tyPart ty σ w k) = 0 := by
    intro k hk
    simp [tyPart, hk]
  rw [sum_type ty σ e _ h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [tyPart, (e a).2, (e b).2]

theorem star_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (z w : Fin g → ℂ) :
    star (hermForm M z w) = hermForm M w z := by
  rw [hermForm_eq_sum, hermForm_eq_sum]
  simp only [star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', star_mul', star_star, hM.apply]
  ring

theorem posDef_of_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) : M.PosDef := by
  refine ⟨hM, fun x hx => ?_⟩
  have hx' : star (⇑x) ≠ 0 := by
    intro h0
    apply hx
    ext i
    simpa using congrFun h0 i
  have h1 := hpos (star ⇑x) hx'
  have h2 : (starRingEnd ℂ) (hermForm M (star ⇑x) (star ⇑x)) = hermForm M (star ⇑x) (star ⇑x) :=
    star_hermForm hM _ _
  have h3 : (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) =
      ∑ i, ∑ j, star (x i) * M i j * x j := by
    rw [Finsupp.sum_fintype x (fun i xi => x.sum fun j xj => star xi * M i j * xj)
      (fun i => by simp [Finsupp.sum])]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.sum_fintype x (fun j xj => star (x i) * M i j * xj) (fun j => by simp)
  have h4 : ∑ i, ∑ j, star (x i) * M i j * x j = hermForm M (star ⇑x) (star ⇑x) := by
    rw [hermForm_eq_sum]
    simp
  rw [h3, h4, Complex.lt_def]
  exact ⟨by simpa using h1, by simp [Complex.conj_eq_iff_im.mp h2]⟩

theorem fromCols_block {I : Type} [Fintype I] {p q : ℕ} (A : Matrix I (Fin p) ℂ) (B : Matrix I (Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ =
      A * G₁ * Aᴴ - B * G₂ * Bᴴ := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

private theorem add_mul_mul_conjTranspose_add_eq_of_two_smul {r p q : ℕ} (C : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (V M N : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (key : V * ((2 : ℂ) • M) * Vᴴ = N) :
    (C * V + C * V) * M * (C * V + C * V)ᴴ = C * N * Cᴴ + C * N * Cᴴ := by
  rw [← key]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, two_smul, Matrix.mul_assoc]

theorem signature_of_factor {p q : ℕ} (M W : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) (h₁ : G₁.PosDef) (h₂ : G₂.PosDef)
    (hM : (2 : ℂ) • M = W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) (hdet : M.det ≠ 0) :
    M.IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * M * Cᴴ).PosDef) ∧
      ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * M * Cᴴ)).PosDef := by
  have hN : (Matrix.fromBlocks G₁ 0 0 (-G₂))ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [Matrix.fromBlocks_conjTranspose, h₁.1.eq, Matrix.conjTranspose_neg, h₂.1.eq,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  have hMh : M.IsHermitian := by
    have h2 : ((2 : ℂ) • M)ᴴ = (2 : ℂ) • M := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hN,
        Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul] at h2
    have h3 : (2 : ℂ) • Mᴴ = (2 : ℂ) • M := by simpa using h2
    exact smul_right_injective _ two_ne_zero h3
  have hW : IsUnit W.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h4 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, h0] at h4
    simp [hdet] at h4
  have hVW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  have hWV : Wᴴ * (W⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hVW, Matrix.conjTranspose_one]
  have key : W⁻¹ * ((2 : ℂ) • M) * (W⁻¹)ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [hM]
    calc W⁻¹ * (W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) * (W⁻¹)ᴴ
        = (W⁻¹ * W) * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Wᴴ * (W⁻¹)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by rw [hVW, hWV, Matrix.one_mul, Matrix.mul_one]
  refine ⟨hMh, ⟨Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹, ?_⟩,
    ⟨Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹, ?_⟩⟩
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, sub_zero]
    exact h₁.add h₁
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, zero_sub,
      neg_add_rev, neg_neg]
    exact h₂.add h₂

theorem conj_cmHostRoot_ne_self (H : Host E) : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [sq, Complex.mul_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.CompanionTheory.Ar.Fl.SignTau

private theorem posDef_reindex_of_hermForm_re_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}
    (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    (Matrix.of fun a b => Hm (e a) (e b)).PosDef := by
  classical
  apply GlobalTheory.CompanionTheory.Ar.Fl.SignTau.posDef_of_hermForm
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact hH.apply _ _
  · intro z hz
    let w : Fin g → ℂ := fun i => if h : ty i = σ then z (e.symm ⟨i, h⟩) else 0
    have hw : ∀ a, w (e a) = z a := fun a => by simp [w, (e a).2]
    have hw0 : ∀ i, ty i ≠ σ → w i = 0 := fun i hi => by simp [w, hi]
    have hwz : w ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hz
      exact fun h => ha (by simpa [h] using (hw a).symm)
    have key : hermForm Hm w w = hermForm (Matrix.of fun a b => Hm (e a) (e b)) z z := by
      rw [GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum, GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum]
      have h1 : ∀ j, ty j ≠ σ → ∑ k, w j * Hm j k * star (w k) = 0 := fun j hj => by
        simp [hw0 j hj]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : ∀ k, ty k ≠ σ → w (e a) * Hm (e a) k * star (w k) = 0 := fun k hk => by
        simp [hw0 k hk]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h2]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [hw]
    rw [← key]
    exact hpos w hwz

theorem GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  intro E _ _ _ H D g ty P p q X τ hP hT hX hpq hτ
  obtain ⟨-, -, -, -, Hm, hH, hpos, hEF⟩ := id hP
  obtain ⟨-, hcomp, hC⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H D g ty P Hm hP hH hEF
  have hτc : ComplexEmbedding.conjugate τ (H.rt : E) ≠ H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ]
    exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.conj_cmHostRoot_ne_self H
  let e₁ : Fin p ≃ {i // ty i = τ} := (Finite.equivFinOfCardEq ((hT τ).1 hτ)).symm
  let e₂ : Fin q ≃ {i // ty i = ComplexEmbedding.conjugate τ} :=
    (Finite.equivFinOfCardEq ((hT (ComplexEmbedding.conjugate τ)).2 hτc)).symm
  let G₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => Hm (e₁ a) (e₁ b)
  let G₂ : Matrix (Fin q) (Fin q) ℂ := (Matrix.of fun a b => Hm (e₂ a) (e₂ b))ᵀ
  let A : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ := Matrix.of fun m a => P (X m) (e₁ a)
  let B : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ := Matrix.of fun m b => star (P (X m) (e₂ b))
  have h₁ : G₁.PosDef := posDef_reindex_of_hermForm_re_pos ty τ e₁ Hm hH hpos
  have h₂ : G₂.PosDef := (posDef_reindex_of_hermForm_re_pos ty (ComplexEmbedding.conjugate τ) e₂ Hm hH hpos).transpose
  have hfac : (2 : ℂ) • ((gramE D X).map fun a => Complex.I * τ a) =
      Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ := by
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.fromCols_block]
    ext m n
    have key := hcomp τ (X m) (X n)
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty τ e₁,
      GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty (ComplexEmbedding.conjugate τ) e₂] at key
    have hA : (A * G₁ * Aᴴ) m n =
        ∑ a, ∑ b, P (X m) (e₁ a) * Hm (e₁ a) (e₁ b) * star (P (X n) (e₁ b)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, A, G₁, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hB : (B * G₂ * Bᴴ) m n =
        star (∑ a, ∑ b, P (X m) (e₂ a) * Hm (e₂ a) (e₂ b) * star (P (X n) (e₂ b))) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply, B, G₂,
        Finset.sum_mul, star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hH.apply]
    rw [Matrix.sub_apply, hA, hB, key]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [show gramE D X m n = sesq D (X m) (X n) from rfl]
    ring
  have hdetA : (gramE D X).det ≠ 0 := hC 0 (Fin p ⊕ Fin q) X (by simp [hpq]) hX
  have hdetM : ((gramE D X).map fun a => Complex.I * τ a).det ≠ 0 := by
    have hM' : ((gramE D X).map fun a => Complex.I * τ a) = Complex.I • (τ.mapMatrix (gramE D X)) := by
      ext m n
      simp [Matrix.map_apply]
    rw [hM', Matrix.det_smul, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) ((map_ne_zero τ).mpr hdetA)
  exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.signature_of_factor _ (Matrix.fromCols A B) G₁ G₂ h₁ h₂ hfac hdetM
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_gram_hermitian_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.DSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem norm_le_one_of_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) (b : 𝓞 E) : ‖j (b : E)‖ ≤ 1 :=
  norm_le_one_of_int (map_isIntegral_int j b.isIntegral_coe)

theorem norm_prime_lt (ℓ : Nat.Primes) : ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ < 1 := by
  have h : (((ℓ : ℕ) : ℂ_[ℓ])) = algebraMap ℚ_[ℓ] ℂ_[ℓ] ((ℓ : ℕ) : ℚ_[ℓ]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast ℓ.2.one_lt)

theorem exists_bound (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    ∃ r : ℝ, 0 < r ∧ Real.log r = -logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ∧
      ∀ x y, ‖j (sesq D x y)‖ ≤ r := by
  have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
    j.injective.comp (RingOfIntegers.coe_injective)
  obtain ⟨a, ha, ha0, -, hlog⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) hinj
    differentIdeal_ne_bot
  have hn : 0 < ‖j (a : E)‖ := by
    rw [norm_pos_iff]
    intro h
    exact ha0 (hinj (by simpa using h))
  refine ⟨‖j (a : E)‖⁻¹, inv_pos.2 hn, ?_, fun x y => ?_⟩
  · rw [Real.log_inv]
    exact congrArg Neg.neg hlog.symm
  · obtain ⟨b, hb⟩ := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.2 a ha x y
    have h1 : ‖j (a : E)‖ * ‖j (sesq D x y)‖ = ‖j (b : E)‖ := by rw [← norm_mul, ← map_mul, hb]
    have h2 := norm_int_le ℓ j b
    rw [← h1] at h2
    rw [← one_div, le_div_iff₀ hn]
    linarith

theorem sesq_sum_left (D : Datum H) {J : Type} (s : Finset J) (f : J → D.La) (y : D.La) :
    sesq D (∑ m ∈ s, f m) y = ∑ m ∈ s, sesq D (f m) y := by
  let φ : D.La →+ E := AddMonoidHom.mk' (fun x => sesq D x y) (fun a b => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1 a b y)
  exact map_sum φ f s

theorem sesq_sum_right (D : Datum H) {J : Type} (s : Finset J) (f : J → D.La) (y : D.La) :
    sesq D y (∑ m ∈ s, f m) = ∑ m ∈ s, sesq D y (f m) := by
  let φ : D.La →+ E := AddMonoidHom.mk' (fun x => sesq D y x) (fun a b => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1 y a b)
  exact map_sum φ f s

theorem sesq_comb (D : Datum H) {J : Type} [Fintype J] (x : J → D.La) (u v : J → 𝓞 E) :
    sesq D (∑ m, u m • x m) (∑ n, v n • x n) =
      ∑ n, (∑ m, (u m : E) * sesq D (x m) (x n)) * IsCMField.complexConj E (v n : E) := by
  rw [sesq_sum_right]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, sesq_sum_left, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun m _ => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1 _ _ _

theorem gram_comb_map (D : Datum H) (τ : E →+* ℂ) {I J : Type} [Fintype J] (x : J → D.La)
    (X : Matrix I J (𝓞 E)) :
    ((gramE D (fun a => ∑ m, X a m • x m)).map fun a => Complex.I * τ a) =
      (X.map fun a => τ (a : E)) * ((gramE D x).map fun a => Complex.I * τ a) * (X.map fun a => τ (a : E))ᴴ := by
  ext a b
  simp only [Matrix.map_apply, gramE, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sesq_comb,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, IsCMField.complexEmbedding_complexConj, starRingEnd_apply]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem norm_diff_lt (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) {r : ℝ} (hr : 0 < r)
    (hb : ∀ x y, ‖j (sesq D x y)‖ ≤ r) (u u' v v' : D.La) :
    ‖j (sesq D (u + ((ℓ : ℕ) : 𝓞 E) • v) (u' + ((ℓ : ℕ) : 𝓞 E) • v')) - j (sesq D u u')‖ < r := by
  obtain ⟨-, hl, hr', hsl, hsr, -, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have hcast : ((((ℓ : ℕ) : 𝓞 E)) : E) = ((ℓ : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) _
  have e : j (sesq D (u + ((ℓ : ℕ) : 𝓞 E) • v) (u' + ((ℓ : ℕ) : 𝓞 E) • v')) - j (sesq D u u') =
      ((ℓ : ℕ) : ℂ_[ℓ]) * (j (sesq D v u') + j (sesq D u v') + ((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')) := by
    rw [hl, hr', hr', hsl, hsl, hsr, hsr, hcast, map_natCast (IsCMField.complexConj E)]
    simp only [map_add, map_mul, map_natCast]
    ring
  have hc := norm_prime_lt ℓ
  have hc0 : 0 ≤ ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ := norm_nonneg _
  have h3 : ‖((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')‖ ≤ r := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc.le).trans (hb v v')
  have h4 : ‖j (sesq D v u') + j (sesq D u v') + ((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')‖ ≤ r :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb _ _) (hb _ _))) h3)
  rw [e, norm_mul]
  calc _ ≤ ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ * r := mul_le_mul_of_nonneg_left h4 hc0
    _ < 1 * r := mul_lt_mul_of_pos_right hc hr
    _ = r := one_mul r

theorem conj_ne (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    (ComplexEmbedding.conjugate τ) (H.rt : E) ≠ H.rt0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq := H.sqrt_neg_disc_sq
  have him : H.rt0 ≠ 0 := by
    intro h0
    rw [h0] at hsq
    simp at hsq
    exact H.d_prime.ne_zero hsq
  have h1 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re hsq
    simpa [pow_two] using this
  have h2 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im hsq
    simpa [pow_two] using this
  have h3 : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg H.rt0.re]
  rw [ComplexEmbedding.conjugate_coe_eq, h]
  intro h5
  have h6 := congrArg Complex.im h5
  simp at h6
  exact him (Complex.ext hre (by simpa using (by linarith : H.rt0.im = 0)))

theorem exists_emb (E : Type) [Field E] [NumberField E] (ℓ : Nat.Primes) : Nonempty (E →+* ℂ_[ℓ]) :=
  ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ_[ℓ]).toRingHom⟩

theorem norm_det_close (D : Datum H) (p : ℕ) (ℓ : Nat.Primes) (x x' w : Fin p → D.La)
    (hx' : ∀ a, x' a = x a + ((ℓ : ℕ) : 𝓞 E) • w a) (hx0 : (gramE D x).det ≠ 0)
    (hxn : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    (gramE D x').det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  have key : ∀ j : E →+* ℂ_[ℓ], 0 < ‖j (gramE D x').det‖ ∧ Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
    intro j
    obtain ⟨r, hr, hlog, hb⟩ := exists_bound D ℓ j
    have hd0 : 0 < ‖j (gramE D x).det‖ := norm_pos_iff.2 ((map_ne_zero j).2 hx0)
    have hdet : ‖((gramE D x).map j).det‖ = r ^ Fintype.card (Fin p) := by
      have e : ((gramE D x).map j).det = j (gramE D x).det := (RingHom.map_det j _).symm
      rw [e, Fintype.card_fin, ← Real.exp_log hd0, hxn j, ← Real.exp_log (pow_pos hr p), Real.log_pow, hlog]
      congr 1
      ring
    have h := GlobalTheory.T.ultrametric_det_norm_stable ℂ_[ℓ] (Fin p) ((gramE D x).map j) ((gramE D x').map j) r hr
      (fun a b => hb _ _) (fun a b => by
        simp only [Matrix.map_apply, gramE, Matrix.of_apply, hx']
        exact norm_diff_lt D ℓ j hr hb _ _ _ _) hdet
    have e' : ((gramE D x').map j).det = j (gramE D x').det := (RingHom.map_det j _).symm
    rw [e', Fintype.card_fin] at h
    refine ⟨by rw [h]; exact pow_pos hr p, ?_⟩
    rw [h, Real.log_pow, hlog]
    ring
  obtain ⟨j⟩ := exists_emb E ℓ
  refine ⟨fun h0 => ?_, fun j => (key j).2⟩
  have := (key j).1
  rw [h0] at this
  simp at this

theorem neg_compl (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ : D.La →+ (Fin g → ℂ)} {p q : ℕ}
    (hP₀ : IsPeriod D ty P₀) (hty : IsTypeFn H p q ty) (hpq : p + q = D.p + D.q)
    (x : Fin p ⊕ Fin q → D.La) (hli : LinearIndependent (𝓞 E) x)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0)
    (hpos : ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef) :
    (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef := by
  obtain ⟨hH, -, C, hC⟩ := GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq hτ
  have hblk : ((gramE D x).map fun a => Complex.I * τ a) =
      Matrix.fromBlocks ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a) 0 0
        ((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a) := by
    ext (a | a) (b | b)
    · simp [gramE]
    · simp [gramE, horth]
    · have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x (.inl b)) (x (.inr a))
      simp [gramE, h, horth]
    · simp [gramE]
  rw [hblk] at hC
  refine GlobalTheory.T.negDef_block_of_posDef p q _ _ C hpos ?_ hC
  ext i k
  have h := congrFun (congrFun hH (.inr i)) (.inr k)
  simpa [gramE] using h

end GlobalTheory.CompanionTheory.Ar.Fl.DSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)) (p q : ℕ) (ℓ : Nat.Primes), IsPeriod D ty P₀ → IsTypeFn H p q ty → p + q = D.p + D.q → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (x : Fin p ⊕ Fin q → D.La), IsLocBasis (𝓞 E) ℓ x ∧ IsPure hP x := by
  intro E _ _ _ H D g ty P₀ p q ℓ hP₀ hty hpq
  obtain ⟨x, hxb, hx0, hxn⟩ := GlobalTheory.T.local_basis_gram_determinant_bound E H D p q ℓ hpq
  have hli := hxb.1
  let Ψ : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}
  let M : (E →+* ℂ) → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    fun τ => (gramE D x).map fun a => Complex.I * τ a
  have hC : ∀ τ : E →+* ℂ, ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, τ ∈ Ψ → (C * M τ * Cᴴ).PosDef := by
    intro τ
    by_cases h : τ ∈ Ψ
    · obtain ⟨C, hC⟩ := (GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq h).2.1
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose C hC using hC
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_integral_posDef_perturbation E Ψ (Fin p) (Fin p ⊕ Fin q) M C (Matrix.fromCols 1 0) (ℓ : ℕ) ℓ.2.ne_zero
    (fun τ h => DSplit.conj_ne τ h)
    (fun τ h => ⟨(GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq h).1, hC τ h⟩)
  let X : Matrix (Fin p) (Fin p ⊕ Fin q) (𝓞 E) := Matrix.fromCols 1 0 + (ℓ : ℕ) • Y
  let x' : Fin p → D.La := fun a => ∑ m, X a m • x m
  let w : Fin p → D.La := fun a => ∑ m, Y a m • x m
  have hx' : ∀ a, x' a = (x ∘ Sum.inl) a + (((ℓ : ℕ) : 𝓞 E)) • w a := by
    intro a
    simp only [x', w, X, Matrix.add_apply, Matrix.smul_apply, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      nsmul_eq_mul, mul_smul, Function.comp]
    congr 1
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
  obtain ⟨hd0, hdn⟩ := DSplit.norm_det_close D p ℓ (x ∘ Sum.inl) x' w hx' hx0 hxn
  obtain ⟨x₂, hx₂, hb₂, horth⟩ := GlobalTheory.T.exists_orthogonal_local_basis E H D p q ℓ x' hpq hd0 hdn
  have hpos : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      ((gramE D (x₂ ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef := by
    intro τ hτ
    rw [hx₂, DSplit.gram_comb_map D τ x X]
    exact hY τ hτ
  obtain ⟨P, hP, hpure⟩ := GlobalTheory.T.gram_signature_orthogonal_split E H D g ty p q x₂ hty hpq hb₂.1 horth fun τ hτ =>
    ⟨hpos τ hτ, DSplit.neg_compl D hP₀ hty hpq x₂ hb₂.1 horth τ hτ (hpos τ hτ)⟩
  exact ⟨P, hP, x₂, hb₂, hpure⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_period_local_basis_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)) (p q : ℕ) (ℓ : Nat.Primes), IsPeriod D ty P₀ → IsTypeFn H p q ty → p + q = D.p + D.q → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (x : Fin p ⊕ Fin q → D.La), IsLocBasis (𝓞 E) ℓ x ∧ IsPure hP x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period
end
