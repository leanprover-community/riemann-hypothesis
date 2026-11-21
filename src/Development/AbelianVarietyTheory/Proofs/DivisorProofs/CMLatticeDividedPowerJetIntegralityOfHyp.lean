import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestLast
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzJetConj

section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeEmb.exists_equiv | exact GlobalTheory.CMTypeEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeEmb.exists_equiv <;> assumption)
end

section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  first | exact @GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | exact GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | (intros; apply GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to <;> assumption)
end

section
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatticeUp

theorem exists_mul_integral : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime →
    OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  intro E _ _ l c y hl hy
  obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele E l (y : Af E) hl fun w hw => by rw [hy w hw, map_one]
  refine ⟨M, hM, fun x hx => ?_⟩
  have hx' : algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c := hx
  have key : algebraMap E (Af E) ((M : E) * x) =
      (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (algebraMap E (Af E) (M : E) * (y : Af E)) := by
    have hyy : (↑y⁻¹ : Af E) * (y : Af E) = 1 := y.inv_mul
    rw [map_mul]
    calc algebraMap E (Af E) (M : E) * algebraMap E (Af E) x
        = algebraMap E (Af E) (M : E) * algebraMap E (Af E) x * ((↑y⁻¹ : Af E) * (y : Af E)) := by rw [hyy, mul_one]
      _ = _ := by ring
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((M : E) * x) fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((M : E) * x)]
    have h1 := GlobalTheory.CMVal.ObjModel.hatO_integral hx' v
    have h2 := hMv v
    have : (algebraMap E (Af E) ((M : E) * x)) v =
        (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) v * (algebraMap E (Af E) (M : E) * (y : Af E)) v := by
      rw [key]; rfl
    rw [show ((((M : E) * x : E)) : v.adicCompletion E) = (algebraMap E (Af E) ((M : E) * x)) v from rfl, this, map_mul]
    exact mul_le_one' h1 h2
  rw [← hb]
  exact (b.isIntegral_coe)

end GlobalTheory.HilbFam.LatticeUp
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime → OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  atlas_forward_decl GlobalTheory.HilbFam.LatticeUp.exists_mul_integral
end

section
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatDen

theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  atlas_forward_decl GlobalTheory.HilbFam.LatDen.nat_mul_integral_mem_lattice
end

section
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.CondNumber

theorem exists_mul_pow_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ M j : ℕ, ¬ l ∣ M ∧ (M : 𝓞 K) * (l : 𝓞 K) ^ j ∈ I := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨j, M, hM, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨M, j, hM, ?_⟩
  have := Ideal.absNorm_mem I
  rw [he] at this
  push_cast at this
  rwa [mul_comm] at this

theorem mem_of_forall_pow {R : Type} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {x : R}
    (h : ∀ (v : HeightOneSpectrum R) (n : ℕ), v.asIdeal ^ n ∣ I → x ∈ v.asIdeal ^ n) : x ∈ I := by
  have e := Ideal.iInf_maxPowDividing_eq (I := I) hI
  rw [← e, Submodule.mem_iInf]
  intro v
  apply h v
  rw [Ideal.dvd_iff_le]
  exact e.ge.trans (iInf_le _ v)

theorem exists_mem_condQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  intro E _ _ _ l 𝔣 Q hl h𝔣 hQ
  obtain ⟨M₁, j, hM₁, hj⟩ := exists_mul_pow_mem hl h𝔣.1
  have h1 : (M₁ : OF E) * (l : OF E) ^ a0 𝔣 l ∈ 𝔣 := by
    refine mem_of_forall_pow h𝔣.1 fun v n hn => ?_
    by_cases hv : (l : OF E) ∈ v.asIdeal
    · have hfin : FiniteMultiplicity v.asIdeal 𝔣 :=
        FiniteMultiplicity.of_not_isUnit v.irreducible.not_isUnit h𝔣.1
      have hle : n ≤ a0 𝔣 l :=
        (hfin.le_multiplicity_of_pow_dvd hn).trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime h𝔣 hv)
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hv _))
    · have h2 := Ideal.le_of_dvd hn hj
      have := v.isPrime
      rcases Ideal.IsPrime.mem_pow_mul v.asIdeal h2 with h3 | h3
      · exact Ideal.mul_mem_right _ _ h3
      · exact absurd (v.isPrime.mem_of_pow_mem _ h3) hv
  have h2 : ∀ q : HeightOneSpectrum (OF E), ∃ M : ℕ, ¬ l ∣ M ∧ (q ∈ Q → (M : OF E) ∈ q.asIdeal) := by
    intro q
    obtain ⟨M, i, hM, hi⟩ := exists_mul_pow_mem hl q.ne_bot
    refine ⟨M, hM, fun hq => ?_⟩
    rcases q.isPrime.mem_or_mem hi with h3 | h3
    · exact h3
    · exact absurd (q.isPrime.mem_of_pow_mem _ h3) (hQ q hq)
  choose N hN hNq using h2
  refine ⟨M₁ * ∏ q ∈ Q, N q, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · exact hM₁ h
    · obtain ⟨q, -, hq⟩ := (Prime.dvd_finset_prod_iff hl.prime _).1 h
      exact hN q hq
  · have h3 : (∏ q ∈ Q, (N q : OF E)) ∈ ∏ q ∈ Q, q.asIdeal := Ideal.prod_mem_prod fun q hq => hNq q hq
    have h4 := Ideal.mul_mem_mul h1 h3
    unfold condQ
    convert h4 using 1
    push_cast
    ring

end GlobalTheory.HilbFam.CondNumber
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  atlas_forward_decl GlobalTheory.HilbFam.CondNumber.exists_mem_condQ
end

section
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam

theorem isIntegral_coord_of_isIntegral (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ)
    (x : Fin 2 → FR E) (_hD : 0 < D) (hθ : IsIntegral ℤ θ)
    (hr : (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E))
    (hu : IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E))) (j : Fin 2) :
    IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  have hc : ∀ y : E, IsIntegral ℤ y → IsIntegral ℤ (IsCMField.complexConj E y) := fun y hy =>
    map_isIntegral_int (IsCMField.complexConj E) hy
  have hfix : ∀ y : FR E, IsCMField.complexConj E (y : E) = y := fun y =>
    IsCMField.complexConj_apply_eq_self E y
  set r := θ - IsCMField.complexConj E θ with hrdef
  have hri : IsIntegral ℤ r := hθ.sub (hc _ hθ)
  have h0 : IsIntegral ℤ ((x 0 : E) * r) := by
    have := hu.sub (hc _ hu)
    rw [map_add, map_mul, hfix, hfix] at this
    have e : (x 0 : E) * r = (x 0 : E) * θ + (x 1 : E) -
        ((x 0 : E) * IsCMField.complexConj E θ + (x 1 : E)) := by rw [hrdef]; ring
    rw [e]; exact this
  have h1 : IsIntegral ℤ ((x 1 : E) * r) := by
    have := (hu.mul hri).sub (h0.mul hθ)
    have e : (x 1 : E) * r = ((x 0 : E) * θ + (x 1 : E)) * r - (x 0 : E) * r * θ := by ring
    rw [e]; exact this
  have hj : IsIntegral ℤ ((x j : E) * r) := by
    fin_cases j
    · exact h0
    · exact h1
  have hD' : (D : E) = -r ^ 2 := by rw [hr]; ring
  have hinj : Function.Injective (algebraMap (FR E) E) := (algebraMap (FR E) E).injective
  have hx : algebraMap (FR E) E (x j) = (x j : E) := rfl
  constructor
  · rw [← isIntegral_algebraMap_iff hinj, map_mul, map_pow, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) ^ 2 = -((x j : E) * r * ((x j : E) * r)) := by ring
    rw [e]; exact (hj.mul hj).neg
  · rw [← isIntegral_algebraMap_iff hinj, map_mul, map_natCast, hx, hD']
    have e : -r ^ 2 * (x j : E) = -((x j : E) * r * r) := by ring
    rw [e]; exact (hj.mul hri).neg

end GlobalTheory.HilbFam
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ) (x : Fin 2 → FR E), 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E)) → ∀ j, IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  atlas_forward_decl GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral
end

section
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

noncomputable section

namespace GlobalTheory.SizeSqIntegral

theorem sz_nat_val (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  have h := GlobalTheory.SizeRat.sz_ratCast l lam (D : ℚ) (-(padicValNat l D : ℝ)) (by
    rw [padicValRat.of_nat]; simp)
  simpa using h

theorem sz_zero_of_isIntegral (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (x : ℂ)
    (h : IsIntegral ℤ x) : Sz l lam 0 x :=
  GlobalTheory.SzRules.sz_of_isIntegral 1 x (fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 hd)) (by simpa using h)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  intro l hl lam D M x _ hx
  constructor
  · apply GlobalTheory.SzRules.sz_of_sq
    have h := GlobalTheory.SzRules.sz_mul (sz_nat_val l lam D) (sz_zero_of_isIntegral l lam _ hx)
    rw [add_zero] at h
    convert h using 1
    ring
  · have h1 := sz_nat_val l lam (l ^ padicValNat l D)
    rw [padicValNat.prime_pow] at h1
    have h2 : Sz l lam 0 (M : ℂ) := sz_zero_of_isIntegral l lam _ (by simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ))))
    have h := GlobalTheory.SzRules.sz_mul h2 h1
    rw [zero_add, ← Nat.cast_mul] at h
    refine GlobalTheory.SzRules.sz_mono ?_ h
    have : (0 : ℝ) ≤ (padicValNat l D : ℝ) := Nat.cast_nonneg _
    linarith

end GlobalTheory.SizeSqIntegral
end
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D M : ℕ) (x : ℂ), 0 < D → IsIntegral ℤ ((D : ℂ) * x ^ 2) → Sz l lam (-(padicValNat l D : ℝ) / 2) ((D : ℂ) * x) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M * l ^ padicValNat l D : ℕ) : ℂ) := by
  atlas_forward_decl GlobalTheory.SizeSqIntegral.main
end

section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.RoadE

open GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def passScaled (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N : ℕ) : Lat (FR E) where
  carrier := {x | ∃ y' ∈ lattice c y, (N : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩ => ⟨a + b, (latticeSub c y).add_mem ha hb, by
    have : ptE t (x + x') = ptE t x + ptE t x' := by simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring
    rw [this, ← hxa, ← hxb]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨b, hb, hxb⟩ => ⟨algebraMap (OF E) E a * b, mul_mem_lattice (algebraMap_mem_orderC c a) hb, by
    rw [ptE_smul, ← hxb]; ring⟩

end GlobalTheory.RoadE

namespace GlobalTheory.RoadE
open GlobalTheory.CMVal

theorem passl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (y : (Af E)ˣ) (θ : E) (D M₀ : ℕ), IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → OneOver l y → 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → ¬ l ∣ M₀ → ∃ (M M' : ℕ) (L : Lat (FR E)), ¬ l ∣ M ∧ ¬ l ∣ M' ∧ M₀ ∣ M' ∧ HasLevel (M' * l ^ (padicValNat l D + a0 𝔣 l)) L ∧ (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y' ∈ lattice (condQ 𝔣 Q) y, ((M * D : ℕ) : E) * y' = (x 0 : E) * θ + (x 1 : E)) ∧ (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb (FR E)), Sz l lam (-(padicValNat l D : ℝ) / 2) ((i (v j) : ℝ) : ℂ)) ∧ Sz l lam (-(padicValNat l D : ℝ) / 2) ((M' * l ^ (padicValNat l D + a0 𝔣 l) : ℕ) : ℂ) := by
  intro E _ _ _ l _ lam 𝔣 Q y θ D M₀ hf hQ hy hD hθ hθD hM₀
  have hl : l.Prime := Fact.out
  set c := condQ 𝔣 Q with hc
  obtain ⟨M, hMl, hMint⟩ := GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l E l c y hl hy
  obtain ⟨M₁, hM₁l, hM₁c⟩ := GlobalTheory.T.exists_coprime_mul_prime_pow_mem_conductor E l 𝔣 Q hl hf hQ
  have hM₁0 : M₁ ≠ 0 := by rintro rfl; exact hM₁l (dvd_zero l)
  have hM0 : M ≠ 0 := by rintro rfl; exact hMl (dvd_zero l)
  have hR : 0 < M₁ * l ^ a0 𝔣 l := Nat.pos_of_ne_zero (mul_ne_zero hM₁0 (pow_ne_zero _ hl.ne_zero))
  obtain ⟨M₂, hM₂l, hM₂⟩ := GlobalTheory.T.nat_mul_integral_mem_cmLattice_prime_to E l c y (M₁ * l ^ a0 𝔣 l) hl hy hR hM₁c
  obtain ⟨D', hD'⟩ := pow_padicValNat_dvd (p := l) (n := D)
  have hD'l : ¬ l ∣ D' := by
    rintro ⟨e, he⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    refine ⟨e, ?_⟩
    calc D = l ^ padicValNat l D * D' := hD'
      _ = l ^ (padicValNat l D + 1) * e := by rw [he, pow_succ]; ring
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : E) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (n : ℤ)))
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hDF : (D : FR E) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x ∈ passScaled θ c y (M * D), ∀ j,
      IsIntegral ℤ ((D : FR E) * ((D : FR E)⁻¹ * x j) ^ 2) ∧ IsIntegral ℤ (x j) := by
    rintro x ⟨y', hy', hxy⟩ j
    have hpt : (((D : FR E)⁻¹ * x 0 : FR E) : E) * θ + (((D : FR E)⁻¹ * x 1 : FR E) : E) = (M : E) * y' := by
      simp only [ptE] at hxy
      push_cast at hxy ⊢
      have h' : (M : E) * y' = (D : E)⁻¹ * (((x 0 : FR E) : E) * θ + ((x 1 : FR E) : E)) := by
        rw [← hxy]; field_simp
      rw [h']; ring
    have h := GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral E θ D (fun j => (D : FR E)⁻¹ * x j) hD hθ hθD (by rw [hpt]; exact hMint y' hy') j
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    simp only [mul_inv_cancel_left₀ hDF] at h2
    exact h2
  refine ⟨M, M₀ * M * D' * M₂ * M₁, passScaled θ c y (M * D), hMl, ?_, ⟨M * D' * M₂ * M₁, by ring⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    exacts [hM₀ h, hMl h, hD'l h, hM₂l h, hM₁l h]
  · refine ⟨fun w hw => ?_, fun x hx => ?_⟩
    · have hwj : ∀ j, IsIntegral ℤ ((w j : FR E) : E) := by
        intro j
        have hwj1 : w j ∈ (1 : Submodule (𝓞 (FR E)) (FR E)) := Submodule.mem_pi.1 hw j (Set.mem_univ j)
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 hwj1
        rw [← ha]
        exact (RingOfIntegers.isIntegral_coe a).map (RingHom.toIntAlgHom (maximalRealSubfield E).subtype)
      have hP : IsIntegral ℤ ((M₀ : E) * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) :=
        (hnat M₀).mul (((hwj 0).mul hθ).add (hwj 1))
      refine ⟨_, hM₂ _ hP, ?_⟩
      have e : (D : E) = (l : E) ^ padicValNat l D * D' := by exact_mod_cast hD'
      simp only [ptE, Pi.smul_apply, Algebra.smul_def, Subfield.coe_mul, map_natCast]
      push_cast
      linear_combination ((M : E) * M₂ * M₁ * (l : E) ^ a0 𝔣 l * M₀ * (((w 0 : FR E) : E) * θ + ((w 1 : FR E) : E))) * e
    · intro j _
      change x j ∈ (1 : Submodule (𝓞 (FR E)) (FR E))
      rw [Submodule.mem_one]
      exact ⟨⟨x j, (key x hx j).2⟩, rfl⟩
  · intro x; exact Iff.rfl
  · intro w hw j i
    have h1 := (key w hw j).1
    set f : FR E →ₐ[ℤ] ℂ := RingHom.toIntAlgHom (Complex.ofRealHom.comp i) with hf
    have h2 : IsIntegral ℤ ((D : ℂ) * (f ((D : FR E)⁻¹ * w j)) ^ 2) := by
      have := h1.map f
      simpa [map_mul, map_pow, map_natCast] using this
    have h3 := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D 0 (f ((D : FR E)⁻¹ * w j)) hD h2).1
    have h4 : (D : ℂ) * f ((D : FR E)⁻¹ * w j) = ((i (w j) : ℝ) : ℂ) := by
      rw [← map_natCast f D, ← map_mul, mul_inv_cancel_left₀ hDF]
      rfl
    rwa [h4] at h3
  · have h := (GlobalTheory.T.algebraicValuation_bound_of_mul_sq_integral l lam D (M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l) 0 hD (by simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℂ)))).2
    rwa [show M₀ * M * D' * M₂ * M₁ * l ^ (padicValNat l D + a0 𝔣 l) =
      M₀ * M * D' * M₂ * M₁ * l ^ a0 𝔣 l * l ^ padicValNat l D by ring]

end GlobalTheory.RoadE
end

section
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.RootDiscrExp

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem finrank_le_two_mul_padicValInt_discr (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (hp : p.Prime) (hd : (p : ℤ) ∣ discr E) : Module.finrank ℚ E ≤ 2 * padicValInt p (discr E) := by
  classical
  have := Fact.mk hp
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have ha : padicValInt p (discr E) = a := by
    rw [padicValInt, hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hm
    have h1 := Int.natCast_dvd.1 hd
    rwa [hdisc, pow_zero, one_mul] at h1
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨P, hPmax, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hP : P.IsPrime := hPmax.isPrime
  have hpP : (p : 𝓞 E) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPo.over]
      exact Ideal.mem_span_singleton_self _
    rwa [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  have h := diffExp E p a m hp hm hdisc P hP hpP
  have hpos := count_span_pos E p hp hP hpP
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hI0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := span_nat_ne_bot p
  have hdvd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ differentIdeal ℤ (𝓞 E) := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) p ((Submodule.mem_bot _).1 hpP)
  have fD := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 hP) hD0
  have hd' := fD.le_multiplicity_of_pow_dvd hdvd
  have hc : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (normalizedFactors X).count P = multiplicity P X := fun X hX =>
    (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 E)).count_normalizedFactors_eq_multiplicity hX
  rw [hc _ hD0, hc _ hI0] at h
  rw [hc _ hI0] at hpos
  rw [ha]
  generalize multiplicity P (differentIdeal ℤ (𝓞 E)) = k at h hd'
  generalize multiplicity P (Ideal.span {(p : 𝓞 E)}) = e at h hd' hpos
  generalize Module.finrank ℚ E = n at h ⊢
  have hk : k ≠ 0 := by
    rintro rfl
    have : a * e ≠ 0 := mul_ne_zero ha0 hpos.ne'
    apply this
    nlinarith
  have hek : e ≤ 2 * k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  nlinarith [Nat.mul_le_mul_left n hek]

theorem half_le_delta_two_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type)
    [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ →
    (1 / 2 : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E 2 := by
  intro E _ _ _ _ I _ d φ h
  have h1 := finrank_le_two_mul_padicValInt_discr E 2 Nat.prime_two (by exact_mod_cast h.2.2.2.2.1)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h2 : (Module.finrank ℚ E : ℝ) ≤ 2 * (padicValInt 2 (discr E) : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp, le_div_iff₀ hn]
  linarith

end GlobalTheory.RootDiscrExp
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.DiscrTower

theorem finrank_mul_padicValInt_discr_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (l : ℕ) (hl : l.Prime) :
    Module.finrank K L * padicValInt l (discr K) ≤ padicValInt l (discr L) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero L)
  rw [h] at hL
  unfold padicValInt
  rw [h, padicValNat.mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL), padicValNat.pow]
  omega

theorem padicValInt_discr_div_le_delta_vp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime →
      (padicValInt l (discr (maximalRealSubfield E)) : ℝ) / Module.finrank ℚ (maximalRealSubfield E) ≤
        GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E l := by
  intro E _ _ _ l hl
  have h := finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl
  have h2 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E) := by exact_mod_cast Module.finrank_pos
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
  rw [div_le_div_iff₀ hF hE, ← h2]
  have h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤
      padicValInt l (discr E) := by exact_mod_cast h
  push_cast
  nlinarith

end GlobalTheory.DiscrTower
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.QuadGenerator

theorem int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h')

theorem isIntegral_int (n : ℤ) : IsIntegral ℤ (n : ℂ) := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)

theorem sq_root (d : ℕ) : (Complex.I * (Real.sqrt d : ℝ)) ^ 2 = -(d : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

theorem half_coords {d : ℕ} (hd : d.Prime) {a b : ℚ}
    (hx : IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ)))) :
    ∃ t k n : ℤ, (t : ℚ) = 2 * a ∧ (k : ℚ) = 2 * b ∧ t ^ 2 + d * k ^ 2 = 4 * n := by
  have hw2 := sq_root d
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
    have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
    simpa [hwc, sub_eq_add_neg] using this
  obtain ⟨t, ht⟩ := int_of_isIntegral (r := 2 * a) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
    push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
    refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
    push_cast
    linear_combination (b : ℂ) ^ 2 * hw2)
  have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [hn, ht]; ring
  obtain ⟨m, hm⟩ := int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
    rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
    exact isIntegral_int _))
  have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
    have : ((m ^ 2 : ℤ) : ℚ) = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      rw [← hm2, ← hm]; push_cast; ring
    exact_mod_cast this
  obtain ⟨k, hk⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, hm3⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have hkb : (k : ℚ) = 2 * b := by
    apply mul_left_cancel₀ hd0
    rw [← hm, hk]; push_cast; ring
  refine ⟨t, k, n, ht, hkb, ?_⟩
  have : ((t ^ 2 + d * k ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
    push_cast
    rw [ht, hkb, hn]; ring
  exact_mod_cast this

theorem even_of_one {d : ℕ} (h4 : d % 4 = 1) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t ∧ 2 ∣ k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 1 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - q ^ 2) = 1 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q + 1) ^ 2 - q ^ 2 - q) = 2 := by linear_combination -h
    omega

theorem even_of_three {d : ℕ} (h4 : d % 4 = 3) {t k n : ℤ} (h : t ^ 2 + d * k ^ 2 = 4 * n) : 2 ∣ t + k := by
  obtain ⟨c, rfl⟩ : ∃ c, d = 4 * c + 3 := ⟨d / 4, by omega⟩
  push_cast at h
  rcases Int.even_or_odd' t with ⟨p, rfl | rfl⟩ <;> rcases Int.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact ⟨p + q, by ring⟩
  · have : 4 * (n - p ^ 2 - c * (2 * q + 1) ^ 2 - 3 * q ^ 2 - 3 * q) = 3 := by linear_combination -h
    omega
  · have : 4 * (n - p ^ 2 - p - c * (2 * q) ^ 2 - 3 * q ^ 2) = 1 := by linear_combination -h
    omega
  · exact ⟨p + q + 1, by ring⟩

theorem integers_one {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 1) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * (Complex.I * (Real.sqrt d : ℝ)) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := even_of_one h4 h
    have ha : a = p := by push_cast at ht; linarith
    have hb : b = q := by push_cast at hk; linarith
    exact ⟨q, p, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw : IsIntegral ℤ (Complex.I * (Real.sqrt d : ℝ)) := by
      refine IsIntegral.of_pow two_pos ?_
      rw [sq_root]
      simpa using isIntegral_int (-(d : ℤ))
    refine ⟨?_, v, u, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

theorem integers_three {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (x : ℂ) :
    (IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))) ↔
      ∃ u v : ℤ, x = 1 * (u * ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) + v) := by
  constructor
  · rintro ⟨hx, a, b, rfl⟩
    obtain ⟨t, k, n, ht, hk, h⟩ := half_coords hd hx
    obtain ⟨j, hj⟩ := even_of_three h4 h
    have hj' : (t : ℚ) + k = 2 * j := by exact_mod_cast hj
    have ha : a = j - k / 2 := by linarith
    have hb : b = k / 2 := by linarith
    exact ⟨k, j, by rw [ha, hb]; push_cast; ring⟩
  · rintro ⟨u, v, rfl⟩
    have hw2 := sq_root d
    obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
    have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
    have hw : IsIntegral ℤ ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2) := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        algebraMap_int_eq, eq_intCast, Int.cast_natCast]
      linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
    refine ⟨?_, v - u / 2, u / 2, by push_cast; ring⟩
    rw [one_mul]
    exact ((isIntegral_int u).mul hw).add (isIntegral_int v)

theorem exists_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ) (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ (w θ : E) (τ : ℍ), w ^ 2 = -(d : E) ∧ (∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)) ∧ θ = (if d % 4 = 3 then (-1 + w) / 2 else w) ∧ (∀ i, φ i θ = (τ : ℂ)) ∧ IsTauOf Λ 1 τ ∧ ((d % 4 = 3 ∧ τ.im = Real.sqrt d / 2) ∨ (d % 4 = 1 ∧ τ.im = Real.sqrt d)) := by
  intro E _ _ _ I _ d φ Λ hF hΛ
  obtain ⟨hd, h4, -, -, -, -, -, w, hw, hφ⟩ := hF
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
  have hodd : d % 2 = 1 := hd.eq_two_or_odd.resolve_left (by omega)
  by_cases h3 : d % 4 = 3
  · have him : ((-1 + Complex.I * (Real.sqrt d : ℝ)) / 2 : ℂ).im = Real.sqrt d / 2 := by simp
    refine ⟨w, (-1 + w) / 2, ⟨(-1 + Complex.I * (Real.sqrt d : ℝ)) / 2, by rw [him]; positivity⟩, hw, hφ,
      by rw [if_pos h3], fun i => ?_, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_three hd h3 x)⟩, Or.inl ⟨h3, him⟩⟩
    rw [map_div₀, map_add, map_neg, map_one, map_ofNat, hφ]
  · have h1 : d % 4 = 1 := by omega
    have him : (Complex.I * (Real.sqrt d : ℝ) : ℂ).im = Real.sqrt d := by simp
    exact ⟨w, w, ⟨Complex.I * (Real.sqrt d : ℝ), by rw [him]; exact hs⟩, hw, hφ,
      by rw [if_neg h3], hφ, ⟨one_ne_zero, fun x => (hΛ x).trans (integers_one hd h1 x)⟩, Or.inr ⟨h1, him⟩⟩

end GlobalTheory.QuadGenerator
end

section
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatValRam GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsFieldData IsIntLattice c_vp cE_vp a0 delta_vp)
open ReciprocityTheory.ChartRestriction.L1 (IsTauOf DD jT)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb)
open scoped UpperHalfPlane Classical

namespace GlobalTheory.JetIntElliptic

theorem sz_l (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    Sz l lam (-1) (l : ℂ) ∧ Sz l lam 1 (l : ℂ)⁻¹ := by
  have h : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [h1, norm_algebraMap', Padic.norm_p]
  refine ⟨⟨natCast_mem _ l, ?_⟩, ⟨inv_mem (natCast_mem _ l), ?_⟩⟩
  · have : (⟨(l : ℂ), natCast_mem _ l⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ) := rfl
    rw [this, map_natCast, h, Real.rpow_neg_one]
  · have : (⟨(l : ℂ)⁻¹, inv_mem (natCast_mem _ l)⟩ : algebraicClosure ℚ ℂ) = (l : algebraicClosure ℚ ℂ)⁻¹ := rfl
    rw [this, map_inv₀, map_natCast, norm_inv, h, inv_inv, Real.rpow_one]

theorem sz_val (l : ℕ) [hl : Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (D : ℕ) :
    Sz l lam (-(padicValNat l D : ℝ)) (D : ℂ) := by
  obtain ⟨m, hm⟩ : l ^ padicValNat l D ∣ D := pow_padicValNat_dvd
  have h := sz_mul (sz_pow (sz_l l lam).1 (padicValNat l D)) (sz_nat (l := l) (lam := lam) m)
  have h2 : (D : ℂ) = (l : ℂ) ^ padicValNat l D * m := by exact_mod_cast hm
  rw [← h2] at h
  convert h using 1
  ring

theorem c_facts {E : Type} [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (l : ℕ) (hl : l.Prime) :
    delta_vp E l ≤ c_vp 𝔣 l ∧ 0 ≤ c_vp 𝔣 l ∧ ∃ q : ℚ, (q : ℝ) = c_vp 𝔣 l := by
  have h0 : 0 ≤ delta_vp E l := by unfold delta_vp; positivity
  unfold c_vp
  split_ifs with h
  · refine ⟨?_, by positivity, ⟨a0 𝔣 l, by simp⟩⟩
    obtain ⟨v, hv, hvd⟩ := h
    obtain ⟨-, -, l', hl', -, hm, hnd, -⟩ := h𝔣.2.2 v hvd
    have hll : l' = l := by
      by_contra hne
      have hc : IsCoprime (l' : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hl' hl).2 hne)
      obtain ⟨a, b, hab⟩ := hc
      have h1 : (1 : OF E) = (a : OF E) * (l' : OF E) + (b : OF E) * (l : OF E) := by exact_mod_cast hab.symm
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (h1 ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hv)))
    subst hll
    have : delta_vp E l' = 0 := by
      unfold delta_vp
      rw [padicValInt.eq_zero_of_not_dvd hnd]; simp
    rw [this]; positivity
  · exact ⟨le_rfl, h0, ⟨(padicValInt l (discr E) : ℚ) / (Module.finrank ℚ E : ℚ), by unfold delta_vp; push_cast; rfl⟩⟩

theorem theta_facts {E : Type} [Field E] [NumberField E] [IsCMField E] (ψ : E →+* ℂ) (d : ℕ) (w θ : E) (hw : w ^ 2 = -(d : E))
    (hψ : ψ w = Complex.I * (Real.sqrt d : ℝ)) (hθ : θ = (if d % 4 = 3 then (-1 + w) / 2 else w)) :
    IsIntegral ℤ θ ∧ (θ - IsCMField.complexConj E θ) ^ 2 = -(((if d % 4 = 3 then d else 4 * d : ℕ) : ℕ) : E) := by
  have hc : IsCMField.complexConj E w = -w := by
    apply ψ.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hψ]
    simp
  split_ifs at hθ ⊢ with h
  · subst hθ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
    have hm' : (d : E) + 1 = 4 * m := by exact_mod_cast hm
    refine ⟨⟨Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]
      linear_combination (1 / 4 : E) * hw - (1 / 4 : E) * hm'
    · rw [map_div₀, map_add, map_neg, map_one, hc, map_ofNat]
      linear_combination hw
  · subst hθ
    refine ⟨⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩, ?_⟩
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      simp only [eq_intCast, Int.cast_natCast, algebraMap_int_eq]
      linear_combination hw
    · rw [hc]; push_cast
      linear_combination 4 * hw

theorem tors_ex (N M₀ : ℕ) (hN : 0 < N) (h1 : 1 < M₀) (hd : M₀ ∣ N) : ∃ y : Fin 2 → ZMod N, M₀ • y = 0 ∧ y ≠ 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hN
  refine ⟨fun _ => (k : ZMod (M₀ * k)), funext fun i => ?_, fun h => ?_⟩
  · simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · have h0 : ((k : ℕ) : ZMod (M₀ * k)) = 0 := congrFun h 0
    have := Nat.le_of_dvd hk ((ZMod.natCast_eq_zero_iff _ _).1 h0)
    nlinarith

theorem val_facts (l d : ℕ) (hl : l.Prime) (hd : d.Prime) (h4 : 4 < d) :
    (padicValNat l (if d % 4 = 3 then d else 4 * d) : ℝ) / 2 =
      (if l = d then 1 / 2 else 0) + (if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0) := by
  haveI := Fact.mk hl
  haveI := Fact.mk hd
  have h1 : padicValNat l d = if l = d then 1 else 0 := by
    split_ifs with h
    · subst h; exact padicValNat_self
    · exact padicValNat_primes h
  have h2 : padicValNat l 4 = if l = 2 then 2 else 0 := by
    split_ifs with h
    · subst h; exact padicValNat.prime_pow 2
    · refine padicValNat.eq_zero_of_not_dvd fun hh => h ?_
      exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow (n := 2) hh)
  by_cases h3 : d % 4 = 3
  · simp only [h3, if_true, h1, not_true, and_false, if_false]
    split_ifs <;> norm_num
  · simp only [h3, if_false, not_false_iff, and_true]
    rw [padicValNat.mul (by norm_num) hd.ne_zero, h1, h2]
    split_ifs <;> norm_num

theorem fin_id (jt Ω p n lp γ pi im r : ℂ) (t f K : ℕ) (hΩ : Ω ≠ 0) (hp : p ≠ 0) (hlp : lp ≠ 0) (hpi : pi ≠ 0) (him : im ≠ 0)
    (hr : r ≠ 0) :
    n ^ (t * f) * jt * ((2 * pi / r * γ / (Ω / lp) / (Ω / lp)) ^ K / ((Ω / lp) ^ t) ^ f) =
      jt * (pi / im) ^ K / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) * (n * lp) ^ (t * f) *
        (2 * im / r * γ * lp ^ 2) ^ K := by
  have h1 : 2 * pi / r * γ / (Ω / lp) / (Ω / lp) = (pi / im) * (2 * im / r * γ * lp ^ 2) / Ω ^ 2 := by field_simp
  have h2 : ∀ x : ℂ, x / p ^ (t * f + 2 * K) / (Ω * 1 / p) ^ (t * f + 2 * K) = x / Ω ^ (t * f + 2 * K) := fun x => by
    rw [div_div, ← mul_pow]; congr 2; field_simp
  rw [h1, h2, ← pow_mul, div_pow, div_pow Ω, mul_pow (pi / im), mul_pow n, pow_add, pow_mul Ω 2]
  field_simp

theorem core (hjsz : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ)) : EisExp → JetInt := by
  intro hEis E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ
  obtain ⟨w, θ, τ, hw, hφw, hθ, hφθ, htau, him⟩ := GlobalTheory.QuadGenerator.exists_generator E I d φ Λ hF hΛ
  have hδ2 := GlobalTheory.RootDiscrExp.half_le_delta_two_vp E I d φ hF
  obtain ⟨hd, h4, hUn, -, -, hI2, hCM, -⟩ := hF
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (FR E) := hcard ▸ hI2
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨hint, hsq⟩ := theta_facts (φ i₀) d w θ hw (hφw i₀) hθ
  have hvD := val_facts l d hl hd h4
  set D : ℕ := if d % 4 = 3 then d else 4 * d with hDdef
  have hD0 : 0 < D := by rw [hDdef]; split_ifs <;> omega
  obtain ⟨M₀, hM₀1, hM₀⟩ : ∃ M₀ : ℕ, 1 < M₀ ∧ ¬ l ∣ M₀ :=
    ⟨l + 1, by have := hl.pos; omega, fun h => hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right dvd_rfl).1 h))⟩
  obtain ⟨M, M', L, hM, hM', hMM, hL, hLm, hLs, hNs⟩ :=
    GlobalTheory.RoadE.passl E l lam 𝔣 Q y θ D M₀ h𝔣 hQl hy hD0 hint hsq hM₀
  have hMpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hM'pos : 0 < M' := Nat.pos_of_ne_zero fun h => hM' (h ▸ dvd_zero l)
  have hNpos : 0 < M' * l ^ (padicValNat l D + a0 𝔣 l) := Nat.mul_pos hM'pos (pow_pos hl.pos _)
  haveI : NeZero (M' * l ^ (padicValNat l D + a0 𝔣 l)) := ⟨hNpos.ne'⟩
  obtain ⟨t, ht, ht0⟩ := tors_ex _ M₀ hNpos hM₀1 (hMM.mul_right _)
  obtain ⟨hδc, hc0, q, hq⟩ := c_facts 𝔣 h𝔣 l hl
  have hdF := (GlobalTheory.DiscrTower.padicValInt_discr_div_le_delta_vp E l hl).trans hδc
  obtain ⟨γ, hγ0, hγ, hγ'⟩ := GlobalTheory.QFam.exists_sz_scale l lam (q + if l = d then 1 / 2 else 0)
  have hqh : ((q + if l = d then 1 / 2 else 0 : ℚ) : ℝ) = c_vp 𝔣 l + if l = d then 1 / 2 else 0 := by
    rw [← hq]; split_ifs <;> push_cast <;> ring
  rw [hqh] at hγ hγ'
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have him0 : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hlp : (l : ℂ) ^ a0 𝔣 l ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  refine ⟨fun _ => Ω / (l : ℂ) ^ a0 𝔣 l, fun _ => 2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l), fun i => ?_,
    fun g κ u hg hu => ?_⟩
  · refine ⟨div_ne_zero hΩ0 hlp, div_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero hpi) hsd) hγ0)
      (div_ne_zero hΩ0 hlp), ?_, ?_⟩
    · have h1 : Ω / (l : ℂ) ^ a0 𝔣 l / Ω = ((l : ℂ)⁻¹) ^ a0 𝔣 l := by rw [inv_pow]; field_simp
      rw [h1]
      simpa using sz_pow (sz_l l lam).2 (a0 𝔣 l)
    · have h1 : Ω / (l : ℂ) ^ a0 𝔣 l * (2 * Real.pi / (Real.sqrt d : ℝ) * γ / (Ω / (l : ℂ) ^ a0 𝔣 l)) * (Real.sqrt d : ℝ) /
          (2 * Real.pi) = γ := by field_simp
      beta_reduce
      rw [h1]
      exact hγ'
  · obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_cmType_realEmbeddings E I φ hCM
    have hD := GlobalTheory.HilbFam.iterD_defSum_eq_jet hEis E I φ e θ τ _ L (M * D) s _ g κ u hf2 hs hNpos hL he hφθ
      (Nat.mul_pos hMpos hD0) hLm hg hu
    obtain ⟨hω, hj, hst⟩ := GlobalTheory.SzTau.main l lam d Λ 1 Ω τ hd h4 hΛ htau hΩ
    haveI : IsGalois ℚ (FR E) := (IsAbelianGalois.tower_bot ℚ (FR E) E).toIsGalois
    have hfpos : (0 : ℝ) < Module.finrank ℚ (FR E) := by exact_mod_cast (by omega : 0 < Module.finrank ℚ (FR E))
    have ha0 : (0 : ℝ) ≤ a0 𝔣 l := Nat.cast_nonneg _
    have hv0 : (0 : ℝ) ≤ padicValNat l D := Nat.cast_nonneg _
    have hJ := hjsz hEis (FR E) hf2 s _ L hs hL z hz l lam (fun j => κ (e.symm j)) t M' M₀ (padicValNat l D + a0 𝔣 l)
      (cE_vp l z) (-(padicValNat l D : ℝ) / 2) (2 * c_vp 𝔣 l + 2 * a0 𝔣 l + (padicValNat l D : ℝ) / 2) (Nat.cast_nonneg _)
      (fun C => by
        have h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z :=
          Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat)
            (Finset.mem_univ C)
        have h2 := (Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))).trans
          (Int.ofNat_le.2 h1)
        exact_mod_cast h2)
      hM' hL.1 hLs hNs (by push_cast; linarith) (by positivity) hM₀ ht ht0 τ _ hj hω
      (div_ne_zero (by simpa using hΩ0) hp)
      (sz_mono (hst _ M₀ t hM₀ ht ht0) (by
        rw [hvD]
        by_cases h2 : l = 2
        · have hc2 : (1 / 2 : ℝ) ≤ c_vp 𝔣 l := by subst h2; exact hδ2.trans hδc
          have hld : ¬ l = d := by omega
          simp only [h2, if_true, true_and] at hld ⊢
          rw [← h2]
          split_ifs <;> linarith
        · simp only [h2, if_false, false_and]
          split_ifs <;> linarith))
    have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
    have hr : Sz l lam (-(if l = 2 ∧ ¬ d % 4 = 3 then 1 else 0)) (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) := by
      rcases him with ⟨h3, h⟩ | ⟨h3, h⟩
      · have : (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = 1 := by rw [h]; push_cast; field_simp
        rw [this]; simpa [h3] using sz_one (l := l) (lam := lam)
      · have : (2 * (τ.im : ℝ) / (Real.sqrt d : ℝ) : ℂ) = ((2 : ℕ) : ℂ) := by rw [h]; push_cast; field_simp
        rw [this]
        split_ifs with h5
        · obtain ⟨rfl, -⟩ := h5; exact (sz_l 2 lam).1
        · simpa using sz_nat (l := l) (lam := lam) 2
    have hn : Sz l lam (0 + -(padicValNat l D : ℝ)) ((M * D : ℕ) : ℂ) := by
      rw [Nat.cast_mul]; exact sz_mul (sz_nat M) (sz_val l lam D)
    have hlps := sz_pow (sz_l l lam).1 (a0 𝔣 l)
    have hall := sz_mul (sz_mul hJ (sz_pow (sz_mul hn hlps) (2 * s * Module.finrank ℚ (FR E))))
      (sz_pow (sz_mul (sz_mul hr hγ) (sz_pow hlps 2)) (∑ i, κ i))
    beta_reduce
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, hcard]
    have hD' : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 = _ := hD
    rw [hD', fin_id _ Ω (2 * Real.pi * Complex.I) _ _ γ _ (τ.im : ℝ) _ (2 * s) _ _ hΩ0 hp hlp hpi him0 hsd]
    rw [wt, hsum, Complex.ofReal_div] at hall
    refine sz_mono hall ?_
    have hdF' : (padicValInt l (discr (FR E)) : ℝ) ≤ c_vp 𝔣 l * Module.finrank ℚ (FR E) := (div_le_iff₀ hfpos).1 hdF
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have h6 := mul_le_mul_of_nonneg_left hdF' hs0
    have h7 : 0 ≤ (s : ℝ) * (c_vp 𝔣 l * Module.finrank ℚ (FR E)) := by positivity
    have h8 : (if l = 2 ∧ ¬ d % 4 = 3 then (1 : ℝ) else 0) = (padicValNat l D : ℝ) / 2 - (if l = d then 1 / 2 else 0) := by
      rw [hvD]; ring
    rw [h8]
    push_cast
    nlinarith

theorem jetInt : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := fun _ hPZ _ _ =>
  core GlobalTheory.HilbFam.sz_jet_conj (GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ) hPZ)

end GlobalTheory.JetIntElliptic
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := by
  atlas_forward_decl GlobalTheory.JetIntElliptic.jetInt
end
