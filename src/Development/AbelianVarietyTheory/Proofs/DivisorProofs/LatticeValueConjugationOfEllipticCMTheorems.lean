import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordInEqOfJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportModularFamilyGL2ZModWeierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGEis
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeQuotientCorrespondenceOfTorsionTranspor
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitZetaAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulMatSmulOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOneIffIsIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau

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
theorem _root_.GlobalTheory.T.hilbertEisenstein_value_derivatives_via_jets : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I) (Ch : ℍ → ℂ), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * ∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) * hfun (2 * s) L μ Ch τ := by
  first | exact @GlobalTheory.HilbFam.eValue_derivs | exact GlobalTheory.HilbFam.eValue_derivs | (intros; apply GlobalTheory.HilbFam.eValue_derivs <;> assumption)
end

section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem E₄_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₄ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 4 = 12 * (Λ.g₂ / Ω ^ 4) := by
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 4 = 16 * (Real.pi : ℂ) ^ 4 := by
    rw [mul_pow, Complex.I_pow_four]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₂_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem E₆_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₆ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 6 = -(216 * (Λ.g₃ / Ω ^ 6)) := by
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 6 = -(64 * (Real.pi : ℂ) ^ 6) := by
    rw [mul_pow, h6]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₃_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem map_E₄_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4) :
    g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4)
      = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 := by
  rw [E₄_div_period_eq h₀, E₄_div_period_eq h₁, map_mul, h, map_ofNat]

theorem map_E₆_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) :
    g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6)
      = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 := by
  rw [E₆_div_period_eq h₀, E₆_div_period_eq h₁, map_neg, map_mul, h, map_ofNat]

theorem map_eisenstein_div_period :
    ∀ (g : ℂ ≃+* ℂ) (Λ₀ Λ₁ : PeriodPair) (c₀ c₁ Ω₀ Ω₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 → g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 → g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4) = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 ∧ g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6) = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 :=
  fun g _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃ =>
    ⟨map_E₄_div_period g h₀ h₁ h₂, map_E₆_div_period g h₀ h₁ h₃⟩

end GlobalTheory.QFam
end

section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem kerReps_transport : ∀ (K : Type) [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (a : K) (S : Finset ℂ), IsTr ι Λ₀ Λ₁ T → a ≠ 0 → (∀ x x', T x x' → T (a * x) (a * x')) → IsKerReps Λ₀ (ι a) S → ∃ (φ : ℂ → ℂ) (S' : Finset ℂ), IsKerReps Λ₁ (ι a) S' ∧ Set.BijOn φ S S' ∧ ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ ι k' = φ P ∧ T k k' := by
  intro K _ ι Λ₀ Λ₁ T a S hT ha hmul hS
  classical
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  obtain ⟨hS1, hS2, hS3⟩ := hS

  have hex : ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ T k k' := by
    intro P hP
    obtain ⟨b, hb⟩ := hT.rat₀ _ (hS1 P hP).1
    obtain ⟨k', hk'⟩ := hT.left (b / a)
    refine ⟨b / a, k', ?_, hk'⟩
    rw [map_div₀, hb]; field_simp
  choose! k k' hk hT' using hex
  set φ : ℂ → ℂ := fun P => ι (k' P) with hφ

  have himg : ∀ P ∈ S, ι a * φ P ∈ Λ₁.lattice ∧ φ P ∉ Λ₁.lattice := by
    intro P hP
    have h1 := hT.mem_iff _ _ (hmul _ _ (hT' P hP))
    have h2 := hT.mem_iff _ _ (hT' P hP)
    rw [map_mul, map_mul, hk P hP] at h1
    rw [hk P hP] at h2
    exact ⟨h1.mp (hS1 P hP).1, fun h => (hS1 P hP).2 (h2.mpr h)⟩
  have hdiff : ∀ P ∈ S, ∀ Q ∈ S, φ P - φ Q ∈ Λ₁.lattice → P = Q := by
    intro P hP Q hQ h
    have h1 := hT.mem_iff _ _ (hT.sub _ _ _ _ (hT' P hP) (hT' Q hQ))
    rw [map_sub, map_sub, hk P hP, hk Q hQ] at h1
    exact hS2 P hP Q hQ (h1.mpr h)
  refine ⟨φ, S.image φ, ⟨?_, ?_, ?_⟩, ⟨fun P hP => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hP),
    fun P hP Q hQ h => hdiff P hP Q hQ (by rw [h, sub_self]; exact zero_mem _), ?_⟩, ?_⟩
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    exact himg P hP
  · intro P' hP' Q' hQ' h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hQ'
    rw [hdiff P hP Q hQ h]
  · intro z hz hz'
    obtain ⟨c, hc⟩ := hT.rat₁ _ hz
    have hzc : ι (c / a) = z := by rw [map_div₀, hc]; field_simp
    obtain ⟨m, hm⟩ := hT.right (c / a)
    have h1 := hT.mem_iff _ _ (hmul _ _ hm)
    have h2 := hT.mem_iff _ _ hm
    rw [map_mul, map_mul, hzc] at h1
    rw [hzc] at h2
    obtain ⟨P, hP, hmP⟩ := hS3 (ι m) (h1.mpr hz) (fun h => hz' (h2.mp h))
    refine ⟨φ P, Finset.mem_image_of_mem φ hP, ?_⟩
    have h3 := hT.mem_iff _ _ (hT.sub _ _ _ _ hm (hT' P hP))
    rw [map_sub, map_sub, hk P hP, hzc] at h3
    exact h3.mp hmP
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hP')
    exact ⟨P, hP, rfl⟩
  · intro P hP
    exact ⟨k P, k' P, hk P hP, rfl, hT' P hP⟩

end GlobalTheory.WpFam
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.NormSqOfSquareEqNeg

theorem normSq_of_sq_eq_neg (d : ℕ) (α : ℂ) (h : α ^ 2 = -(d : ℂ)) : (Complex.normSq α : ℂ) = d := by
  have h1 : Complex.normSq α ^ 2 = (d : ℝ) ^ 2 := by
    rw [← map_pow, h, Complex.normSq_neg, Complex.normSq_natCast]
    ring
  have h2 : Complex.normSq α = d := by
    have := Complex.normSq_nonneg α
    nlinarith [sq_nonneg (Complex.normSq α - d), sq_nonneg (Complex.normSq α + d), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  rw [h2]; simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ)
    (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  obtain ⟨_, _, _, hL₀, ⟨𝔞, _, hL₁⟩, _, _, hP⟩ := id hT
  obtain ⟨_, hm₀, him, hint⟩ := GlobalTheory.LatOfMult.main K d δ ι 1 Λ₀ hd hδ hL₀
  obtain ⟨_, hm₁, _, _⟩ := GlobalTheory.LatOfMult.main K d δ ι 𝔞 Λ₁ hd hδ hL₁
  have hα : ι δ ≠ 0 := fun h => him (by simp [h])
  have hδ0 : δ ≠ 0 := fun h => hα (by simp [h])
  have hα2 : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hN : (Complex.normSq (ι δ) : ℂ) = d := normSq_of_sq_eq_neg d _ hα2
  have hc : ι δ ^ 2 - (Complex.normSq (ι δ) : ℂ) = -(2 * d : ℂ) := by rw [hα2, hN]; ring
  have hc0 : -(2 * d : ℂ) ≠ 0 := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simpa using this
  obtain ⟨S, hS⟩ := kernel_reps_exist Λ₀ (ι δ) hα hm₀
  have hTr := GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  have hmul : ∀ x x', Tr t x x' → Tr t (δ * x) (δ * x') := fun x x' h => (GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t).2.1 δ x x' hint h
  obtain ⟨φ, S', hS', hbij, hrel⟩ := GlobalTheory.WpFam.kerReps_transport K ι Λ₀ Λ₁ (Tr t) δ S hTr hδ0 hmul hS
  have e₀ := quasiPeriodConstIsogeny_thm Λ₀ (ι δ) S hα hm₀ hS
  have e₁ := quasiPeriodConstIsogeny_thm Λ₁ (ι δ) S' hα hm₁ hS'
  rw [hc] at e₀ e₁
  have s₀ : s2 Λ₀ = (∑ P ∈ S, Λ₀.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₀]
  have s₁ : s2 Λ₁ = (∑ P ∈ S', Λ₁.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₁]
  have key : ∀ P ∈ S, g (Λ₀.weierstrassP P / Ω₀ ^ 2) = Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 := by
    intro P hPS
    obtain ⟨k, k', hk, hk', hkk⟩ := hrel P hPS
    have hnot : ι k ∉ Λ₀.lattice := by rw [hk]; exact (hS.1 P hPS).2
    have := (hP k k' hnot hkk).1
    rwa [hk, hk'] at this
  have hsum : ∑ P ∈ S, Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 = ∑ Q ∈ S', Λ₁.weierstrassP Q / Ω₁ ^ 2 :=
    Finset.sum_nbij φ (fun a ha => hbij.mapsTo ha) hbij.injOn hbij.surjOn (fun _ _ => rfl)
  have hg2 : g (-(2 * d : ℂ)) = -(2 * d : ℂ) := by simp [map_neg, map_mul, map_ofNat, map_natCast]
  rw [s₀, s₁, div_right_comm, div_right_comm (∑ P ∈ S', _), map_div₀, hg2, Finset.sum_div, Finset.sum_div, map_sum,
    Finset.sum_congr rfl key, hsum]

end GlobalTheory.NormSqOfSquareEqNeg
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transport_second_eisenstein_cm : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  atlas_forward_decl GlobalTheory.NormSqOfSquareEqNeg.main
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelLin

theorem main : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop),
    (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) →
    (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  intro N _ R h1 h2 h3
  choose f hf using h1
  have huniq : ∀ x y y', R x y → R x y' → y = y' := by
    intro x y y' hy hy'
    have h := h3 _ _ (h2 x y x y' hy hy')
    exact sub_eq_zero.mp (h.mp (sub_self x))
  have hsub : ∀ x x', f (x - x') = f x - f x' :=
    fun x x' => huniq _ _ _ (hf (x - x')) (h2 _ _ _ _ (hf x) (hf x'))
  let g : (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N) := AddMonoidHom.ofMapSub f hsub
  let L : (Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → ZMod N) := g.toZModLinearMap N
  have hL : ∀ x, L x = f x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x x' hxx
    have : f (x - x') = 0 := by rw [hsub, hxx, sub_self]
    exact sub_eq_zero.mp ((h3 _ _ (hf (x - x'))).mpr this)
  let M : Matrix (Fin 2) (Fin 2) (ZMod N) := LinearMap.toMatrixRight' L
  have hM : ∀ x, x ᵥ* M = f x := by
    intro x
    rw [← hL, ← Matrix.toLinearMapRight'_apply]
    simp [M]
  have hU : IsUnit M := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, hM x⟩
  refine ⟨hU.unit, fun x => ?_⟩
  have : vmul x hU.unit = f x := by
    simp [vmul, hM]
  rw [this]
  exact hf x

end GlobalTheory.RelLin
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_bijective_relation_rowVec_eq_matrix : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) → (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  atlas_forward_decl GlobalTheory.RelLin.main
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelTors

theorem mul_mem_iff {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (z : ℂ) :
    c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice := by
  rw [h.2, PeriodPair.mem_lattice]
  simp only [tauPair, mul_one]
  constructor
  · rintro ⟨u, v, e⟩
    exact ⟨u, v, (mul_left_cancel₀ h.1 e).symm⟩
  · rintro ⟨u, v, e⟩
    exact ⟨u, v, by rw [← e]⟩

theorem main : ∀ (K : Type) [Field K] [CharZero K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTr ι Λ₀ Λ₁ T → IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x y, R x y ↔ ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ T k k') → (∀ x, ∃ y, R x y) ∧ (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) ∧ (∀ x y, R x y → (x = 0 ↔ y = 0)) := by
  intro K _ _ ι Λ₀ Λ₁ T c₀ c₁ τ₀ τ₁ hT h0 h1 N _ R hR
  obtain ⟨-, a2, a3, a4, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ₀
  obtain ⟨-, b2, b3, b4, b5⟩ := GlobalTheory.WpFam.TorsMem.main N τ₁
  have H0 := mul_mem_iff h0
  have H1 := mul_mem_iff h1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have T00 : T 0 0 := hT.triv 0 0 (by simp) (by simp)
  have Tneg : ∀ a b, T a b → T (-a) (-b) := fun a b h => by
    simpa using hT.sub 0 0 a b T00 h
  have Tadd : ∀ a b c d, T a b → T c d → T (a + c) (b + d) := fun a b c d h h' => by
    simpa using hT.sub _ _ _ _ h (Tneg _ _ h')
  have Tnat : ∀ (n : ℕ) a b, T a b → T (n * a) (n * b) := by
    intro n a b h
    induction n with
    | zero => simpa using T00
    | succ n ih => simpa [add_mul] using Tadd _ _ _ _ ih h
  have adj : ∀ k k' m m', T k k' → ι k - ι m ∈ Λ₀.lattice → ι k' - ι m' ∈ Λ₁.lattice → T m m' := by
    intro k k' m m' h hm hm'
    have := hT.sub _ _ _ _ h (hT.triv (k - m) (k' - m') (by rwa [map_sub]) (by rwa [map_sub]))
    simpa using this
  have real0 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₀.lattice → ∃ m, ι m = w := by
    intro w k h
    obtain ⟨l, hl⟩ := hT.rat₀ _ h
    exact ⟨k + l, by rw [map_add, hl]; ring⟩
  have real1 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₁.lattice → ∃ m, ι m = w := by
    intro w k h
    obtain ⟨l, hl⟩ := hT.rat₁ _ h
    exact ⟨k + l, by rw [map_add, hl]; ring⟩
  refine ⟨fun x => ?_, fun x y x' y' hxy hxy' => ?_, fun x y hxy => ?_⟩
  ·
    obtain ⟨l, hl⟩ := hT.rat₀ ((N : ℂ) * (c₀ * tors N τ₀ x))
      (by rw [show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]; exact a4 x)
    set k : K := l / N with hkdef
    have hk : ι k = c₀ * tors N τ₀ x := by
      rw [hkdef, map_div₀, hl, map_natCast]; field_simp
    obtain ⟨k'', hk''⟩ := hT.left k
    have m1 : ι ((N : K) * k'') ∈ Λ₁.lattice := by
      refine (hT.mem_iff _ _ (Tnat N _ _ hk'')).1 ?_
      rw [map_mul, map_natCast, hk, show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]
      exact a4 x
    have hc1 := h1.1
    have hz : (N : ℂ) * (ι k'' / c₁) ∈ (tauPair τ₁).lattice := by
      rw [← H1]
      convert m1 using 1
      rw [map_mul, map_natCast]; field_simp
    obtain ⟨y, hy⟩ := b5 _ hz
    have hy' : ι k'' - c₁ * tors N τ₁ y ∈ Λ₁.lattice := by
      have := (H1 _).2 hy
      convert this using 1
      field_simp
    obtain ⟨k', hk'⟩ := real1 (c₁ * tors N τ₁ y) k'' (by rw [← neg_sub]; exact neg_mem hy')
    exact ⟨y, (hR x y).2 ⟨k, k', hk, hk', adj k k'' k k' hk'' (by simp) (by rw [hk']; exact hy')⟩⟩
  ·
    obtain ⟨k₁, k₁', e₁, e₁', t₁⟩ := (hR _ _).1 hxy
    obtain ⟨k₂, k₂', e₂, e₂', t₂⟩ := (hR _ _).1 hxy'
    have t₁₂ := hT.sub _ _ _ _ t₁ t₂
    have d0 : c₀ * tors N τ₀ (x - x') - ι (k₁ - k₂) ∈ Λ₀.lattice := by
      rw [map_sub, e₁, e₂, show c₀ * tors N τ₀ (x - x') - (c₀ * tors N τ₀ x - c₀ * tors N τ₀ x')
        = c₀ * -(tors N τ₀ (x - x' + x') - (tors N τ₀ (x - x') + tors N τ₀ x')) by
          rw [sub_add_cancel]; ring, H0]
      exact neg_mem (a2 _ _)
    have d1 : c₁ * tors N τ₁ (y - y') - ι (k₁' - k₂') ∈ Λ₁.lattice := by
      rw [map_sub, e₁', e₂', show c₁ * tors N τ₁ (y - y') - (c₁ * tors N τ₁ y - c₁ * tors N τ₁ y')
        = c₁ * -(tors N τ₁ (y - y' + y') - (tors N τ₁ (y - y') + tors N τ₁ y')) by
          rw [sub_add_cancel]; ring, H1]
      exact neg_mem (b2 _ _)
    obtain ⟨m, hm⟩ := real0 _ _ d0
    obtain ⟨m', hm'⟩ := real1 _ _ d1
    exact (hR _ _).2 ⟨m, m', hm, hm', adj _ _ m m' t₁₂
      (by rw [hm, ← neg_sub]; exact neg_mem d0) (by rw [hm', ← neg_sub]; exact neg_mem d1)⟩
  ·
    obtain ⟨k, k', e, e', t⟩ := (hR _ _).1 hxy
    rw [← a3 x, ← b3 y, ← H0, ← H1, ← e, ← e']
    exact hT.mem_iff k k' t

end GlobalTheory.RelTors
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCorrespondence_torsion_relation_properties : ∀ (K : Type) [Field K] [CharZero K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTr ι Λ₀ Λ₁ T → IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x y, R x y ↔ ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ T k k') → (∀ x, ∃ y, R x y) ∧ (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) ∧ (∀ x y, R x y → (x = 0 ↔ y = 0)) := by
  atlas_forward_decl GlobalTheory.RelTors.main
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem exists_torsion_matrix : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  intro K _ _ ι g t Λ₀ Λ₁ Ω₀ Ω₁ h c₀ c₁ τ₀ τ₁ h₀ h₁ N _
  obtain ⟨a, b, c⟩ := GlobalTheory.T.latticeCorrespondence_torsion_relation_properties K ι Λ₀ Λ₁ (Tr t) c₀ c₁ τ₀ τ₁
    (GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ h) h₀ h₁ N
    (fun x y => ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ Tr t k k')
    (fun _ _ => Iff.rfl)
  exact GlobalTheory.T.additive_bijective_relation_rowVec_eq_matrix N _ a b c

end GlobalTheory.WpFam
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_matrix_of_conjugateTransport : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  atlas_forward_decl GlobalTheory.WpFam.exists_torsion_matrix
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.Transp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT c₀ c₁ τ₀ τ₁ h₀ h₁ ω₀ ω₁ hω₀ hω₁
  subst hω₀ hω₁
  have hT' := hT
  obtain ⟨hΩ₀, hΩ₁, -, -, -, hg₂, hg₃, hwp⟩ := hT'
  have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have hE := map_eisenstein_div_period g Λ₀ Λ₁ c₀ c₁ Ω₀ Ω₁ τ₀ τ₁ h₀ h₁ hg₂ hg₃
  have hs₀ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ₀ c₀ Ω₀ τ₀ h₀
  have hs₁ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ₁ c₁ Ω₁ τ₁ h₁
  have hs := GlobalTheory.T.galois_transport_second_eisenstein_cm K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  refine ⟨div_ne_zero (mul_ne_zero hΩ₀ h₀.1) h2πi, div_ne_zero (mul_ne_zero hΩ₁ h₁.1) h2πi,
    hE.1, hE.2, ?_, ?_⟩
  · rw [hs₀.1, hs₁.1, hs]
  · intro N _
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_torsion_matrix_of_conjugateTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT c₀ c₁ τ₀ τ₁ h₀ h₁ N
    refine ⟨A, hA, fun x => ?_⟩
    rw [(hs₀.2 N x).1, (hs₀.2 N x).2, (hs₁.2 N (vmul x A)).1, (hs₁.2 N (vmul x A)).2]
    by_cases hx : x = 0
    · have hv : vmul x A = 0 := ((GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x A).2 hx
      have ht : ∀ τ : ℍ, tors N τ 0 = 0 := by intro τ; simp [tors]
      rw [hv, hx, ht, ht, mul_zero, mul_zero]
      simp [PeriodPair.weierstrassP_zero, PeriodPair.derivWeierstrassP_zero]
    · obtain ⟨k, k', hk, hk', htr⟩ := hA x
      have hnot : ι k ∉ Λ₀.lattice := by
        rw [hk, ((GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ₀ c₀ τ₀ h₀).1 _), ((GlobalTheory.WpFam.TorsMem.main N τ₀).2.2.1 x)]
        exact hx
      rw [← hk, ← hk']
      exact hwp k k' hnot htr

end GlobalTheory.WpFam.Transp
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  atlas_forward_decl GlobalTheory.WpFam.Transp.main
end

section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  first | exact @GlobalTheory.wB_nonhol_correction | exact GlobalTheory.wB_nonhol_correction | (intros; apply GlobalTheory.wB_nonhol_correction <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HilbFam GlobalTheory.WpFam GlobalTheory.QFam ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane nonZeroDivisors Matrix

set_option autoImplicit false

namespace GlobalTheory.RoadE.ConjLat

def intA (K : Type) [Field K] [NumberField K] : Subring (Af K) where
  carrier := {z | ∀ v, z v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

section Quad

variable {K : Type} [Field K] [NumberField K]

theorem mem_intA {z : Af K} : z ∈ intA K ↔ ∀ v, Valued.v (z v) ≤ 1 :=
  forall_congr' fun _ => HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem exists_int {z : K} (hz : algebraMap K (Af K) z ∈ intA K) : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = z := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one K z fun v => ?_
  have := mem_intA.1 hz v
  rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this

theorem approx (D : ℕ) (hD : D ≠ 0) (z : Af K) : ∃ a : K, ∃ w ∈ intA K, z = algebraMap K (Af K) a + D * w := by
  obtain ⟨a, u, hu, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K D (Nat.pos_of_ne_zero hD)).1 z
  exact ⟨a, u, hu, by rw [e, nsmul_eq_mul]⟩

def IsW (t : (Af K)ˣ) (θ κ₁ κ₂ : K) (D : ℕ) (W : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  (∃ w ∈ intA K, (t : Af K) * algebraMap K (Af K) κ₁ = algebraMap K (Af K) (W 0 0 * θ + W 0 1) + D * w) ∧
  (∃ w ∈ intA K, (t : Af K) * algebraMap K (Af K) κ₂ = algebraMap K (Af K) (W 1 0 * θ + W 1 1) + D * w)

variable {t : (Af K)ˣ} {θ κ₁ κ₂ : K}

theorem exists_isW (hO : ∀ z : K, algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * θ + b)
    (hA : ∀ z : K, (t : Af K) * algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * κ₁ + b * κ₂)
    (D : ℕ) (hD : D ≠ 0) : ∃ W, IsW t θ κ₁ κ₂ D W := by
  have key : ∀ κ : K, (t : Af K) * algebraMap K (Af K) κ ∈ intA K → ∃ a b : ℤ, ∃ w ∈ intA K,
      (t : Af K) * algebraMap K (Af K) κ = algebraMap K (Af K) (a * θ + b) + D * w := fun κ hκ => by
    obtain ⟨a, w, hw, e⟩ := approx D hD ((t : Af K) * algebraMap K (Af K) κ)
    have : algebraMap K (Af K) a ∈ intA K := by
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem hκ (mul_mem (natCast_mem _ D) hw)
    obtain ⟨p, q, rfl⟩ := (hO a).1 this
    exact ⟨p, q, w, hw, e⟩
  obtain ⟨a, b, h1⟩ := key κ₁ ((hA _).2 ⟨1, 0, by simp⟩)
  obtain ⟨c, d, h2⟩ := key κ₂ ((hA _).2 ⟨0, 1, by simp⟩)
  exact ⟨!![a, b; c, d], by simpa using h1, by simpa using h2⟩

theorem IsW.of_dvd {D D' : ℕ} {W : Matrix (Fin 2) (Fin 2) ℤ} (h : IsW t θ κ₁ κ₂ D W) (hd : D' ∣ D) : IsW t θ κ₁ κ₂ D' W := by
  obtain ⟨m, rfl⟩ := hd
  obtain ⟨⟨w, hw, e⟩, ⟨w', hw', e'⟩⟩ := h
  exact ⟨⟨m * w, mul_mem (natCast_mem _ m) hw, by rw [e]; push_cast; ring⟩,
    ⟨m * w', mul_mem (natCast_mem _ m) hw', by rw [e']; push_cast; ring⟩⟩

theorem IsW.row (hO : ∀ z : K, algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * θ + b)
    (hI : ∀ a b : ℤ, (a : K) * θ + b = 0 → a = 0 ∧ b = 0)
    {D : ℕ} (hD : D ≠ 0) {W : Matrix (Fin 2) (Fin 2) ℤ} (h : IsW t θ κ₁ κ₂ D W) {p q r s : ℤ} {w : Af K} (hw : w ∈ intA K)
    (e : (t : Af K) * algebraMap K (Af K) (p * κ₁ + q * κ₂) = algebraMap K (Af K) (r * θ + s) + D * w) :
    ((p * W 0 0 + q * W 1 0 : ℤ) : ZMod D) = r ∧ ((p * W 0 1 + q * W 1 1 : ℤ) : ZMod D) = s := by
  obtain ⟨⟨w₁, hw₁, e₁⟩, ⟨w₂, hw₂, e₂⟩⟩ := h
  have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.2 hD
  set z : K := ((p * W 0 0 + q * W 1 0 - r : ℤ) * θ + (p * W 0 1 + q * W 1 1 - s : ℤ)) with hz
  have h1 : algebraMap K (Af K) z = D * (w - p * w₁ - q * w₂) := by
    simp only [hz, map_add, map_mul, map_intCast] at e e₁ e₂ ⊢
    push_cast
    linear_combination e - p * e₁ - q * e₂
  have h2 : algebraMap K (Af K) (z / D) = w - p * w₁ - q * w₂ := by
    rw [div_eq_inv_mul, map_mul, h1, ← mul_assoc, ← map_natCast (algebraMap K (Af K)), ← map_mul, inv_mul_cancel₀ hDK,
      map_one, one_mul]
  obtain ⟨a, b, hab⟩ := (hO (z / D)).1 (h2 ▸ sub_mem (sub_mem hw (mul_mem (intCast_mem _ p) hw₁))
    (mul_mem (intCast_mem _ q) hw₂))
  rw [div_eq_iff hDK] at hab
  obtain ⟨ha, hb⟩ := hI (p * W 0 0 + q * W 1 0 - r - a * D) (p * W 0 1 + q * W 1 1 - s - b * D) (by
    rw [hz] at hab; push_cast at hab ⊢; linear_combination hab)
  constructor
  · rw [show p * W 0 0 + q * W 1 0 = r + a * D by linear_combination ha]; simp
  · rw [show p * W 0 1 + q * W 1 1 = s + b * D by linear_combination hb]; simp

theorem IsW.exists_inv (hO : ∀ z : K, algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * θ + b)
    (hI : ∀ a b : ℤ, (a : K) * θ + b = 0 → a = 0 ∧ b = 0)
    (hA : ∀ z : K, (t : Af K) * algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * κ₁ + b * κ₂)
    {D : ℕ} (hD : D ≠ 0) {W : Matrix (Fin 2) (Fin 2) ℤ} (h : IsW t θ κ₁ κ₂ D W) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℤ, V.map (Int.cast : ℤ → ZMod D) * W.map (Int.cast : ℤ → ZMod D) = 1 := by
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.LatDecomp.exists_nat_mul_integral (t : Af K)
  have key : ∀ r s : ℤ, ∃ p q : ℤ,
      ((p * W 0 0 + q * W 1 0 : ℤ) : ZMod D) = r ∧ ((p * W 0 1 + q * W 1 1 : ℤ) : ZMod D) = s := fun r s => by
    obtain ⟨a, w, hw, e⟩ := approx (D * d) (mul_ne_zero hD hd0)
      (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) (r * θ + s))
    have hw' : -((d : Af K) * t * w) ∈ intA K := neg_mem (mul_mem hd hw)
    have e' : (t : Af K) * algebraMap K (Af K) a = algebraMap K (Af K) (r * θ + s) + D * -((d : Af K) * t * w) := by
      have := congrArg (fun z => (t : Af K) * z) e
      simp only [← mul_assoc, Units.mul_inv, one_mul] at this
      rw [this]; push_cast; ring
    obtain ⟨p, q, rfl⟩ := (hA a).1 (e' ▸ add_mem ((hO _).2 ⟨r, s, rfl⟩) (mul_mem (natCast_mem _ D) hw'))
    exact ⟨p, q, h.row hO hI hD hw' e'⟩
  obtain ⟨a, b, h1, h2⟩ := key 1 0
  obtain ⟨c, d, h3, h4⟩ := key 0 1
  refine ⟨!![a, b; c, d], ?_⟩
  push_cast at h1 h2 h3 h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]

end Quad

theorem lift_inv {D : ℕ} {P Q : Matrix (Fin 2) (Fin 2) ℤ}
    (h : P.map (Int.cast : ℤ → ZMod D) * Q.map (Int.cast : ℤ → ZMod D) = 1) :
    ∃ Z : Matrix (Fin 2) (Fin 2) ℤ, P * Q = 1 + (D : ℤ) • Z := by
  have h' : ∀ i j, ∃ z, (P * Q - 1) i j = (D : ℤ) * z := fun i j => by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).1 ?_
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply] at this ⊢
    push_cast
    rw [this]; split_ifs <;> simp
  choose Z hZ using h'
  refine ⟨Matrix.of Z, ?_⟩
  rw [← sub_eq_iff_eq_add']
  ext i j
  simpa using hZ i j

section Lat

variable {F : Type} [Field F] [NumberField F]

def vm (x : Fin 2 → F) (P : Matrix (Fin 2) (Fin 2) ℤ) : Fin 2 → F := x ᵥ* P.map (Int.cast : ℤ → F)

omit [NumberField F] in

theorem vm_apply (x : Fin 2 → F) (P : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) : vm x P j = x 0 * P 0 j + x 1 * P 1 j := by
  simp [vm, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

omit [NumberField F] in

theorem vm_vm (x : Fin 2 → F) {P Q Z : Matrix (Fin 2) (Fin 2) ℤ} {D : ℕ} (h : P * Q = 1 + (D : ℤ) • Z) :
    vm (vm x P) Q = x + (D : 𝓞 F) • vm x Z := by
  have h' : ∀ i j, ((P i 0 * Q 0 j + P i 1 * Q 1 j : ℤ) : F) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j + D * Z i j : ℤ) : F) :=
    fun i j => by
      have := congrFun (congrFun h i) j
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [this]
  funext j
  have h0 := h' 0 j
  have h1 := h' 1 j
  simp only [vm_apply, Pi.add_apply, Pi.smul_apply, Algebra.smul_def, map_natCast]
  push_cast at h0 h1
  fin_cases j
  · simp [Matrix.one_apply] at h0 h1 ⊢
    linear_combination x 0 * h0 + x 1 * h1
  · simp [Matrix.one_apply] at h0 h1 ⊢
    linear_combination x 0 * h0 + x 1 * h1

theorem vm_mem {x : Fin 2 → F} (hx : x ∈ stdLat F) (P : Matrix (Fin 2) (Fin 2) ℤ) : vm x P ∈ stdLat F := fun j _ => by
  rw [vm_apply, mul_comm (x 0), mul_comm (x 1), ← zsmul_eq_mul, ← zsmul_eq_mul]
  exact add_mem (zsmul_mem (hx 0 trivial) _) (zsmul_mem (hx 1 trivial) _)

theorem mem_twist (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (x : Fin 2 → F) :
    x ∈ HilbFam.twist N L α ↔ ∃ l ∈ L, ∃ z ∈ stdLat F, x = vm l (α.map (ZMod.cast : ZMod N → ℤ)) + (N : 𝓞 F) • z := by
  have e : ∀ z : Fin 2 → F, vm z ((N : ℤ) • 1) = (N : 𝓞 F) • z := fun z => by
    funext j
    simp only [vm_apply, Pi.smul_apply, Algebra.smul_def (N : 𝓞 F), map_natCast, Matrix.smul_apply]
    fin_cases j <;> simp [mul_comm, Matrix.one_apply]
  rw [HilbFam.twist, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨l, hl, z, hz, by rw [← e]; rfl⟩
  · rintro ⟨l, hl, z, hz, rfl⟩
    exact ⟨_, ⟨l, hl, rfl⟩, _, ⟨z, hz, rfl⟩, by rw [← e]; rfl⟩

omit [NumberField F] in

theorem vm_add_smul (x z : Fin 2 → F) (a : 𝓞 F) (P : Matrix (Fin 2) (Fin 2) ℤ) :
    vm (x + a • z) P = vm x P + a • vm z P := by
  funext j
  simp only [vm_apply, Pi.add_apply, Pi.smul_apply, Algebra.smul_def]
  ring

theorem twist_iff {N d : ℕ} {L : Lat F} (hL : HasLevel N L) {α : Matrix (Fin 2) (Fin 2) (ZMod N)}
    {W V Z Z' Z'' : Matrix (Fin 2) (Fin 2) ℤ} (h1 : α.map (ZMod.cast : ZMod N → ℤ) * W = 1 + (N : ℤ) • Z)
    (h2 : W * α.map (ZMod.cast : ZMod N → ℤ) = 1 + (N : ℤ) • Z') (h3 : W * V = 1 + (d : ℤ) • Z'')
    {x : Fin 2 → F} (hx : (d : 𝓞 F) • x ∈ stdLat F) : x ∈ HilbFam.twist N L α ↔ vm x W ∈ L := by
  rw [mem_twist]
  constructor
  · rintro ⟨l, hl, z, hz, rfl⟩
    rw [vm_add_smul, vm_vm l h1]
    exact add_mem (add_mem hl (hL.1 _ (vm_mem (hL.2 hl) _))) (hL.1 _ (vm_mem hz _))
  · intro h
    have hs : x ∈ stdLat F := by
      have e := vm_vm x h3
      have e' := vm_add_smul 0 x (d : 𝓞 F) Z''
      have e0 : vm (0 : Fin 2 → F) Z'' = 0 := Matrix.zero_vecMul _
      rw [zero_add, e0, zero_add] at e'
      rw [← e'] at e
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem (vm_mem (hL.2 h) _) (vm_mem hx _)
    exact ⟨_, h, -vm x Z', neg_mem (vm_mem hs _), by rw [vm_vm x h2, smul_neg, add_neg_cancel_right]⟩

theorem exists_den (x : Fin 2 → F) : ∃ d : ℕ, d ≠ 0 ∧ (d : 𝓞 F) • x ∈ stdLat F := by
  have h : ∀ i, ∃ d : ℕ, d ≠ 0 ∧ (d : 𝓞 F) • x i ∈ (1 : Submodule (𝓞 F) F) := fun i => by
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.LatDecomp.exists_nat_mul_integral (algebraMap F (Af F) (x i))
    obtain ⟨r, hr⟩ := exists_int (K := F) (z := d * x i) (by rw [map_mul, map_natCast]; exact hd)
    exact ⟨d, hd0, Submodule.mem_one.2 ⟨r, by rw [hr, Algebra.smul_def, map_natCast]⟩⟩
  obtain ⟨a, ha0, ha⟩ := h 0
  obtain ⟨b, hb0, hb⟩ := h 1
  refine ⟨a * b, mul_ne_zero ha0 hb0, fun j _ => ?_⟩
  fin_cases j
  · show ((a * b : ℕ) : 𝓞 F) • x 0 ∈ _
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ ha
  · show ((a * b : ℕ) : 𝓞 F) • x 1 ∈ _
    rw [Nat.cast_mul, mul_smul]; exact Submodule.smul_mem _ _ hb

end Lat

theorem mem_nlat {E : Type} [Field E] [NumberField E] (c : Ideal (OF E)) (y : (Af E)ˣ) {n : ℕ} (hn : 0 < n) (e : E) :
    (∃ y' ∈ lattice c y, (n : E) * y' = e) ↔
      algebraMap E (Af E) e * algebraMap E (Af E) (n : E)⁻¹ * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [← map_mul]
  constructor
  · rintro ⟨y', h, rfl⟩
    rwa [mul_comm (n : E), mul_inv_cancel_right₀ hn']
  · intro h
    exact ⟨e * (n : E)⁻¹, h, by field_simp⟩

theorem twist_lattice : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E]
  (c : Ideal (OF E)) (y : (Af E)ˣ) (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (θ₀ κ₁ κ₂ : K)
  (Λ₀ Λ₁ : PeriodPair) (c₁ : ℂ) (τ₀ τ₁ : ℍ) (N : ℕ) [NeZero N] (A : GL (Fin 2) (ZMod N)) (n : ℕ)
  (L₀ : Lat (maximalRealSubfield E)),
  Module.finrank ℚ K = 2 → c ≠ ⊥ →
  GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ → IsTauOf Λ₀ 1 τ₀ → ι θ₀ = (τ₀ : ℂ) →
  GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsInvIdealOf t 𝔞 → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ₁ → IsTauOf Λ₁ c₁ τ₁ → ι κ₁ = c₁ * τ₁ → ι κ₂ = c₁ →
  (∀ x : Fin 2 → ZMod N, ∃ k k' : K, ι k = tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') →
  0 < n → HasLevel N L₀ →
  (∀ x : Fin 2 → maximalRealSubfield E, x ∈ L₀ ↔
    ∃ y' ∈ lattice c y, (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * algebraMap K E θ₀ + ((x 1 : maximalRealSubfield E) : E)) →
  ∀ x : Fin 2 → maximalRealSubfield E, x ∈ HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N)) ↔
    ∃ y' ∈ lattice c (y * (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t)⁻¹),
      (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * algebraMap K E κ₁ + ((x 1 : maximalRealSubfield E) : E) * algebraMap K E κ₂ := by
  intro K _ _ ι E _ _ _ _ c y t 𝔞 θ₀ κ₁ κ₂ Λ₀ Λ₁ c₁ τ₀ τ₁ N _ A n L₀ _ hc h0 hτ₀ hθ h𝔞 h1 hτ₁ hκ₁ hκ₂ htor hn hL hL₀ x
  have hN : N ≠ 0 := NeZero.ne N
  have hO : ∀ z : K, algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * θ₀ + b := fun z => by
    have e1 : algebraMap K (Af K) z ∈ intA K ↔ z ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨exists_int, fun ⟨r, hr⟩ => hr ▸ GlobalTheory.LatDecomp.algebraMap_integral r⟩
    have e2 : z ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ ι z ∈ Λ₀.lattice := by
      rw [← SetLike.mem_coe (p := Λ₀.lattice), h0, ι.injective.mem_set_image]; rfl
    rw [e1, e2, hτ₀.2]
    refine exists₂_congr fun a b => ?_
    rw [← ι.injective.eq_iff]; simp [hθ]
  have hA : ∀ z : K, (t : Af K) * algebraMap K (Af K) z ∈ intA K ↔ ∃ a b : ℤ, z = a * κ₁ + b * κ₂ := fun z => by
    have e2 : z ∈ 𝔞 ↔ ι z ∈ Λ₁.lattice := by
      rw [← SetLike.mem_coe (p := Λ₁.lattice), h1, ι.injective.mem_set_image]; rfl
    rw [mem_intA, ← h𝔞 z, e2, hτ₁.2]
    refine exists₂_congr fun a b => ?_
    rw [← ι.injective.eq_iff, map_add, map_mul, map_mul, hκ₁, hκ₂, map_intCast, map_intCast]
    constructor <;> intro h <;> linear_combination h
  have hI : ∀ a b : ℤ, (a : K) * θ₀ + b = 0 → a = 0 ∧ b = 0 := fun a b h => by
    have h' := congrArg (fun z => (ι z).im) h
    simp [hθ, τ₀.im_ne_zero] at h'
    subst h'
    simpa using h
  obtain ⟨d, hd0, hd⟩ := exists_den x
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.LatDecomp.exists_nat_mul_good hc y (n : E)⁻¹
  obtain ⟨W, hW⟩ := exists_isW hO hA (N * (M * d)) (mul_ne_zero hN (mul_ne_zero hM0 hd0))
  obtain ⟨V, hV⟩ := (hW.of_dvd (D' := d) ⟨N * M, by ring⟩).exists_inv hO hI hA hd0
  obtain ⟨Z'', h3⟩ := lift_inv (mul_eq_one_comm.1 hV)
  have hAW : ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → ZMod N) *
      W.map (Int.cast : ℤ → ZMod N) = 1 := by
    have e0 : ((A : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → ZMod N) = A := by
      ext i j; simp
    rw [e0]
    refine Matrix.ext_iff_vecMul.2 fun v => ?_
    obtain ⟨k, k', hk, hk', hT⟩ := htor v
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    have ek : (((v 0).val : ℤ) : K) * θ₀ + (((v 1).val : ℤ) : K) = N * k := ι.injective (by
      simp only [map_add, map_mul, map_intCast, map_natCast, hk, hθ, tors, Int.cast_natCast]; field_simp)
    have ek' : (((vmul v A 0).val : ℤ) : K) * κ₁ + (((vmul v A 1).val : ℤ) : K) * κ₂ = N * k' := ι.injective (by
      simp only [map_add, map_mul, map_intCast, map_natCast, hk', hκ₁, hκ₂, tors, Int.cast_natCast]; field_simp)
    obtain ⟨r0, r1⟩ := (hW.of_dvd (D' := N) ⟨_, rfl⟩).row hO hI hN (mem_intA.2 hT)
      (p := (vmul v A 0).val) (q := (vmul v A 1).val) (r := (v 0).val) (s := (v 1).val) (by
        rw [ek, ek', map_mul, map_mul, map_natCast]; ring)
    push_cast at r0 r1
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at r0 r1
    rw [← Matrix.vecMul_vecMul, Matrix.vecMul_one]
    funext j
    change (vmul v A ᵥ* _) j = _
    fin_cases j
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using r0
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using r1
  obtain ⟨Z, h1'⟩ := lift_inv hAW
  obtain ⟨Z', h2'⟩ := lift_inv (mul_eq_one_comm.1 hAW)
  rw [twist_iff hL h1' h2' h3 hd, hL₀, mem_nlat c _ hn, mem_nlat c _ hn]
  obtain ⟨⟨w₁, hw₁, e₁⟩, ⟨w₂, hw₂, e₂⟩⟩ := hW
  have f₁ := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K E) e₁
  have f₂ := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K E) e₂
  simp only [map_add, map_mul, GlobalTheory.LatDecomp.finiteAdeleMap_algebraMap, map_intCast, map_natCast] at f₁ f₂
  have hx : ∀ i, (d : Af E) * algebraMap E (Af E) ((x i : maximalRealSubfield E) : E) ∈ intA E := fun i => by
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hd i trivial)
    have hr' : (d : E) * ((x i : maximalRealSubfield E) : E) = ((algebraMap (OF E) (𝓞 E) r : 𝓞 E) : E) := by
      have := congrArg (fun z : maximalRealSubfield E => (z : E)) hr
      simp only [Pi.smul_apply, Algebra.smul_def, map_natCast, Subfield.coe_mul, SubringClass.coe_natCast] at this
      exact this.symm
    rw [← map_natCast (algebraMap E (Af E)), ← map_mul, hr']
    exact GlobalTheory.LatDecomp.algebraMap_integral _
  have hz := hM _ (mul_mem (natCast_mem (intA E) N) (add_mem
    (mul_mem (hx 0) (GlobalTheory.LatDecomp.finiteAdeleMap_integral (mem_intA.1 hw₁)))
    (mul_mem (hx 1) (GlobalTheory.LatDecomp.finiteAdeleMap_integral (mem_intA.1 hw₂)))))
  rw [← add_mem_cancel_right (H := hatO c) hz, mul_inv_rev, inv_inv, Units.val_mul]
  have hT : (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t : Af E) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K E (t : Af K) := rfl
  refine iff_of_eq (congrArg (· ∈ hatO c) ?_)
  simp only [hT, vm_apply, Subfield.coe_add, Subfield.coe_mul, SubringClass.coe_intCast, map_add, map_mul, map_intCast,
    map_natCast]
  push_cast at f₁ f₂
  linear_combination (-(algebraMap E (Af E) (n : E)⁻¹ * ((y⁻¹ : (Af E)ˣ) : Af E))) *
    (algebraMap E (Af E) ((x 0 : maximalRealSubfield E) : E) * f₁ + algebraMap E (Af E) ((x 1 : maximalRealSubfield E) : E) * f₂)

end GlobalTheory.RoadE.ConjLat
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.IdealTheta

theorem exists_primitive_rat {K : Type} [Field K] [CharZero K] (a₁ a₂ : K) (r s : ℚ)
    (h : (r : K) * a₁ + (s : K) * a₂ = 1) :
    ∃ (c : ℚ) (p q u v : ℤ), 0 < c ∧ p * v - q * u = 1 ∧ (p : K) * a₁ + (q : K) * a₂ = (c : K) := by
  set A : ℤ := r.num * s.den with hA
  set B : ℤ := s.num * r.den with hB
  have hr : (r : K) * (r.den : K) = (r.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num r)
    push_cast at this; exact this
  have hs : (s : K) * (s.den : K) = (s.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num s)
    push_cast at this; exact this
  have hAB : (A : K) * a₁ + (B : K) * a₂ = (r.den : K) * (s.den : K) := by
    rw [hA, hB]; push_cast
    rw [← hr, ← hs]
    linear_combination ((r.den : K) * (s.den : K)) * h
  have hN : (r.den : K) * (s.den : K) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr s.den_nz)
  have hg : Int.gcd A B ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rw [h0.1, h0.2] at hAB
    apply hN
    rw [← hAB]; simp
  obtain ⟨p, hp⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
  obtain ⟨q, hq⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
  have hbez := Int.gcd_eq_gcd_ab A B
  set g : ℕ := Int.gcd A B with hgdef
  have hgZ : (g : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hgK : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr hg
  refine ⟨((r.den : ℚ) * (s.den : ℚ)) / (g : ℚ), p, q, -Int.gcdB A B, Int.gcdA A B, ?_, ?_, ?_⟩
  · have h1 : (0 : ℚ) < r.den := Nat.cast_pos.mpr r.den_pos
    have h2 : (0 : ℚ) < s.den := Nat.cast_pos.mpr s.den_pos
    have h3 : (0 : ℚ) < g := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)
    positivity
  · apply mul_left_cancel₀ hgZ
    linear_combination -hbez - Int.gcdA A B * hp - Int.gcdB A B * hq
  · have hpK : (A : K) = (g : K) * (p : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hp
    have hqK : (B : K) = (g : K) * (q : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hq
    push_cast
    rw [eq_div_iff hgK, ← hAB, hpK, hqK]
    ring

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) → 𝔞 ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → ∃ (c : ℚ) (θ : K) (τ : ℍ), 0 < c ∧ ι θ = (τ : ℂ) ∧ IsTauOf Λ (c : ℂ) τ ∧ ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
  intro K _ _ d δ ι 𝔞 Λ hK _ _ _ hΛ
  obtain ⟨c₀, τ₀, hc₀, hlat⟩ := latTau Λ
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ y : K, y ∈ 𝔞 ∧ ι y = z := by
    intro z
    have : z ∈ (Λ.lattice : Set ℂ) ↔ z ∈ ι '' (𝔞 : Set K) := by rw [hΛ]
    exact this
  obtain ⟨a₁, -, ha₁⟩ := (hmem (c₀ * τ₀)).mp ((hlat _).mpr ⟨1, 0, by simp⟩)
  obtain ⟨a₂, -, ha₂⟩ := (hmem c₀).mp ((hlat _).mpr ⟨0, 1, by simp⟩)
  have hA : ∀ x : K, x ∈ 𝔞 ↔ ∃ m n : ℤ, x = (m : K) * a₁ + (n : K) * a₂ := by
    intro x
    have h1 : x ∈ 𝔞 ↔ ι x ∈ Λ.lattice := by
      rw [hmem]
      exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => ι.injective e ▸ hy⟩
    rw [h1, hlat]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [← ι.injective.eq_iff]
    simp only [map_add, map_mul, map_intCast, ha₁, ha₂]
    constructor <;> intro h <;> rw [h] <;> ring
  have hli : LinearIndependent ℚ ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro r s h
    rw [Rat.smul_def, Rat.smul_def] at h
    have h1 := congrArg ι h
    simp only [map_add, map_mul, map_ratCast, ha₁, ha₂, map_zero] at h1
    have h2 : (r : ℂ) * τ₀ + (s : ℂ) = 0 := by
      apply mul_left_cancel₀ hc₀
      linear_combination h1
    have h3 := congrArg Complex.im h2
    have hr : r = 0 := by
      have := τ₀.im_ne_zero
      simpa [this] using h3
    subst hr
    simpa using h2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (show (1 : K) ∈ Submodule.span ℚ (Set.range ![a₁, a₂]) by rw [hspan]; trivial)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hw
  obtain ⟨c, p, q, u, v, hc, hdet, hcK⟩ := exists_primitive_rat a₁ a₂ (w 0) (w 1) hw
  have hcK0 : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  have hcC0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdetK : (p : K) * v - q * u = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hdet
  have hdetR : (p : ℝ) * v - q * u = 1 := by exact_mod_cast hdet
  set θ : K := -((u : K) * a₁ + (v : K) * a₂) / (c : K) with hθ
  have hcθ : (c : K) * θ = -((u : K) * a₁ + (v : K) * a₂) := by
    rw [hθ]; field_simp
  have hcC : (c : ℂ) = c₀ * ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcK
    simp only [map_add, map_mul, map_ratCast, map_intCast, ha₁, ha₂] at h1
    linear_combination -h1
  have hz : ((p : ℂ) * τ₀ + q) ≠ 0 := by
    intro h0; apply hcC0; rw [hcC, h0, mul_zero]
  have hιθ : ι θ = -((u : ℂ) * τ₀ + v) / ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcθ
    simp only [map_add, map_mul, map_neg, map_ratCast, map_intCast, ha₁, ha₂] at h1
    rw [eq_div_iff hz]
    apply mul_left_cancel₀ hc₀
    rw [hcC] at h1
    linear_combination h1
  have him : 0 < (ι θ).im := by
    rw [hιθ, Complex.div_im, ← sub_div]
    refine div_pos ?_ (Complex.normSq_pos.mpr hz)
    have hy : 0 < (τ₀ : ℂ).im := τ₀.im_pos
    simp only [Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.intCast_im, Complex.intCast_re]
    have : -(↑u * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) * (↑p * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑q) -
        -(↑u * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑v) * (↑p * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) = (τ₀ : ℂ).im := by
      linear_combination (τ₀ : ℂ).im * hdetR
    rw [this]; exact hy
  have hmain : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
    intro x
    rw [hA]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * q - n * p, m * v - n * u, ?_⟩
      push_cast
      linear_combination (-((m : K) * q - n * p)) * hcθ + ((m : K) * v - n * u) * hcK
        - ((m : K) * a₁ + (n : K) * a₂) * hdetK
    · rintro ⟨a, b, rfl⟩
      refine ⟨b * p - a * u, b * q - a * v, ?_⟩
      push_cast
      linear_combination (a : K) * hcθ - (b : K) * hcK
  refine ⟨c, θ, ⟨ι θ, him⟩, hc, rfl, ⟨hcC0, fun z => ?_⟩, hmain⟩
  rw [hmem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, rfl⟩ := (hmain y).mp hy
    exact ⟨a, b, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, (hmain _).mpr ⟨a, b, rfl⟩, by simp⟩

end GlobalTheory.IdealTheta
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UpperHalfPlane GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory.LatJet (EisExp FR)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula lamInf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf IsInvIdealOf nrm)
open GlobalTheory.ToricTransport (coordIn)
open ReciprocityTheory.ChartRestriction.L1 (IsTauOf)
open scoped Classical nonZeroDivisors MatrixGroups

namespace GlobalTheory.LatConjEll

theorem indep {K : Type} [Field K] (ι : K →+* ℂ) (θ : K) (τ : ℍ) (h : ι θ = τ) (a b : ℤ) (hab : (a : K) * θ + b = 0) :
    a = 0 ∧ b = 0 := by
  have h1 := congrArg ι hab
  simp only [map_add, map_mul, map_intCast, h, map_zero] at h1
  have h2 := congrArg Complex.im h1
  have ha : a = 0 := by
    have : (a : ℝ) * τ.im = 0 := by simpa using h2
    exact_mod_cast (mul_eq_zero.1 this).resolve_right τ.im_pos.ne'
  subst ha
  exact ⟨rfl, by simpa using h1⟩

theorem covol {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (θ₀ θ₁ : K) (c : ℚ) (τ₀ τ₁ : ℍ)
    (hc : 0 < c) (h0 : ι θ₀ = τ₀) (h1 : ι θ₁ = τ₁)
    (hO : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ ∃ a b : ℤ, x = (a : K) * θ₀ + b)
    (ha : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ₁ + (b : K))) :
    (c : ℝ) ^ 2 * τ₁.im = nrm 𝔞 * τ₀.im := by
  obtain ⟨θ, hθ⟩ := (FractionalIdeal.mem_one_iff _).1 ((hO θ₀).2 ⟨1, 0, by simp⟩)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.Basis.mk (v := ![θ, 1])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply indep ι θ₀ τ₀ h0
      have := congrArg (algebraMap (𝓞 K) K) hst
      simpa [hθ] using this)
    (by
      intro x _
      obtain ⟨u, v, huv⟩ := (hO (algebraMap (𝓞 K) K x)).1 ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
      rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
      refine ⟨u, v, FaithfulSMul.algebraMap_injective (𝓞 K) K ?_⟩
      simp [huv, hθ])
  let bI : Module.Basis (Fin 2) ℤ 𝔞 := Module.Basis.mk
    (v := ![⟨c * θ₁, (ha _).2 ⟨1, 0, by simp⟩⟩, ⟨c, (ha _).2 ⟨0, 1, by simp⟩⟩])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply indep ι θ₁ τ₁ h1
      have := congrArg Subtype.val hst
      apply mul_left_cancel₀ hcK
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, Submodule.coe_zero] at this
      linear_combination this)
    (by
      intro x _
      obtain ⟨u, v, huv⟩ := (ha x).1 x.2
      rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
      refine ⟨u, v, Subtype.ext ?_⟩
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul]
      rw [huv]; ring)
  have key := FractionalIdeal.abs_det_basis_change b 𝔞 bI
  set B := b.localizationLocalization ℚ ℤ⁰ K with hB
  have hB0 : B 0 = θ₀ := by simp [hB, b, hθ]
  have hB1 : B 1 = 1 := by simp [hB, b]
  have e0 : (bI 0 : K) = c * θ₁ := by simp [bI]
  have e1 : (bI 1 : K) = c • B 1 := by simp [bI, hB1, Rat.smul_def]
  have hs := B.sum_repr (c * θ₁)
  rw [Fin.sum_univ_two, hB0, hB1] at hs
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at key
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply, e0, e1, map_smul, Module.Basis.repr_self] at key
  simp at key
  have h2 := congrArg (fun z => (ι z).im) hs
  simp [Rat.smul_def, h0, h1] at h2
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hp : (0 : ℝ) < ((B.repr (c * θ₁) 0 : ℚ) : ℝ) := by
    have := mul_pos hcR τ₁.im_pos
    rw [← h2] at this
    exact (pos_iff_pos_of_mul_pos this).2 τ₀.im_pos
  have hp' : 0 < B.repr (c * θ₁) 0 := by exact_mod_cast hp
  rw [nrm, ← key, abs_of_pos hp', abs_of_pos hc]
  push_cast
  linear_combination (-(c : ℝ)) * h2

theorem ratio_rat {K : Type} [Field K] (ι : K →+* ℂ) (d : ℕ) (hd : 0 < d) (δ θ : K) (τ : ℍ) (hδ : δ ^ 2 = -(d : K)) (h : ι θ = τ)
    (a b : ℤ) (hab : δ = a * θ + b) : ∃ q : ℚ, 2 * τ.im / Real.sqrt d = q := by
  have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp [pow_two] at hre him
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : (ι δ).im = a * τ.im := by rw [hab]; simp [h]
  have h4 : (ι δ).re = 0 := by
    by_contra hne
    have : (ι δ).im = 0 := by
      have : 2 * (ι δ).re * (ι δ).im = 0 := by linarith
      simpa [hne] using this
    rw [this] at hre
    nlinarith [mul_self_nonneg (ι δ).re]
  have h5 : (d : ℝ) = (a * τ.im) ^ 2 := by rw [← h3]; rw [h4] at hre; linarith
  have ha : (a : ℝ) ≠ 0 := by
    intro h0; rw [h0] at h5; simp at h5; omega
  refine ⟨2 / |(a : ℚ)|, ?_⟩
  rw [h5, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos τ.im_pos]
  have := τ.im_pos
  have := abs_pos.2 ha
  push_cast
  field_simp

theorem sum_transport {J : Type} [Fintype J] [DecidableEq J] (g : ℂ ≃+* ℂ) (σ : J ≃ J) (k a : ℕ) (κ κ' : J → ℕ)
    (hκ : ∀ j, κ' (σ j) = κ j) (x₀ x₁ ω₀ ω₁ : ℂ) (H₀ H₁ : (J → ℕ) → ℂ) (hx : g (x₀ / ω₀ ^ 2) = x₁ / ω₁ ^ 2)
    (hH : ∀ μ : J → ℕ, g (H₀ μ / ω₀ ^ (a + 2 * ∑ j, μ j)) = H₁ (fun j => μ (σ.symm j)) / ω₁ ^ (a + 2 * ∑ j, μ j)) :
    g ((∑ μ ∈ Finset.Iic κ, ((∏ j, rco k (κ j) (μ j) : ℤ) : ℂ) * x₀ ^ (∑ j, (κ j - μ j)) * H₀ μ) / ω₀ ^ (a + 2 * ∑ j, κ j)) =
      (∑ μ ∈ Finset.Iic κ', ((∏ j, rco k (κ' j) (μ j) : ℤ) : ℂ) * x₁ ^ (∑ j, (κ' j - μ j)) * H₁ μ) / ω₁ ^ (a + 2 * ∑ j, κ j) := by
  rw [Finset.sum_div, Finset.sum_div, map_sum]
  have hκ' : ∀ j, κ' j = κ (σ.symm j) := fun j => by rw [← hκ]; simp
  refine Finset.sum_equiv (σ.arrowCongr (Equiv.refl ℕ)) (fun μ => ?_) (fun μ hμ => ?_)
  · simp only [Finset.mem_Iic, Pi.le_def, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, hκ']
    exact ⟨fun h j => h _, fun h j => by simpa using h (σ j)⟩
  · have hle : ∀ j, μ j ≤ κ j := Finset.mem_Iic.1 hμ
    have hsum : ∑ j, κ j = ∑ j, (κ j - μ j) + ∑ j, μ j := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => (Nat.sub_add_cancel (hle j)).symm
    have hsp : ∀ (r x H ω : ℂ), r * x ^ (∑ j, (κ j - μ j)) * H / ω ^ (a + 2 * ∑ j, κ j) =
        r * (x / ω ^ 2) ^ (∑ j, (κ j - μ j)) * (H / ω ^ (a + 2 * ∑ j, μ j)) := fun r x H ω => by
      rw [show a + 2 * ∑ j, κ j = 2 * ∑ j, (κ j - μ j) + (a + 2 * ∑ j, μ j) by rw [hsum]; ring, pow_add, pow_mul, div_pow]
      ring
    have hf : (σ.arrowCongr (Equiv.refl ℕ)) μ = fun j => μ (σ.symm j) := rfl
    have e1 : ∏ j, rco k (κ' j) (μ (σ.symm j)) = ∏ j, rco k (κ j) (μ j) :=
      (Fintype.prod_equiv σ _ _ fun j => by simp [hκ]).symm
    have e2 : ∑ j, (κ' j - μ (σ.symm j)) = ∑ j, (κ j - μ j) :=
      (Fintype.sum_equiv σ _ _ fun j => by simp [hκ]).symm
    rw [hf]
    simp only [e1, e2]
    rw [hsp, hsp, map_mul, map_mul, map_pow, hx, hH, map_intCast]

theorem value_eq (hE : EisExp) (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n s N d : ℕ) (κ : I → ℕ) (Ch : ℍ → ℂ) (S : ℂ → ℂ)
    (Ω c ω : ℂ) (hf : 2 ≤ Module.finrank ℚ (FR E)) (hs : 1 ≤ s) (hN : 0 < N) (hL : HasLevel N L)
    (he : ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) (hθ : ∀ i, φ i θ = (τ : ℂ)) (hn : 0 < n)
    (hmem : ∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E))
    (hcard : Fintype.card I = Module.finrank ℚ (FR E)) (hD : DerivFormula φ (2 * s) Λ) (hS : IsLatSum φ (2 * s) κ Λ S)
    (hc : c ≠ 0) (hω : ω = Ω * c / (2 * Real.pi * Complex.I)) :
    coordIn E d s κ Ω (S 0) = (-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) *
      (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * c ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) *
      ((∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) *
        (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) *
          hfun (2 * s) L μ Ch τ) / ω ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i)) := by
  obtain ⟨⟨g, hg⟩, hD⟩ := hD
  obtain ⟨u, hu⟩ := GlobalTheory.LatConjOne.exists_list_count κ
  have e1 := ((hD g hg).2 κ u (fun i => by convert hu i)).1 S hS
  have e2 := GlobalTheory.T.hilbertEisenstein_value_derivatives_via_jets hE E I φ e θ τ Λ L n s N g κ u Ch hf hs hN hL he hθ hn hmem hg hu
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have him : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hn0 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  have hq : ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) = ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) * ((Real.pi / τ.im : ℝ) : ℂ) := by
    push_cast; field_simp
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  rw [coordIn, GlobalTheory.LatConjOne.cmPeriodConstant_eq_of_card_cmType E d (by omega) hcard κ, hcard, hq, mul_pow, hω, div_pow, mul_pow Ω c]
  rw [e1] at e2
  generalize (∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), (_ : ℂ)) = T at e2 ⊢
  have hcM := pow_ne_zero (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) hc
  have hpM := pow_ne_zero (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) h2pi
  rw [div_eq_iff hpM] at e2
  generalize c ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = cM at *
  generalize (2 * Real.pi * Complex.I : ℂ) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = pM at *
  generalize Ω ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = W
  have h3 : T / (W * cM / pM) = T * pM * W⁻¹ * cM⁻¹ := by rw [div_div_eq_mul_div, div_eq_mul_inv, mul_inv]; ring
  have h4 : cM * cM⁻¹ = 1 := mul_inv_cancel₀ hcM
  rw [h3]
  linear_combination ((-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) * W⁻¹) * e2 -
    ((-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) * W⁻¹ *
      (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * T * pM) * h4

theorem latConj : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ →
    GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatConj := by
  intro hSK hPZ _ _
  have hW2 := GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ
  have hS := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hZ := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSK
  have hE := GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ
  intro K _ _ d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ _ hTT E _ _ _ _ I _ φ s 𝔣 Q hD κ κ' hκ y S S' hSS hSS'
  obtain ⟨hU, hφ, hφK, hs, hb, hQ⟩ := hD
  have hf : 2 ≤ Module.finrank ℚ (FR E) := GlobalTheory.LatConjOne.two_le_finrank_of_unramFin E hU
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  obtain ⟨-, -, hg, hL0, ⟨𝔞, hinv, hL1⟩, -⟩ := id hTT
  have hmod : nrm 𝔞 = modF t := GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf t 𝔞 hinv
  have h𝔞 : 𝔞 ≠ 0 := by
    rintro rfl
    have h1 : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := Λ₁.ω₁_mem_lattice
    rw [hL1] at h1
    obtain ⟨x, hx, hx'⟩ := h1
    have hx0 : x = 0 := (FractionalIdeal.mem_zero_iff _).1 hx
    have := Λ₁.indep.ne_zero 0
    simp [← hx', hx0] at this
  obtain ⟨c₀, θ₀, τ₀, hc₀, hθ₀, hT₀, hO⟩ := GlobalTheory.IdealTheta.main K d δ ι 1 Λ₀ hK2 hd hδ one_ne_zero hL0
  obtain ⟨c₁, θ₁, τ₁, hc₁, hθ₁, hT₁, ha⟩ := GlobalTheory.IdealTheta.main K d δ ι 𝔞 Λ₁ hK2 hd hδ h𝔞 hL1
  have hc1 : c₀ = 1 := by
    obtain ⟨a, b, hab⟩ := (hO 1).1 (FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 ((hO c₀).2 ⟨0, 1, by simp⟩)
    have hint : IsIntegral ℤ c₀ := by
      have h1 : IsIntegral ℤ (algebraMap ℚ K c₀) := by
        have := w.isIntegral_coe
        rw [hw] at this
        simpa using this
      exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h1
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hm' : (m : ℚ) = c₀ := by simpa using hm
    have h2 := indep ι θ₀ τ₀ hθ₀ (m * a) (m * b - 1) (by
      rw [← hm'] at hab; push_cast at hab ⊢; linear_combination -hab)
    have h3 : m = 1 := Int.eq_one_of_mul_eq_one_right (by rw [← hm'] at hc₀; exact_mod_cast hc₀.le) (by linarith [h2.2])
    rw [← hm', h3]; simp
  subst hc1
  simp only [Rat.cast_one, one_mul] at hT₀ hO
  have hcov := covol ι 𝔞 θ₀ θ₁ c₁ τ₀ τ₁ hc₁ hθ₀ hθ₁ hO ha
  have hδO : δ ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have hint : IsIntegral ℤ δ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hδ]
      exact (isIntegral_natCast d).neg
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨δ, hint⟩, rfl⟩
  obtain ⟨a₀, b₀, hab⟩ := (hO δ).1 hδO
  obtain ⟨q, hq⟩ := ratio_rat ι d hd δ θ₀ τ₀ hδ hθ₀ a₀ b₀ hab
  have hφι : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hφK]
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeEmb.exists_equiv E I φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := by
    rw [Fintype.card_congr e, ← NumberField.Embeddings.card (FR E) ℂ]
    refine Fintype.card_congr (Equiv.ofBijective (fun f => Complex.ofRealHom.comp f) ⟨fun f f' h => ?_, fun f => ?_⟩)
    · ext x
      have := congrArg (fun u : FR E →+* ℂ => u x) h
      simpa using this
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal f).embedding, by ext x; simp⟩
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hθF : algebraMap K E θ₀ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i⟩ := hI
    have h1 := he i x
    simp only at hx
    rw [hx, hφι, hθ₀] at h1
    have := congrArg Complex.im h1
    simp at this
    exact τ₀.im_pos.ne' this
  obtain ⟨n, N, L₀, hn, hN, h2N, hLev, hmem⟩ := GlobalTheory.RoadE.exists_level E (algebraMap K E θ₀) (condQ 𝔣 Q) y 2 hc hθF two_pos
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact (1 < N) := ⟨Nat.le_of_dvd hN h2N⟩
  obtain ⟨hω₀, hω₁, h4, h6, hG, hA⟩ := GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hTT 1 c₁ τ₀ τ₁ hT₀ hT₁ _ _ rfl rfl
  obtain ⟨A, hAt, hAw⟩ := hA N
  have hmem₁ := GlobalTheory.RoadE.ConjLat.twist_lattice K ι E (condQ 𝔣 Q) y t 𝔞 θ₀ (c₁ * θ₁) c₁ Λ₀ Λ₁ c₁ τ₀ τ₁ N A n L₀ hK2 hc hL0 hT₀ hθ₀ hinv hL1 hT₁
    (by simp [hθ₁]) (by simp) (by simpa using hAt) hn hLev hmem
  have hc₁E : (c₁ : E) ≠ 0 := by exact_mod_cast hc₁.ne'
  have hc₁C : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁.ne'
  let α : Eˣ := (Units.mk0 (c₁ : E) hc₁E)⁻¹
  have hα : (α : E) = (c₁ : E)⁻¹ := by simp [α]
  have hSt := (hS E I φ hf hφ).1 s hs
  set y₁ := y * (upIdele K E t)⁻¹ with hy₁
  have hlat : (fun x => (α : E) * x) '' lattice (condQ 𝔣 Q) y₁ =
      lattice (condQ 𝔣 Q) (Units.map (algebraMap E (Af E)).toMonoidHom α * y₁) := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mul_mem_lattice_princ _ _ α x).2 hx
    · intro hx
      refine ⟨(α⁻¹ : Eˣ) * x, (mul_mem_lattice_princ _ _ α _).1 ?_, ?_⟩ <;> simpa using hx
  have hH := ((hSt.1 (condQ 𝔣 Q) y₁ hc).2 κ' α S' hSS').1
  have hmem₂ : ∀ x : Fin 2 → FR E, x ∈ HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N)) ↔
      ∃ y' ∈ (fun x => (α : E) * x) '' lattice (condQ 𝔣 Q) y₁, (n : E) * y' = (x 0 : E) * algebraMap K E θ₁ + (x 1 : E) := by
    intro x
    rw [hmem₁]
    simp only [map_mul, map_ratCast, Set.mem_image, exists_exists_and_eq_and, hα]
    refine exists_congr fun w => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · field_simp
      linear_combination h
    · field_simp at h
      linear_combination h
  have hr0 : ∃ x : K, starRingEnd ℂ (ι x) ≠ ι x := ⟨θ₀, fun h => by
    rw [hθ₀, Complex.conj_eq_iff_im] at h
    exact τ₀.im_pos.ne' h⟩
  obtain ⟨π, hπ⟩ := GlobalTheory.LatConjOne.exists_perm ι φ g hφ hφK hg hr0
  have hπ' : ∀ i x, g (φ i x) = φ (π i) x := fun i x => by
    have := congrArg (fun h : E →+* ℂ => h x) (hπ i); simpa using this
  have hκπ : ∀ i, κ' (π i) = κ i := fun i => hκ i (π i) (hπ' i)
  have hsum : ∑ i, κ' i = ∑ i, κ i := (Fintype.sum_equiv π _ _ fun i => (hκπ i).symm).symm
  let σ : Emb (FR E) ≃ Emb (FR E) := e.symm.trans (π.trans e)
  have hσ : ∀ (j : Emb (FR E)) (x : FR E), g ((j x : ℝ) : ℂ) = ((σ j x : ℝ) : ℂ) := fun j x => by
    have h1 := he (e.symm j) x
    rw [e.apply_symm_apply] at h1
    rw [← h1, hπ', he]; rfl
  let v : Fin 2 → ZMod N := ![1, 0]
  have hv : v ≠ 0 := fun h => by
    have := congrFun h 0
    simp [v] at this
  have V0 := value_eq hE E I φ e (algebraMap K E θ₀) τ₀ _ L₀ n s N d κ (wB N v) S Ω₀ 1 _ hf hs hN hLev he
    (fun i => by rw [hφι, hθ₀]) hn hmem hcard (hSt.1 _ y hc).1 hSS one_ne_zero rfl
  have V1 := value_eq hE E I φ e (algebraMap K E θ₁) τ₁ _ (HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N))) n s N d κ'
    (wB N (vmul v A)) _ Ω₁ c₁ _ hf hs hN (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel _ N L₀ _ hLev) he
    (fun i => by rw [hφι, hθ₁]) hn hmem₂ hcard (by rw [hlat]; exact (hSt.1 _ _ hc).1) hH hc₁C rfl
  obtain ⟨a, haz⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  have T := sum_transport g σ (2 * s) (2 * s * Module.finrank ℚ (FR E)) (fun j => κ (e.symm j)) (fun j => κ' (e.symm j))
    (fun j => by simp [σ, hκπ])
    (((Real.pi / τ₀.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N v τ₀)
    (((Real.pi / τ₁.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N (vmul v A) τ₁) _ _
    (fun μ => hfun (2 * s) L₀ μ (wB N v) τ₀)
    (fun μ => hfun (2 * s) (HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (vmul v A)) τ₁)
    (by rw [GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity, GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity, neg_div, neg_div, add_div, add_div, map_neg, map_add, hG, (hAw v).1])
    (fun μ => by
      have h := GlobalTheory.T.transport_modularFamily_GL2ZMod_weierstrass g N N (wt (2 * s) μ) a A _
        (fun β => hfun (2 * s) (HilbFam.twist N L₀ ((β : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))
          (fun j => μ (σ.symm j)) (wB N (vmul v β))) τ₀ τ₁ _ _ hN dvd_rfl haz
        (GlobalTheory.T.hilbert_family_weierstrass_twist hE (FR E) hf s N L₀ hs hLev v μ)
        (fun β => GlobalTheory.T.galois_conj_qExpansion_family_diag_one_unit hE (FR E) hf s N L₀ hs hLev z hz g a μ _ v haz (fun i j hij => by
          have : j = σ i := by
            ext x
            have := (hij x).symm.trans (hσ i x)
            exact_mod_cast this
          simp [this]) hv β) hω₀ h4 h6 hAw 1
      have hv1 : vmul v 1 = v := by simp [vmul]
      simp only [Units.val_one, one_mul, hv1, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L₀ hLev] at h
      exact h)
  have hse : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
  rw [hse] at T
  rw [hsum] at V1
  have hlam : (lamInf φ (2 * s) κ' α)⁻¹ = (c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) := by
    have : ∀ i, (φ i α) ^ (2 * s + κ' i) * (starRingEnd ℂ (φ i α))⁻¹ ^ κ' i = ((c₁ : ℂ) ^ (2 * s))⁻¹ := fun i => by
      rw [hα, map_inv₀, map_ratCast, map_inv₀, map_ratCast, inv_inv, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hc₁C, one_pow,
        mul_one, inv_pow]
    rw [lamInf, Finset.prod_congr rfl fun i _ => this i, Finset.prod_const, Finset.card_univ, hcard, inv_pow, inv_inv, ← pow_mul]
  have hC0 : C0 E d (2 * s) κ = C0 E d (2 * s) κ' := by
    rw [cmValueConst_eq, cmValueConst_eq, hsum]
    congr 2
    exact Fintype.prod_equiv π _ _ fun i => by rw [hκπ]
  simp only [neg_zero, Complex.cpow_zero, mul_one, hlam] at V1
  have hmpos : (0 : ℝ) < modF t := by
    rw [← hmod]
    have h1 : 0 < nrm 𝔞 * τ₀.im := by
      rw [← hcov]
      have : (0 : ℝ) < c₁ := by exact_mod_cast hc₁
      have := τ₁.im_pos
      positivity
    exact (pos_iff_pos_of_mul_pos h1).2 τ₀.im_pos
  have hm0 : ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hmpos.ne')
  have hr : ((2 * τ₁.im / Real.sqrt d : ℝ) : ℂ) * (c₁ : ℂ) ^ 2 = ((modF t : ℝ) : ℂ) * q := by
    have : (2 * τ₁.im / Real.sqrt d : ℝ) * (c₁ : ℝ) ^ 2 = modF t * q := by
      rw [← hq, ← hmod]
      linear_combination (2 / Real.sqrt d) * hcov
    exact_mod_cast this
  have hr' := congrArg (fun x : ℂ => x ^ (∑ i, κ i)) hr
  simp only [mul_pow] at hr'
  rw [V0, hq]
  simp only [map_mul, map_pow, map_neg, map_one, one_pow, Complex.ofReal_ratCast, map_ratCast, map_natCast]
  rw [mul_one Ω₀] at T
  simp only [mul_one]
  rw [T]
  unfold coordIn at V1 ⊢
  rw [hC0]
  rw [hsum] at V1
  apply mul_left_cancel₀ (mul_ne_zero hm0 (pow_ne_zero (2 * s * Module.finrank ℚ (FR E)) hc₁C))
  generalize (∑ μ ∈ Finset.Iic (fun j ↦ κ' (e.symm j)), (_ : ℂ)) / _ = X at V1 ⊢
  rw [pow_add (c₁ : ℂ), pow_mul (c₁ : ℂ) 2 (∑ i, κ i)] at V1
  have hmi := mul_inv_cancel₀ hm0
  linear_combination -V1 - ((-1) ^ (∑ i, κ i) * (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) *
    (c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * X) * hr' -
    ((c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * (C0 E d (2 * s) κ' : ℂ) * S' 0 /
      Ω₁ ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)) * hmi

end GlobalTheory.LatConjEll
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueConjugation_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatConj := by
  atlas_forward_decl GlobalTheory.LatConjEll.latConj
end
