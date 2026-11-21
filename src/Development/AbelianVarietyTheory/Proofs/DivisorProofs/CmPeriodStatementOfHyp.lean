import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorialInvLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImaginaryGeneratorCmType
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIntegerInIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QexpansionOnAllComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStripsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertClassFieldLatticeTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodConstantEqOfCardCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordInEqOfJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionOfFunctionalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetAnalyticOfPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBaseChangeOfDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNatCastEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinRuleOfQExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetLiftOfDeformationDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicModelOfDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelOfDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOfAlgebraicModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFormStatementHolds

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_lattice_order_coprime_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime →
    ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
    ∃ n : ℕ, n.Coprime l ∧ (∀ x ∈ lattice c y, (n : E) * x ∈ orderC c) ∧ ∀ x ∈ orderC c, (n : E) * x ∈ lattice c y := by
  first | exact @GlobalTheory.CMVal.LatLoc.lattice_near_orderC | exact GlobalTheory.CMVal.LatLoc.lattice_near_orderC | (intros; apply GlobalTheory.CMVal.LatLoc.lattice_near_orderC <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_imaginary_generator_cm_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E), IsUnit M →
    (∀ ξ ∈ M, IsCMField.complexConj E ξ = -ξ) → ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ (e₀ : ℤˣ) (l : ℕ), l.Prime →
    ∃ ξ ∈ M, (∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im) ∧
      ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ := by
  first | exact @GlobalTheory.SignGen.exists_signed_generator | exact GlobalTheory.SignGen.exists_signed_generator | (intros; apply GlobalTheory.SignGen.exists_signed_generator <;> assumption)
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory.FGIndex

theorem relIndex_ne_zero_coprime {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ) (hl : l.Prime)
    (_hAB : A ≤ B) (hB : B.FG) (h : ∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) :
    A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  haveI : AddGroup.FG B := (AddGroup.fg_iff_addSubgroup_fg B).2 hB
  haveI : AddGroup.FG (B ⧸ A.addSubgroupOf B) :=
    AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  have hq : ∀ q : B ⧸ A.addSubgroupOf B, ∃ n : ℕ, n.Coprime l ∧ n • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨n, hn, hnA⟩ := h b b.2
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hnA
  haveI : Finite (B ⧸ A.addSubgroupOf B) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨n, hn, hnq⟩ := hq q
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, Nat.coprime_zero_left] at hn; exact absurd hn hl.one_lt.ne'
      · exact h0
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn0, hnq⟩
  have h0 : A.relIndex B ≠ 0 := by
    rw [AddSubgroup.relIndex, AddSubgroup.index]
    exact Nat.card_pos.ne'
  refine ⟨h0, ?_⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ A.addSubgroupOf B) l hd
  obtain ⟨n, hn, hnx⟩ := hq x
  have : l ∣ n := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hnx
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 (Nat.coprime_comm.1 hn) this

theorem main : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l :=
  fun A B l hl hAB hB h => relIndex_ne_zero_coprime A B l hl hAB hB h

end GlobalTheory.FGIndex
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_coprime_of_torsion : ∀ {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (l : ℕ), l.Prime → A ≤ B → B.FG →
    (∀ z ∈ B, ∃ n : ℕ, n.Coprime l ∧ n • z ∈ A) → A.relIndex B ≠ 0 ∧ (A.relIndex B).Coprime l := by
  atlas_forward_decl GlobalTheory.FGIndex.main
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory

theorem polMod_mul_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  intro E _ _ _ L ⟨N, hN, hL⟩ hu
  have hLfg : L.FG := by
    apply Submodule.FG.of_restrictScalars ℤ
    let f : E →ₗ[ℤ] E := LinearMap.mulLeft ℤ (N : E)
    have hf : Function.Injective f := mul_right_injective₀ (Nat.cast_ne_zero.2 hN.ne')
    let g : 𝓞 E →ₗ[ℤ] E := (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
    have hg : (LinearMap.range g).FG := by
      rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map _
    refine Submodule.fg_of_fg_map_injective f hf (hg.of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(N : E) * x, hL x hx⟩, rfl⟩
  have hMfg : (polMod L).FG := Submodule.fg_of_isUnit hu
  have hP : (polMod L * L).FG := hMfg.mul hLfg
  exact (Submodule.fg_iff_addSubgroup_fg ((polMod L * L).restrictScalars ℤ)).1 (hP.restrictScalars)

end GlobalTheory
end

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_lattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  atlas_forward_decl GlobalTheory.polMod_mul_fg
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discriminant_mul_trace_dual_integral : ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  first | exact @GlobalTheory.discr_mul_isIntegral_of_traceDual | exact GlobalTheory.discr_mul_isIntegral_of_traceDual | (intros; apply GlobalTheory.discr_mul_isIntegral_of_traceDual <;> assumption)
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_integer_in_ideal : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by
  first | exact @GlobalTheory.NormCoprime.exists_coprime_mem | exact GlobalTheory.NormCoprime.exists_coprime_mem | (intros; apply GlobalTheory.NormCoprime.exists_coprime_mem <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.PolarisationModuleProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gen_mul {L : Submodule (OF E) E} {l : ℕ} {ξ : E} (h : GenAt l (polMod L) ξ) :
    ∀ z ∈ polMod L * L, ∃ n : ℕ, n.Coprime l ∧ (n : E) * z ∈ mulLat ξ L := by
  intro z hz
  induction hz using Submodule.mul_induction_on' with
  | mem_mul_mem η hη x hx =>
    obtain ⟨n, hn, a, ha⟩ := h.2 η hη
    refine ⟨n, hn, Submodule.mem_map.2 ⟨a • x, L.smul_mem a hx, ?_⟩⟩
    rw [LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc, mul_comm ξ, ← ha]; ring
  | add z1 _ z2 _ h1 h2 =>
    obtain ⟨n1, hn1, h1⟩ := h1
    obtain ⟨n2, hn2, h2⟩ := h2
    refine ⟨n1 * n2, Nat.Coprime.mul hn1 hn2, ?_⟩
    have e : ((n1 * n2 : ℕ) : E) * (z1 + z2) = (n2 : OF E) • ((n1 : E) * z1) + (n1 : OF E) • ((n2 : E) * z2) := by
      rw [Algebra.smul_def, Algebra.smul_def]; push_cast; ring
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem trInt_of_isIntegral {x : E} (hx : IsIntegral ℤ x) : TrInt x := by
  have h := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn]; simp⟩

theorem isIntegral_of_mem_orderC {c : Ideal (OF E)} {x : E} (hx : x ∈ orderC c) : IsIntegral ℤ x := by
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  refine IsIntegral.add ?_ ?_
  · exact (algebraMap (OF E) (𝓞 E) a).2
  · exact b.2

theorem invertible_of_isUnit {M : Submodule (OF E) E} (hU : IsUnit M) : Module.Invertible (OF E) M := by
  have h : Module.Invertible (OF E) ↥(↑hU.unit : Submodule (OF E) E) := inferInstance
  rwa [hU.unit_spec] at h

theorem sandwich_latMod {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ latMod c y) ∧
      ∀ x ∈ latMod c y, IsIntegral ℤ ((N : E) * x) :=
  GlobalTheory.T.exists_denominator_of_adelic_lattice E c hc y

theorem modulePart {I : Type} (φ : I → E →+* ℂ) (hφ : IsCMType φ) (e₀ : ℤˣ) : ModulePart φ e₀ := by
  intro c hc y
  obtain ⟨N, hN, hO, hint⟩ := sandwich_latMod hc y
  obtain ⟨hU, hEq⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod c y) ⟨N, hN, hO, hint⟩
  have hanti : ∀ ξ ∈ polMod (latMod c y), IsCMField.complexConj E ξ = -ξ := fun ξ h => h.1
  have hFG : (dualLat (latMod c y)).toAddSubgroup.FG := hEq ▸ GlobalTheory.T.polarization_lattice_fg E (latMod c y) ⟨N, hN, hint⟩ hU
  refine ⟨invertible_of_isUnit hU, hEq, ?_, fun l hl => ⟨?_, fun ξ hξ hg => ?_⟩⟩
  · obtain ⟨ξ, hξ, hpos, -⟩ := GlobalTheory.T.exists_imaginary_generator_cm_type E (polMod (latMod c y)) hU hanti I φ hφ e₀ 2 Nat.prime_two
    exact ⟨ξ, hξ, hpos⟩
  · obtain ⟨ξ, hξ, hpos, hg⟩ := GlobalTheory.T.exists_imaginary_generator_cm_type E (polMod (latMod c y)) hU hanti I φ hφ e₀ l hl
    exact ⟨ξ, ⟨hξ, hpos⟩, hξ, hg⟩
  · have hle : mulLat ξ (latMod c y) ≤ dualLat (latMod c y) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      exact polMod_mul_le _ (Submodule.mul_mem_mul hg.1 hx)
    have h5 := GlobalTheory.T.relIndex_coprime_of_torsion (mulLat ξ (latMod c y)).toAddSubgroup (dualLat (latMod c y)).toAddSubgroup l hl hle hFG
      (fun z hz => by
        obtain ⟨n, hn, h⟩ := gen_mul hg z (hEq ▸ hz)
        exact ⟨n, hn, by rw [nsmul_eq_mul]; exact h⟩)
    exact ⟨hle, h5.1, h5.2⟩

theorem sizePart {I : Type} (φ : I → E →+* ℂ) (hφ : IsCMType φ) (e₀ : ℤˣ) : SizePart φ e₀ := by
  intro 𝔣 Q h𝔣 hQ l hl hQl y hy ξ hξ hg
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    have : (𝔣 * ∏ q ∈ Q, q.asIdeal) ≠ 0 :=
      mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
    exact this
  obtain ⟨n, hn, hLO, hOL⟩ := GlobalTheory.T.adelic_lattice_order_coprime_index E (condQ 𝔣 Q) hc l hl y hy
  obtain ⟨N, hN, hO, hint⟩ := sandwich_latMod hc y
  obtain ⟨hU, hEq⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod (condQ 𝔣 Q) y) ⟨N, hN, hO, hint⟩
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨i, -, -⟩ := hφ σ
    have := hξ.2 i
    simp at this
  have hn1 : (n : E) ∈ dualLat (latMod (condQ 𝔣 Q) y) := by
    intro x hx
    have h1 := isIntegral_of_mem_orderC (hLO x hx)
    apply trInt_of_isIntegral
    have : (n : E) * bar x = bar ((n : E) * x) := by simp [bar]
    rw [this]
    exact map_isIntegral_int (IsCMField.complexConj E) h1
  rw [← hEq] at hn1
  obtain ⟨n', hn', hm⟩ := gen_mul hg _ hn1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hm
  rw [LinearMap.mulLeft_apply] at hxe
  have hxi : IsIntegral ℤ ((n : E) * x) := isIntegral_of_mem_orderC (hLO x hx)
  have key : ((n' * n * n : ℕ) : E) * ξ⁻¹ = (n : E) * x := by
    have hx' : x = ((n' : E) * n) * ξ⁻¹ := by
      rw [← hxe, mul_comm ξ, mul_assoc, mul_inv_cancel₀ hξ0, mul_one]
    rw [hx']; push_cast; ring
  have hinv : ∀ σ : E →+* ℂ, IntAt l (σ ξ)⁻¹ := fun σ => ⟨n' * n * n,
    Nat.Coprime.mul (Nat.Coprime.mul hn' hn) hn, by
      rw [← map_inv₀, ← map_natCast σ, ← map_mul, key]; exact map_isIntegral_int σ hxi⟩
  refine ⟨hξ0, hinv, fun hdisc h𝔣l σ => ?_⟩
  have hcl : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → (l : OF E) ∉ v.asIdeal := by
    intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact h𝔣l v h
    · obtain ⟨q, hq, hvq⟩ := (Prime.dvd_finset_prod_iff v.prime _).1 h
      have : v.asIdeal = q.asIdeal :=
        ((q.isMaximal).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hvq)).symm
      rw [this]; exact hQl q hq
  obtain ⟨m, hm, hmc⟩ := GlobalTheory.T.exists_coprime_integer_in_ideal (maximalRealSubfield E) (condQ 𝔣 Q) l hl hc hcl
  have hmO : ∀ b : 𝓞 E, (m : E) * algebraMap (𝓞 E) E b ∈ orderC (condQ 𝔣 Q) := by
    intro b
    refine mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) m * b,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmc), ?_⟩
    simp
  have hξL : ∀ b : 𝓞 E, ((n : E) * m) * algebraMap (𝓞 E) E b ∈ latMod (condQ 𝔣 Q) y := by
    intro b
    have := hOL _ (hmO b)
    rwa [← mul_assoc] at this
  have htr : ∀ b : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E ((((n : E) * m) ^ 2 * ξ) * algebraMap (𝓞 E) E b) = k := by
    intro b
    obtain ⟨k, hk⟩ := hξ.1.2 _ (hξL b) _ (by simpa using hξL 1)
    refine ⟨k, ?_⟩
    rw [← hk]
    congr 1
    simp [bar]
    ring
  have h7 := GlobalTheory.T.discriminant_mul_trace_dual_integral E _ htr
  have h7' : IsIntegral ℤ (((discr E).natAbs : E) * (((n : E) * m) ^ 2 * ξ)) := by
    have hcast : ((discr E).natAbs : E) = (((discr E).natAbs : ℤ) : E) := (Int.cast_natCast _).symm
    rw [hcast, Int.natCast_natAbs]
    rcases abs_choice (discr E) with h | h <;> rw [h]
    · exact h7
    · push_cast; rw [neg_mul]; exact h7.neg
  refine ⟨(map_ne_zero σ).2 hξ0, ⟨(discr E).natAbs * (n * m) ^ 2, ?_, ?_⟩, hinv σ⟩
  · refine Nat.Coprime.mul ?_ (Nat.Coprime.pow_left 2 (Nat.Coprime.mul hn hm))
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 fun h => hdisc (Int.natCast_dvd.2 h))
  · have : (((discr E).natAbs * (n * m) ^ 2 : ℕ) : ℂ) * σ ξ = σ (((discr E).natAbs : E) * (((n : E) * m) ^ 2 * ξ)) := by
      rw [map_mul, map_mul, map_pow, map_mul]; simp only [map_natCast]; push_cast; ring
    rw [this]
    exact map_isIntegral_int σ h7'

theorem polarisationModule : PolarisationModule :=
  fun _ _ _ _ _ _ φ hφ e₀ => ⟨modulePart φ hφ e₀, sizePart φ hφ e₀⟩

end GlobalTheory.PolarisationModuleProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_module_statement : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule := by
  atlas_forward_decl GlobalTheory.PolarisationModuleProof.polarisationModule
end

section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.LatJet

theorem JetRing.repr_algebraMap {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (a : R) :
    J.b.repr (algebraMap R J.B a) = Finsupp.single ⟨0, by simp⟩ a := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

theorem jetCore_of (h1 : JetRingEx) (h2 : JetLift) (h3 : JetBC) (h4 : JetAnalytic) : JetCore := by
  obtain ⟨ε, hε⟩ := h4
  refine ⟨ε, ?_⟩
  intro E _ _ _ I _ 𝔠 hf R₀ s r hs R _ _ _ _ _ X₀ δ₀ N hN κ
  obtain ⟨J⟩ := h1 R I (∑ i, κ i)
  obtain ⟨Y⟩ := h2 (FR E) 𝔠 R I (∑ i, κ i) J X₀ δ₀ N hN
  letI : Algebra R₀ J.B := ((algebraMap R J.B).comp (algebraMap R₀ R)).toAlgebra
  let ν : Idx I (∑ i, κ i) := ⟨κ, Nat.le_succ _⟩
  refine ⟨J.b.repr (r.val J.B Y.X' trivial Y.δ') ν, ?_⟩
  intro σ hσ φ c y m hφ hc hr T hT g u hg hu
  obtain ⟨J'⟩ := h1 ℂ I (∑ i, κ i)
  obtain ⟨Y', τ, q, hτ, hq, hd⟩ := h3 E I 𝔠 φ (lattice c y) R σ _ J J' X₀ δ₀ N Y T hT
  letI : Algebra R₀ J'.B := ((algebraMap ℂ J'.B).comp R₀.subtype).toAlgebra
  have hcomm : ∀ a : R₀, τ (algebraMap R₀ J.B a) = algebraMap R₀ J'.B a := by
    intro a
    apply J'.b.repr.injective
    ext μ
    rw [hτ]
    change σ (J.b.repr (algebraMap R J.B (algebraMap R₀ R a)) μ) = J'.b.repr (algebraMap ℂ J'.B (a : ℂ)) μ
    rw [J.repr_algebraMap, J'.repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp [hσ]
  have hbc := r.baseChange J.B J'.B ⟨τ, hcomm⟩ Y.X' trivial Y'.X' trivial q Y.δ' Y'.δ' hq hd
  have key := hε E I 𝔠 φ c y hf hφ hc R₀ s r m hs hr T _ J' Y' (fun _ => rfl) g ν u hg hu
  rw [hbc] at key
  rw [← key]
  exact congrArg (T.C ^ (2 * s) * ·) (hτ _ ν).symm

end GlobalTheory.LatJet
end
end

section
set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors
open NumberField Complex GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.RealMult GlobalTheory.LatJet

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

def pairAct (a b c d : F) (p : F × F) : F × F := (p.2 * b + p.1 * d, p.2 * a + p.1 * c)

def pairInv (a b c d : F) (q : F × F) : F × F := (q.1 * a - q.2 * b, q.2 * d - q.1 * c)

theorem pairInv_act (a b c d : F) (h : a * d - b * c = 1) (p : F × F) :
    pairInv a b c d (pairAct a b c d p) = p := by
  ext
  · simp only [pairInv, pairAct]; linear_combination p.1 * h
  · simp only [pairInv, pairAct]; linear_combination p.2 * h

theorem pairAct_inv (a b c d : F) (h : a * d - b * c = 1) (q : F × F) :
    pairAct a b c d (pairInv a b c d q) = q := by
  ext
  · simp only [pairInv, pairAct]; linear_combination q.1 * h
  · simp only [pairInv, pairAct]; linear_combination q.2 * h

theorem int_of_mul_mem (I : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) (x : F) (h : ∀ y ∈ I, x * y ∈ I) :
    ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x := by
  have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ x * I ≤ I := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact (I : Submodule (𝓞 F) F).smul_mem r (h j hj)
  have h2 := mul_le_mul_left h1 I⁻¹
  simp only [mul_assoc, mul_inv_cancel₀ hI, mul_one] at h2
  have h3 : x ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := h2 (FractionalIdeal.mem_spanSingleton_self _ x)
  exact (FractionalIdeal.mem_one_iff _).1 h3

theorem mul_mem_of_int (I : FractionalIdeal (𝓞 F)⁰ F) {x y : F} (hx : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x)
    (hy : y ∈ I) : x * y ∈ I := by
  obtain ⟨r, rfl⟩ := hx
  rw [← Algebra.smul_def]
  exact (I : Submodule (𝓞 F) F).smul_mem r hy

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

theorem mem_dual_iff_latM (𝔞 : Frac F) (x : F) : x ∈ dualLat 𝔞 ↔ x ∈ latM 𝔞 := by
  rw [latM_eq_dual]; rfl

theorem dualLat_ne_zero (𝔞 : Frac F) : dualLat 𝔞 ≠ 0 := by
  rw [dualLat, ← latM_eq_dual, latM]
  refine mul_ne_zero (inv_ne_zero ?_) (Units.ne_zero _)
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

variable {𝔞 𝔟 : Frac F} {a b c d : F}

theorem a_int (h : InModularGroup 𝔞 𝔟 a b c d) : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a :=
  int_of_mul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (Units.ne_zero _) a fun y hy ↦ by
    have := (h.2 y hy 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).1
    simpa [mul_comm] using this

theorem d_int (h : InModularGroup 𝔞 𝔟 a b c d) : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = d :=
  int_of_mul_mem (dualLat 𝔞) (dualLat_ne_zero 𝔞) d fun y hy ↦ by
    have := (h.2 0 (zero_mem _) y hy).2
    simpa [mul_comm] using this

def latEquiv (h : InModularGroup 𝔞 𝔟 a b c d) : LatPair 𝔞 𝔟 ≃ LatPair 𝔞 𝔟 where
  toFun p := ⟨pairAct a b c d p.1, by
    obtain ⟨h1, h2⟩ := h.2 p.1.2 p.2.2.1 p.1.1 ((mem_dual_iff_latM 𝔞 _).2 p.2.1)
    refine ⟨(mem_dual_iff_latM 𝔞 _).1 h2, h1, fun h0 ↦ p.2.2.2 ?_⟩
    rw [← pairInv_act a b c d h.1 p.1, h0]; simp [pairInv]⟩
  invFun q := ⟨pairInv a b c d q.1, by
    have hm := (mem_dual_iff_latM 𝔞 _).2 q.2.1
    have hb := q.2.2.1
    refine ⟨(mem_dual_iff_latM 𝔞 _).1 ?_, ?_, fun h0 ↦ q.2.2.2 ?_⟩
    · refine (dualLat 𝔞 : Submodule (𝓞 F) F).sub_mem (mul_comm a q.1.1 ▸ mul_mem_of_int _ (a_int h) hm) ?_
      simpa using (h.2 q.1.2 hb 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).2
    · refine (𝔟 : Submodule (𝓞 F) F).sub_mem (mul_comm d q.1.2 ▸ mul_mem_of_int (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (d_int h) hb) ?_
      simpa using (h.2 0 (zero_mem _) q.1.1 hm).1
    · rw [← pairAct_inv a b c d h.1 q.1, h0]; simp [pairAct]⟩
  left_inv p := Subtype.ext (pairInv_act a b c d h.1 p.1)
  right_inv q := Subtype.ext (pairAct_inv a b c d h.1 q.1)

theorem latEquiv_apply (h : InModularGroup 𝔞 𝔟 a b c d) (p : LatPair 𝔞 𝔟) :
    (latEquiv h p).1 = pairAct a b c d p.1 := rfl

def clsEquiv (h : InModularGroup 𝔞 𝔟 a b c d) : Quotient (latRel 𝔞 𝔟) ≃ Quotient (latRel 𝔞 𝔟) :=
  Quotient.congr (latEquiv h) fun p q ↦ by
    show (∃ ε : (𝓞 F)ˣ, _) ↔ (∃ ε : (𝓞 F)ˣ, _)
    simp only [latEquiv_apply, pairAct]
    constructor
    · rintro ⟨ε, h1, h2⟩
      exact ⟨ε, by rw [h1, h2]; ring, by rw [h1, h2]; ring⟩
    · rintro ⟨ε, h1, h2⟩
      have hd := h.1
      exact ⟨ε, by linear_combination a * h1 - b * h2 + (((ε : 𝓞 F) : F) * p.1.1 - q.1.1) * hd,
        by linear_combination d * h2 - c * h1 + (((ε : 𝓞 F) : F) * p.1.2 - q.1.2) * hd⟩

theorem clsEquiv_mk (h : InModularGroup 𝔞 𝔟 a b c d) (p : LatPair 𝔞 𝔟) :
    clsEquiv h (Quotient.mk _ p) = Quotient.mk _ (latEquiv h p) := rfl

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

def moeb (a b c d : F) (z : Emb F → ℂ) : Emb F → ℂ :=
  fun τ ↦ ((τ a : ℂ) * z τ + (τ b : ℂ)) / ((τ c : ℂ) * z τ + (τ d : ℂ))

def den (c d : F) (z : Emb F → ℂ) (τ : Emb F) : ℂ := (τ c : ℂ) * z τ + (τ d : ℂ)

theorem det_emb {a b c d : F} (h : a * d - b * c = 1) (τ : Emb F) : τ a * τ d - τ b * τ c = 1 := by
  rw [← map_mul, ← map_mul, ← map_sub, h, map_one]

theorem den_ne {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) (τ : Emb F) :
    den c d z τ ≠ 0 := by
  intro h0
  have him : τ c * (z τ).im = 0 := by
    have := congrArg Complex.im h0
    simpa [den] using this
  have hc : τ c = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact h1
    · exact absurd h1 (hz τ).ne'
  have hc' : c = 0 := (map_eq_zero τ).1 hc
  have hd : (τ d : ℂ) = 0 := by simpa [den, hc] using h0
  have hd' : d = 0 := (map_eq_zero τ).1 (by exact_mod_cast hd)
  rw [hc', hd'] at h
  simp at h

theorem moeb_mem {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) :
    moeb a b c d z ∈ halfSpace F := by
  intro τ
  have hn := Complex.normSq_pos.2 (den_ne h hz τ)
  have hdet := det_emb h τ
  simp only [den] at hn
  simp only [moeb, Complex.div_im]
  rw [← sub_div]
  refine div_pos ?_ hn
  have : ((τ a : ℂ) * z τ + (τ b : ℂ)).im * ((τ c : ℂ) * z τ + (τ d : ℂ)).re -
      ((τ a : ℂ) * z τ + (τ b : ℂ)).re * ((τ c : ℂ) * z τ + (τ d : ℂ)).im =
      (z τ).im * (τ a * τ d - τ b * τ c) := by
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this, hdet, mul_one]
  exact hz τ

theorem latPt_moeb {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) (p : F × F)
    (τ : Emb F) : latPt (moeb a b c d z) p τ = latPt z (pairAct a b c d p) τ / den c d z τ := by
  have hne := den_ne h hz τ
  simp only [den] at hne
  have hne' : z τ * (τ c : ℂ) + (τ d : ℂ) ≠ 0 := by rw [mul_comm]; exact hne
  simp only [latPt, moeb, pairAct, den, map_add, map_mul, Complex.ofReal_add, Complex.ofReal_mul]
  rw [eq_div_iff hne]
  field_simp
  ring

theorem eisTerm_moeb {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) (k : ℕ)
    (σ : ℂ) (p : F × F) :
    eisTerm k σ (moeb a b c d z) p =
      (∏ τ, den c d z τ) ^ k * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * eisTerm k σ z (pairAct a b c d p) := by
  have hprod : ∏ τ, latPt (moeb a b c d z) p τ = (∏ τ, latPt z (pairAct a b c d p) τ) / ∏ τ, den c d z τ := by
    simp_rw [latPt_moeb h hz p]
    rw [Finset.prod_div_distrib]
  unfold eisTerm
  rw [hprod]
  generalize ∏ τ, latPt z (pairAct a b c d p) τ = P
  generalize ∏ τ, den c d z τ = Q
  have harg : ((‖Q‖ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (norm_nonneg _)]; exact Real.pi_pos.ne
  have hQ : (((‖Q‖⁻¹ : ℝ)) : ℂ) ^ (-2 * σ) = ((‖Q‖ : ℝ) : ℂ) ^ (2 * σ) := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, neg_mul, neg_neg]
  have hN : ((‖P / Q‖ : ℝ) : ℂ) ^ (-2 * σ) = ((‖P‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖Q‖ : ℝ) : ℂ) ^ (2 * σ) := by
    rw [norm_div, div_eq_mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _)), hQ]
  rw [hN, inv_div, div_eq_mul_inv, mul_pow]
  ring

theorem eisClass_moeb [IsTotallyReal F] {𝔞 𝔟 : Frac F} {a b c d : F} (h : InModularGroup 𝔞 𝔟 a b c d)
    {z : Emb F → ℂ} (hz : z ∈ halfSpace F) {k : ℕ} (hk : Even k) (σ : ℂ) (x : Quotient (latRel 𝔞 𝔟)) :
    eisClass 𝔞 𝔟 k σ (moeb a b c d z) x =
      (∏ τ, den c d z τ) ^ k * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * eisClass 𝔞 𝔟 k σ z (clsEquiv h x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [clsEquiv_mk, eisClass_mk _ _ hk, eisClass_mk _ _ hk, latEquiv_apply]
    exact eisTerm_moeb h.1 hz k σ p.1

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

theorem eisMod : EisMod := by
  intro F _ _ _ 𝔞 𝔟 s hs G hG hdiff
  refine ⟨hdiff, ?_⟩
  intro a b c d hγ z hz
  have hw := moeb_mem hγ.1 hz
  have hQ : (∏ τ, den c d z τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ ↦ den_ne hγ.1 hz τ
  change G (moeb a b c d z) = (∏ τ, den c d z τ) ^ (2 * s) * G z
  have hk : Even (2 * s) := even_two_mul s
  by_cases h2 : 2 * s = 2
  · obtain ⟨H, hH, rfl⟩ := hG.2 h2
    rw [h2]
    set K : ℂ → ℂ := fun σ ↦
      (∏ τ, den c d z τ) ^ 2 * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * H σ z with hK
    have heq : ∀ σ : ℂ, 0 < σ.re → H σ (moeb a b c d z) = K σ := by
      intro σ hσ
      rw [(hH.1 σ hσ _ hw).2, hK]
      simp only
      rw [(hH.1 σ hσ z hz).2, eisSum, eisSum]
      simp_rw [eisClass_moeb hγ hz even_two σ]
      rw [tsum_mul_left, Equiv.tsum_eq]
    have hU : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
    have hf : AnalyticOnNhd ℂ (fun σ ↦ H σ (moeb a b c d z)) halfPlane :=
      (hH.2.2 [] _ hw).analyticOnNhd hU
    have hnQ : ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hQ
    have hg : AnalyticOnNhd ℂ K halfPlane := by
      refine DifferentiableOn.analyticOnNhd ?_ hU
      refine DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const _) ?_) (hH.2.2 [] z hz)
      exact (Differentiable.const_cpow (differentiable_id.const_mul 2) (Or.inl hnQ)).differentiableOn
    have hpc : IsPreconnected halfPlane := (convex_halfSpace_re_gt _).isPreconnected
    have h1 : (1 : ℂ) ∈ halfPlane := by show -1 / 2 < (1 : ℂ).re; norm_num
    have hev : (fun σ ↦ H σ (moeb a b c d z)) =ᶠ[nhds 1] K := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with σ hσ using heq σ hσ
    have := hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h1 hev
      (show (0 : ℂ) ∈ halfPlane by show -1 / 2 < (0 : ℂ).re; norm_num)
    refine this.trans ?_
    simp [hK]
  · have h1 := hG.1 h2 _ hw
    have h0 := hG.1 h2 z hz
    have h3 : HasSum (fun x ↦ (∏ τ, den c d z τ) ^ (2 * s) * eisClass 𝔞 𝔟 (2 * s) 0 z (clsEquiv hγ x))
        ((∏ τ, den c d z τ) ^ (2 * s) * G z) :=
      (Equiv.hasSum_iff (clsEquiv hγ) (f := fun x ↦ (∏ τ, den c d z τ) ^ (2 * s) * eisClass 𝔞 𝔟 (2 * s) 0 z x)).2
        (h0.mul_left _)
    refine h1.unique ?_
    convert h3 using 1
    funext x
    rw [eisClass_moeb hγ hz hk]
    simp

end GlobalTheory.EisModular
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD)

namespace GlobalTheory.JetIntegral

section Size

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [e, map_mul, norm_mul, Real.rpow_add l_pos]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg l_pos.le _)

theorem sz_one : Sz l lam 0 (1 : ℂ) := by
  refine ⟨one_mem _, ?_⟩
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]

theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam ((n : ℝ) * r) (x ^ n) := by
  induction n with
  | zero => simpa using (sz_one (lam := lam))
  | succ n ih =>
    have h := sz_mul ih hx
    rw [pow_succ]
    convert h using 1
    push_cast; ring

theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (sz_one (lam := lam))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sz_inv_l_pow (n : ℕ) : Sz l lam (n : ℝ) (((l : ℂ) ^ n)⁻¹) := by
  have hmem : ((l : ℂ) ^ n)⁻¹ ∈ algebraicClosure ℚ ℂ :=
    inv_mem (pow_mem (natCast_mem _ l) n)
  refine ⟨hmem, ?_⟩
  have e : (⟨((l : ℂ) ^ n)⁻¹, hmem⟩ : algebraicClosure ℚ ℂ) = ((l : algebraicClosure ℚ ℂ) ^ n)⁻¹ := by
    apply Subtype.ext; simp
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  rw [e, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, hl, inv_pow, inv_inv, Real.rpow_natCast]

theorem sz_sign (ε : ℤˣ) : Sz l lam 0 (((ε : ℤ) : ℂ)⁻¹) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using (sz_one (lam := lam))
  · have hmem : (-1 : ℂ) ∈ algebraicClosure ℚ ℂ := neg_mem (one_mem _)
    have e : (⟨-1, hmem⟩ : algebraicClosure ℚ ℂ) = -1 := rfl
    refine ⟨by simpa using hmem, ?_⟩
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, inv_neg, inv_one]
    rw [e, map_neg, map_one, norm_neg, norm_one, Real.rpow_zero]

end Size

theorem expand_id {I : Type} [Fintype I] (D x m C e : ℂ) (a b A : I → ℂ) (κ : I → ℕ) (k : ℕ)
    (hm : m ≠ 0) (he : e ≠ 0) (ha : ∀ i, a i ≠ 0) (hA : ∀ i, A i ≠ 0)
    (h : C ^ k * x = m * D * ∏ i, (e * A i) ^ κ i) :
    D * ∏ i, ((b i / a i) ^ κ i / a i ^ k) = x * m⁻¹ * (C / ∏ i, a i) ^ k * ∏ i, (e⁻¹ * (b i / (a i * A i))) ^ κ i := by
  have h3 : ∏ i, (e⁻¹ * (b i / (a i * A i))) ^ κ i = (∏ i, (b i / a i) ^ κ i) / ∏ i, (e * A i) ^ κ i := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← div_pow]
    congr 1
    field_simp [ha i, hA i, he]
  have h1 : ∏ i, ((b i / a i) ^ κ i / a i ^ k) = (∏ i, (b i / a i) ^ κ i) / ∏ i, a i ^ k := by
    rw [Finset.prod_div_distrib]
  have h2 : (C / ∏ i, a i) ^ k = C ^ k / ∏ i, a i ^ k := by rw [div_pow, Finset.prod_pow]
  have hP2 : ∏ i, a i ^ k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ha i)
  have hP3 : ∏ i, (e * A i) ^ κ i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero he (hA i))
  rw [h1, h2, h3]
  generalize ∏ i, (b i / a i) ^ κ i = P1 at *
  generalize ∏ i, a i ^ k = P2 at *
  generalize ∏ i, (e * A i) ^ κ i = P3 at *
  field_simp
  linear_combination (-P1) * h

end GlobalTheory.JetIntegral

namespace GlobalTheory.JetIntegral

theorem padicVal_nonneg {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (z : ClassGroup (OF E) → ℚ)
    (C : ClassGroup (OF E)) :
    0 ≤ padicValRat l ((l : ℚ) ^ cE_vp l z * (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))) := by
  have hl : (l : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  by_cases hq : z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E) = 0
  · rw [hq, mul_zero, padicValRat.zero]
  rw [padicValRat.mul (pow_ne_zero _ hl) hq, padicValRat.pow, padicValRat.self (Fact.out : l.Prime).one_lt, mul_one]
  have h1 : (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat ≤ cE_vp l z :=
    Finset.le_sup (f := fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat)
      (Finset.mem_univ C)
  have h2 := Int.self_le_toNat (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)))
  have h3 : ((-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat : ℤ) ≤ (cE_vp l z : ℤ) := by
    exact_mod_cast h1
  omega

theorem jetInt : EisRule → JetCore → ModelInt → JetInt := by
  intro hEis hJet hMod
  intro E _ _ _ _ I _ d φ s hFD hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ lam Ω hΩ
  classical
  obtain ⟨𝔠, R, hloc, X₀, δ₀, N, T, a, b, hR0, hRq, hAdm, hOver, hab, hC⟩ :=
    hMod E I d φ s hFD hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, fun i => ⟨(hab i).1, (hab i).2.1, (hab i).2.2.2.1, (hab i).2.2.2.2.1⟩, ?_⟩
  intro g κ u hg hu
  obtain ⟨-, -, hUn, -, -, -, hCM, -⟩ := hFD
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  set m : ℂ := (l : ℂ) ^ cE_vp l z with hmdef
  have hm0 : m ≠ 0 := pow_ne_zero _ hl0
  have hmR : m ∈ R := by
    have h := hRq ((l : ℚ) ^ cE_vp l z) (by
      rw [padicValRat.pow, padicValRat.self hl.one_lt]; positivity)
    simpa [hmdef] using h
  have hmz : ∀ C, m * ((z C / 2 ^ Module.finrank ℚ (FR E) : ℚ) : ℂ) ∈ R := by
    intro C
    have h := hRq _ (padicVal_nonneg l z C)
    convert h using 1
    push_cast [hmdef]
    ring
  obtain ⟨r, hr⟩ := hEis E hf2 𝔠 s hs z hz R m hmR hmz
  obtain ⟨ε, hε⟩ := hJet
  obtain ⟨x, hx⟩ := hε E I 𝔠 hf2 R s r hs R X₀ δ₀ N hAdm κ
  have hxe := hx R.subtype (fun a => rfl) φ (condQ 𝔣 Q) y m hCM hc0 (hr I φ (condQ 𝔣 Q) y hCM hc0) T hOver g u hg hu
  have hε0 : ((ε : ℤ) : ℂ) ≠ 0 := by exact_mod_cast ε.ne_zero
  rw [expand_id (iterD u g 0) (R.subtype x) m T.C ((ε : ℤ) : ℂ) a b T.A κ (2 * s) hm0 hε0 (fun i => (hab i).1)
    (fun i => (hab i).2.2.1) hxe]
  have hx0 : Sz l lam 0 (R.subtype x) := hR0 _ x.2
  have hmi : Sz l lam (cE_vp l z : ℝ) m⁻¹ := sz_inv_l_pow _
  have hCp := sz_pow hC (2 * s)
  have hP := sz_prod Finset.univ (fun i => (κ i : ℝ) * (0 + c_vp 𝔣 l)) _
    (fun i _ => sz_pow (sz_mul (sz_sign ε) (hab i).2.2.2.2.2) (κ i))
  have htot := sz_mul (sz_mul (sz_mul hx0 hmi) hCp) hP
  convert htot using 1
  push_cast
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.JetIntegral
end
end

section
set_option autoImplicit false

noncomputable section

open MvPolynomial Finset GlobalTheory.Cris GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

abbrev K : Type := FractionRing R

theorem charZero_K : CharZero (K R) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective R (K R))

attribute [local instance] charZero_K

variable {R I} in

def filt (k : ℕ) : Ideal (MvPolynomial I (K R)) where
  carrier := {p | ∀ μ : I →₀ ℕ, ∑ i, μ i < k → p.coeff μ = 0}
  zero_mem' := by intro μ _; simp
  add_mem' := by
    intro p q hp hq μ hμ
    simp [coeff_add, hp μ hμ, hq μ hμ]
  smul_mem' := by
    intro c p hp μ hμ
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have : ∑ i, x.2 i ≤ ∑ i, μ i := by
      rw [← hx]; simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]; omega
    rw [hp x.2 (lt_of_le_of_lt this hμ), mul_zero]

theorem filt_mul {a b : ℕ} {p q : MvPolynomial I (K R)} (hp : p ∈ filt a) (hq : q ∈ filt b) :
    p * q ∈ filt (a + b) := by
  intro μ hμ
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hs : ∑ i, x.1 i + ∑ i, x.2 i = ∑ i, μ i := by
    rw [← hx]; simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  by_cases h1 : ∑ i, x.1 i < a
  · rw [hp x.1 h1, zero_mul]
  · rw [hq x.2 (by omega), mul_zero]

theorem filt_pow (k : ℕ) : (filt (R := R) (I := I) 1) ^ k ≤ filt k := by
  induction k with
  | zero => intro p _ μ hμ; omega
  | succ k ih =>
    rw [pow_succ, Ideal.mul_le]
    intro p hp q hq
    exact filt_mul R I (ih hp) hq

abbrev C : Type := MvPolynomial I (K R) ⧸ (filt (R := R) (I := I) (n + 2))

def m : Ideal (C R I n) := (filt 1).map (Ideal.Quotient.mk _)

theorem m_pow : m R I n ^ (n + 2) = ⊥ := by
  rw [m, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact filt_pow R I _

def δ : DividedPowers (m R I n) := DividedPowers.RatAlgebra.dividedPowers _

def x (i : I) : C R I n := Ideal.Quotient.mk _ (X i)

theorem x_mem (i : I) : x R I n i ∈ m R I n := by
  refine Ideal.mem_map_of_mem _ ?_
  intro μ hμ
  have : μ ≠ Finsupp.single i 1 := by
    rintro rfl; simp at hμ
  rw [coeff_X']; simp [Ne.symm this]

def E (ν : I → ℕ) : C R I n := ∏ i, (δ R I n).dpow (ν i) (x R I n i)

theorem dpow_mem_pow (k : ℕ) {z : C R I n} (hz : z ∈ m R I n) : (δ R I n).dpow k z ∈ m R I n ^ k := by
  simp only [δ, DividedPowers.RatAlgebra.dpow_apply, if_pos hz]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hz k)

theorem E_big (ν : I → ℕ) (h : n + 2 ≤ ∑ i, ν i) : E R I n ν = 0 := by
  have h1 : E R I n ν ∈ m R I n ^ (∑ i, ν i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => dpow_mem_pow R I n _ (x_mem R I n i)
  have h2 := Ideal.pow_le_pow_right h h1
  rw [m_pow] at h2
  exact (Ideal.mem_bot).1 h2

theorem E_mul (ν ν' : I → ℕ) : E R I n ν * E R I n ν' =
    (∏ i, (ν i + ν' i).choose (ν i) : ℕ) • E R I n (ν + ν') := by
  rw [E, E, E, ← Finset.prod_mul_distrib, nsmul_eq_mul, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(δ R I n).mul_dpow (x_mem R I n i)]; rfl

theorem E_zero : E R I n 0 = 1 := by
  simp [E, (δ R I n).dpow_zero (x_mem R I n _)]

end GlobalTheory.DivPowTrunc

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

attribute [local instance] charZero_K

theorem mk_C (c : K R) : Ideal.Quotient.mk (filt (R := R) (I := I) (n + 2)) (MvPolynomial.C c) = algebraMap (K R) (C R I n) c := by
  rw [← MvPolynomial.algebraMap_eq]; exact Ideal.Quotient.mk_algebraMap _ _ _

theorem E_eq (ν : I → ℕ) : E R I n ν = Ideal.Quotient.mk _
    (monomial (Finsupp.equivFunOnFinite.symm ν) (∏ i, ((ν i).factorial : K R))⁻¹) := by
  have h1 : (∏ i, ((ν i).factorial : C R I n)) * E R I n ν =
      Ideal.Quotient.mk _ (monomial (Finsupp.equivFunOnFinite.symm ν) (1 : K R)) := by
    rw [E, ← Finset.prod_mul_distrib]
    simp_rw [(δ R I n).factorial_mul_dpow_eq_pow (x_mem R I n _), x, ← map_pow, ← map_prod]
    congr 1
    rw [← prod_X_pow_eq_monomial]
    symm
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [Finsupp.mem_support_iff, not_not] at hi
    rw [hi, pow_zero]
  have h2 : (∏ i, ((ν i).factorial : C R I n)) = algebraMap (K R) (C R I n) (∏ i, ((ν i).factorial : K R)) := by
    simp [map_prod, map_natCast]
  have hne : (∏ i, ((ν i).factorial : K R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [show monomial (Finsupp.equivFunOnFinite.symm ν) (∏ i, ((ν i).factorial : K R))⁻¹ =
      MvPolynomial.C (∏ i, ((ν i).factorial : K R))⁻¹ * monomial (Finsupp.equivFunOnFinite.symm ν) 1 by
    rw [C_mul_monomial, mul_one], map_mul, ← h1, h2, ← mul_assoc, mk_C, ← map_mul, inv_mul_cancel₀ hne, map_one,
    one_mul]

def Eidx (ν : Idx I n) : C R I n := E R I n ν.1

def S : Submodule R (C R I n) := Submodule.span R (Set.range (Eidx R I n))

theorem E_mem_S (μ : I → ℕ) : E R I n μ ∈ S R I n := by
  by_cases h : ∑ i, μ i ≤ n + 1
  · exact Submodule.subset_span ⟨⟨μ, h⟩, rfl⟩
  · rw [E_big R I n μ (by omega)]; exact Submodule.zero_mem _

theorem S_mul {a b : C R I n} (ha : a ∈ S R I n) (hb : b ∈ S R I n) : a * b ∈ S R I n := by
  have : S R I n * S R I n ≤ S R I n := by
    rw [S, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨a, ⟨ν, rfl⟩, b, ⟨ν', rfl⟩, rfl⟩
    dsimp only
    rw [Eidx, Eidx, E_mul]
    exact nsmul_mem (E_mem_S R I n _) _
  exact this (Submodule.mul_mem_mul ha hb)

def B : Subalgebra R (C R I n) :=
  (S R I n).toSubalgebra (by rw [← E_zero R I n]; exact E_mem_S R I n _) fun _ _ ha hb => S_mul R I n ha hb

theorem linIndep : LinearIndependent R (Eidx R I n) := by
  rw [linearIndependent_iff']
  intro s g hg ν hν
  have h3 : ∑ μ ∈ s, g μ • Eidx R I n μ = Ideal.Quotient.mk _ (∑ μ ∈ s,
      monomial (Finsupp.equivFunOnFinite.symm μ.1) (algebraMap R (K R) (g μ) * (∏ i, ((μ.1 i).factorial : K R))⁻¹)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Eidx, E_eq, Algebra.smul_def, IsScalarTower.algebraMap_apply R (K R) (C R I n), ← mk_C, ← map_mul,
      C_mul_monomial]
  rw [h3, Ideal.Quotient.eq_zero_iff_mem] at hg
  have := hg (Finsupp.equivFunOnFinite.symm ν.1) (by have := ν.2; simp; omega)
  rw [coeff_sum, Finset.sum_eq_single ν] at this
  · rw [coeff_monomial, if_pos rfl] at this
    have hne : (∏ i, ((ν.1 i).factorial : K R))⁻¹ ≠ 0 :=
      inv_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    have h4 : algebraMap R (K R) (g ν) = 0 := (mul_eq_zero.1 this).resolve_right hne
    exact IsFractionRing.injective R (K R) (by rw [h4, map_zero])
  · intro μ _ hμ
    rw [coeff_monomial, if_neg]
    intro h
    exact hμ (Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h))
  · intro h; exact absurd hν h

def v (ν : Idx I n) : B R I n := ⟨Eidx R I n ν, Submodule.subset_span ⟨ν, rfl⟩⟩

theorem span_v : ⊤ ≤ Submodule.span R (Set.range (v R I n)) := by
  rintro ⟨z, hz⟩ -
  change z ∈ S R I n at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ν, rfl⟩ := hy
    exact Submodule.subset_span ⟨ν, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a c ha hc iha ihc => exact Submodule.add_mem _ iha ihc
  | smul r a ha iha => exact Submodule.smul_mem _ r iha

def b : Module.Basis (Idx I n) R (B R I n) :=
  Module.Basis.mk (v := v R I n) (LinearIndependent.of_comp (B R I n).val.toLinearMap (linIndep R I n)) (span_v R I n)

theorem b_apply (ν : Idx I n) : ((b R I n ν : B R I n) : C R I n) = E R I n ν.1 := by
  simp [b, v, Eidx]

end GlobalTheory.DivPowTrunc

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

attribute [local instance] charZero_K

theorem cc (p : MvPolynomial I (K R)) : constantCoeff p = coeff 0 p := congrFun constantCoeff_eq p

def εC : C R I n →+* K R :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff fun a ha => by
    rw [cc]; exact ha 0 (by simp)

theorem εC_mk (p : MvPolynomial I (K R)) : εC R I n (Ideal.Quotient.mk _ p) = constantCoeff p :=
  Ideal.Quotient.lift_mk _ _ _

theorem εC_alg (c : K R) : εC R I n (algebraMap (K R) (C R I n) c) = c := by
  rw [← mk_C, εC_mk, constantCoeff_C]

theorem εC_m {z : C R I n} (hz : z ∈ m R I n) : εC R I n z = 0 := by
  have : m R I n ≤ RingHom.ker (εC R I n) := by
    rw [m, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, εC_mk, cc]
    exact hp 0 (by simp)
  exact this hz

theorem mem_m {z : C R I n} (hz : εC R I n z = 0) : z ∈ m R I n := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine Ideal.mem_map_of_mem _ ?_
  intro μ hμ
  have : μ = 0 := by
    ext i
    have := (Finset.sum_eq_zero_iff.1 (Nat.lt_one_iff.1 hμ)) i (Finset.mem_univ _)
    simpa using this
  rw [this, ← cc, ← εC_mk]; exact hz

theorem εC_dpow {z : C R I n} (hz : z ∈ m R I n) {k : ℕ} (hk : k ≠ 0) : εC R I n ((δ R I n).dpow k z) = 0 := by
  have := congrArg (εC R I n) ((δ R I n).factorial_mul_dpow_eq_pow (n := k) hz)
  rw [map_mul, map_pow, εC_m R I n hz, zero_pow hk, map_natCast] at this
  exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

theorem εC_E (ν : I → ℕ) : εC R I n (E R I n ν) = if ν = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, E_zero, map_one]
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h'; push_neg at h'; exact h (funext h')
    rw [E, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (εC_dpow R I n (x_mem R I n i) hi)

def i0 : Idx I n := ⟨0, by simp⟩

def εR : B R I n →ₗ[R] K R where
  toFun y := εC R I n y
  map_add' y z := by simp
  map_smul' r y := by
    change εC R I n ((r • y : B R I n) : C R I n) = r • εC R I n y
    rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R (K R) (C R I n), map_mul, εC_alg,
      Algebra.smul_def]

theorem coord_eq (y : B R I n) : algebraMap R (K R) ((b R I n).repr y (i0 I n)) = εC R I n y := by
  have : (Algebra.linearMap R (K R)).comp ((b R I n).coord (i0 I n)) = εR R I n := by
    refine (b R I n).ext fun ν => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]
    change _ = εC R I n ((b R I n ν : B R I n) : C R I n)
    rw [b_apply, εC_E, Finsupp.single_apply]
    by_cases h : ν.1 = 0
    · have : i0 I n = ν := Subtype.ext h.symm
      simp [this, h]
    · have : i0 I n ≠ ν := fun e => h (congrArg Subtype.val e).symm
      simp [this, Ne.symm this, h]
  exact LinearMap.congr_fun this y

def π : B R I n →+* R where
  toFun y := (b R I n).repr y (i0 I n)
  map_one' := IsFractionRing.injective R (K R) (by rw [coord_eq]; simp)
  map_mul' y z := IsFractionRing.injective R (K R) (by rw [map_mul (algebraMap R (K R)), coord_eq, coord_eq, coord_eq,
    Subalgebra.coe_mul, map_mul])
  map_zero' := by rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  map_add' y z := by rw [LinearEquiv.map_add, Finsupp.add_apply]

theorem π_apply (y : B R I n) : algebraMap R (K R) (π R I n y) = εC R I n y := coord_eq R I n y

theorem dpow_x_mem (i : I) (k : ℕ) : (δ R I n).dpow k (x R I n i) ∈ B R I n := by
  change _ ∈ S R I n
  by_cases hk : k ≤ n + 1
  · have : (δ R I n).dpow k (x R I n i) = E R I n (Pi.single i k) := by
      rw [E, Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, (δ R I n).dpow_zero (x_mem R I n j)]
      · simp
    rw [this]; exact E_mem_S R I n _
  · have h1 := Ideal.pow_le_pow_right (show n + 2 ≤ k by omega) (dpow_mem_pow R I n k (x_mem R I n i))
    rw [m_pow, Ideal.mem_bot] at h1
    rw [h1]; exact Submodule.zero_mem _

def Q (z : C R I n) : Prop := z ∈ m R I n ∧ ∀ k, (δ R I n).dpow k z ∈ B R I n

theorem Q_zero : Q R I n 0 := by
  refine ⟨Ideal.zero_mem _, fun k => ?_⟩
  rcases k with _ | k
  · rw [(δ R I n).dpow_zero (Ideal.zero_mem _)]; exact Subalgebra.one_mem _
  · rw [(δ R I n).dpow_eval_zero k.succ_ne_zero]; exact Subalgebra.zero_mem _

theorem Q_add {y z : C R I n} (hy : Q R I n y) (hz : Q R I n z) : Q R I n (y + z) := by
  refine ⟨Ideal.add_mem _ hy.1 hz.1, fun k => ?_⟩
  rw [(δ R I n).dpow_add hy.1 hz.1]
  exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (hy.2 _) (hz.2 _)

theorem Q_smul (r : R) {z : C R I n} (hz : Q R I n z) : Q R I n (r • z) := by
  rw [Algebra.smul_def]
  refine ⟨Ideal.mul_mem_left _ _ hz.1, fun k => ?_⟩
  rw [(δ R I n).dpow_mul hz.1]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ r) _) (hz.2 k)

theorem Q_E {ν : I → ℕ} (hν : ν ≠ 0) : Q R I n (E R I n ν) := by
  obtain ⟨i₀, hi⟩ : ∃ i, ν i ≠ 0 := by
    by_contra h'; push_neg at h'; exact hν (funext h')
  have hE : E R I n ν = (∏ i ∈ Finset.univ.erase i₀, (δ R I n).dpow (ν i) (x R I n i)) *
      (δ R I n).dpow (ν i₀) (x R I n i₀) := (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  have hy : (δ R I n).dpow (ν i₀) (x R I n i₀) ∈ m R I n := (δ R I n).dpow_mem hi (x_mem R I n i₀)
  have ha : (∏ i ∈ Finset.univ.erase i₀, (δ R I n).dpow (ν i) (x R I n i)) ∈ B R I n :=
    Subalgebra.prod_mem _ fun i _ => dpow_x_mem R I n i _
  rw [hE]
  refine ⟨Ideal.mul_mem_left _ _ hy, fun k => ?_⟩
  rw [(δ R I n).dpow_mul hy, (δ R I n).dpow_comp hi (x_mem R I n i₀)]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ha _)
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_x_mem R I n i₀ _))

theorem integral (y : B R I n) (hy : π R I n y = 0) : Q R I n (y : C R I n) := by
  rw [← (b R I n).linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum,
    AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_induction _ (Q R I n) (fun _ _ => Q_add R I n) (Q_zero R I n) fun ν _ => ?_
  rw [Subalgebra.coe_smul, b_apply]
  by_cases hν : ν.1 = 0
  · have : ν = i0 I n := Subtype.ext hν
    have h0 : (b R I n).repr y ν = 0 := by rw [this]; exact hy
    rw [h0, zero_smul]; exact Q_zero R I n
  · exact Q_smul R I n _ (Q_E R I n hν)

end GlobalTheory.DivPowTrunc

namespace GlobalTheory.DivPowTrunc

variable (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Type) [Fintype I] (n : ℕ)

attribute [local instance] charZero_K

abbrev f : B R I n →+* C R I n := (B R I n).val

def J : Ideal (C R I n) := (RingHom.ker (π R I n)).map (f R I n)

theorem ker_m {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) : (y : C R I n) ∈ m R I n := by
  apply mem_m
  rw [← π_apply, RingHom.mem_ker.1 hy, map_zero]

theorem dpowJ {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) (k : ℕ) :
    (DividedPowers.RatAlgebra.dividedPowers (J R I n)).dpow k (f R I n y) = (δ R I n).dpow k (y : C R I n) := by
  have h1 : f R I n y ∈ J R I n := Ideal.mem_map_of_mem _ hy
  simp only [δ, DividedPowers.RatAlgebra.dpow_apply, if_pos h1, if_pos (ker_m R I n hy)]
  rfl

theorem hmem (k : ℕ) {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) :
    ∃ (z : B R I n) (_ : k ≠ 0 → z ∈ RingHom.ker (π R I n)),
      f R I n z = (DividedPowers.RatAlgebra.dividedPowers (J R I n)).dpow k (f R I n y) := by
  refine ⟨⟨(δ R I n).dpow k (y : C R I n), (integral R I n y hy).2 k⟩, fun hk => ?_, ?_⟩
  · rw [RingHom.mem_ker]
    apply IsFractionRing.injective R (K R)
    rw [π_apply, map_zero]
    exact εC_dpow R I n (ker_m R I n hy) hk
  · rw [dpowJ R I n hy]; rfl

def κ : DividedPowers (RingHom.ker (π R I n)) :=
  DividedPowers.ofInjective (RingHom.ker (π R I n)) (J R I n) (f R I n) Subtype.val_injective
    (DividedPowers.RatAlgebra.dividedPowers (J R I n)) rfl fun k _ hy => hmem R I n k hy

theorem κ_apply {y : B R I n} (hy : y ∈ RingHom.ker (π R I n)) (k : ℕ) :
    (((κ R I n).dpow k y : B R I n) : C R I n) = (δ R I n).dpow k (y : C R I n) := by
  simp only [κ, DividedPowers.ofInjective, dif_pos hy]
  exact (Exists.choose_spec (hmem R I n k hy)).2.trans (dpowJ R I n hy k)

theorem nil : IsNilDP (κ R I n) := by
  refine ⟨n + 2, fun l hl hs => ?_⟩
  have key : ∀ l : List (ℕ × B R I n), (∀ p ∈ l, p.2 ∈ RingHom.ker (π R I n)) →
      (((l.map fun p => (κ R I n).dpow p.1 p.2).prod : B R I n) : C R I n) ∈ m R I n ^ (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro h
      have hp : p.2 ∈ RingHom.ker (π R I n) := h p (by simp)
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Subalgebra.coe_mul, pow_add, κ_apply R I n hp]
      exact Ideal.mul_mem_mul (dpow_mem_pow R I n _ (ker_m R I n hp)) (ih fun q hq => h q (by simp [hq]))
  have h2 := Ideal.pow_le_pow_right hs (key l hl)
  rw [m_pow, Ideal.mem_bot] at h2
  exact Subtype.val_injective h2

def jetRing : JetRing R I n where
  B := B R I n
  b := b R I n
  one := Subtype.ext (by rw [b_apply]; exact E_zero R I n)
  mul ν ν' := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, b_apply, b_apply, E_mul]
    split_ifs with h
    · simp [b_apply]
    · rw [E_big R I n _ (by simp only [Pi.add_apply] at h ⊢; omega)]
      simp
  π := π R I n
  π_eq _ := rfl
  κ := κ R I n
  nil := nil R I n

end GlobalTheory.DivPowTrunc

theorem GlobalTheory.DivPowTrunc.jetRingEx : GlobalTheory.LatJet.JetRingEx :=
  fun R _ _ _ I _ n => ⟨GlobalTheory.DivPowTrunc.jetRing R I n⟩
end
end

section
namespace GlobalTheory.JoinFun

theorem denominators_transport_reflection : GlobalTheory.Published.HilbertBlumenthal → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport ∧ GlobalTheory.ToricTransport.TwistedTransport ∧ GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators ∧ GlobalTheory.SqTop.Refl := by
  intro hHB hGD hADR hADC hPC hGM hST hEM hHCF hSKDR hPZ hHT
  have hDP : GlobalTheory.Published.DelignePappasModel := hHB.1
  have hHQ : GlobalTheory.Published.HilbertQExpansion := hHB.2.1
  have hQAll := GlobalTheory.T.qexpansion_on_all_components hDP hHQ
  have hW2 := GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ
  have hLip := GlobalTheory.T.lipschitz_formula_totally_real_poisson
  have hS44 := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hZD := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSKDR
  have hEisExp := GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta hLip hW2 hPZ
  have hEisRule := GlobalTheory.T.eisenstein_rule_of_q_expansion hQAll hEisExp GlobalTheory.EisModular.eisMod GlobalTheory.PairFourier.eisFourier GlobalTheory.T.torus_form_statement_holds
  have hJetAn := GlobalTheory.T.jet_analytic_of_periods hGM hPC hHB hGD hADR hADC hS44
  have hJetBC := GlobalTheory.T.jet_base_change_of_deformation hGD hADR
  have hJetLift := GlobalTheory.T.jet_lift_of_deformation_de_rham hGD hADR hADC
  have hJetCore := GlobalTheory.LatJet.jetCore_of GlobalTheory.DivPowTrunc.jetRingEx hJetLift hJetBC hJetAn
  have hMAlg := GlobalTheory.T.algebraic_model_of_de_rham hPC hADR hADC
  have hMConj := GlobalTheory.T.conjugate_model_of_de_rham hPC hADR hADC
  have hMInt := GlobalTheory.T.integral_model_of_algebraic_model hPC hST hADR hADC GlobalTheory.T.polarisation_module_statement GlobalTheory.T.polarisation_dual_statement hMAlg
  have hJetInt := GlobalTheory.JetIntegral.jetInt hEisRule hJetCore hMInt
  have hExp := GlobalTheory.JetExp.expansion_of_jetInt hJetInt
  have hRam := GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion hS44 hExp
  have hUnr := GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality hS44 hJetInt
  have hLatAlg := GlobalTheory.LatAlgebraic.latAlg hZD hS44 hEisRule hJetCore hMAlg
  have hLatConj := GlobalTheory.LatConjOne.latConj hZD hS44 hEisRule hJetCore hMAlg hMConj
  have hField := GlobalTheory.SqTop.fieldDat
  have hAbs := GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT
  have hLNe := GlobalTheory.SqTop.lNe_of_functionalEquation hAbs GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips hField
  exact ⟨GlobalTheory.T.toric_denominator_of_zeta_denominators hZD hRam hUnr, GlobalTheory.T.hilbert_class_field_lattice_transport hHCF hLatAlg hLatConj,
    GlobalTheory.TwistedTransportProof.main (GlobalTheory.T.period_existence_cm hEM) hLatAlg hLatConj, hZD, GlobalTheory.T.reflection_of_functional_equation hHT hField hLNe⟩

end GlobalTheory.JoinFun
end
