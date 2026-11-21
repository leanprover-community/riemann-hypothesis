import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeSandwichOfLatticeNormalForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormBoundsUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VectorsLinearMapsBoundedDenominatorsAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChange
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingCharacterArgumentCompUnipotentRadicals
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingBoundedIntegralStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelEqParahoricCategory
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  first | exact @GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | exact GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | (intros; apply GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSandwich_of_latticeNormalForm : ∀ (X : Fields) (Pr : Primes X) (R : Ranks), GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R := by
  first | exact @GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | exact GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | (intros; apply GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.QNormalShape

section Abstract

variable {O F : Type} [CommRing O] [Field F] [Algebra O F]

theorem mem_span_basis_iff [IsDomain O] [IsFractionRing O F] {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) (v : Fin N → F) :
    v ∈ Submodule.span O (Set.range b) ↔ ∀ l, b.repr v l ∈ Set.range (algebraMap O F) :=
  b.mem_span_iff_repr_mem O v

theorem isLattice_span_basis {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) :
    Submodule.IsLattice F (Submodule.span O (Set.range b)) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]

theorem mem_normalForm_iff {Y : Type} [AddCommGroup Y] [Module F Y] [Module O Y] {c : ℕ} (q : O)
    (M : Submodule O Y) (a : Fin c → Y) (e : Fin c → ℤ) (z y : Y) :
    y ∈ IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm F q M a e z ↔ ∃ m ∈ M, ∃ s : Fin c → O,
      y = m + ∑ i, s i • ((algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)) := by
  unfold IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm
  rw [← Submodule.span_range_eq_iSup, Submodule.mem_sup]
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨m, hm, s, rfl⟩
  · rintro ⟨m, hm, s, rfl⟩
    exact ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩

theorem irreducible_of_notMem_sq [IsDomain O] [IsDiscreteValuationRing O] {q : O}
    (h1 : q ∈ IsLocalRing.maximalIdeal O) (h2 : q ∉ IsLocalRing.maximalIdeal O ^ 2) : Irreducible q := by
  refine ⟨h1, fun a b hab => ?_⟩
  by_contra h
  rw [not_or] at h
  exact h2 (hab ▸ pow_two (IsLocalRing.maximalIdeal O) ▸ Ideal.mul_mem_mul h.1 h.2)

end Abstract

theorem exists_shape : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord → ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (n c : ℕ)
    (h : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ∃ r ∈ Loc.R1 E n c, ∃ (e : Fin c → ℤ) (z : Fin n → E),
      (r * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z := by
  intro H E _ _ _ P hd n c h
  have hP := P.isPrime
  have hS : P.asIdeal.primeCompl ≤ (𝓞 E)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField E P.asIdeal.primeCompl hS
  have : IsLocalization.AtPrime A P.asIdeal := Localization.subalgebra.isLocalization_ofField E _ hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot A
  have : IsFractionRing A E := Localization.subalgebra.isFractionRing_ofField E _ hS
  have hA : ∀ a : E, a ∈ Set.range (algebraMap A E) ↔ IntAt P a := by
    intro a
    constructor
    · rintro ⟨⟨x, r, s, hs, rfl⟩, rfl⟩
      refine ⟨r, s, hs, ?_⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      change algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E r * (algebraMap (𝓞 E) E s)⁻¹) = _
      field_simp
    · rintro ⟨r, s, hs, e⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      refine ⟨⟨a, r, s, hs, ?_⟩, rfl⟩
      rw [← e]
      field_simp
  have hmax : Ideal.map (algebraMap (𝓞 E) A) P.asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A
  have hq : Irreducible (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) := by
    refine irreducible_of_notMem_sq ?_ ?_
    · rw [← hmax]
      exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · rw [← hmax, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.asIdeal.primeCompl]
      rintro ⟨s, hs, hm⟩
      exact (Ideal.IsPrime.mul_mem_pow _ hm).elim hs hd.2
  obtain ⟨r, hr, e, z, hz⟩ := H A E _ hq n c _ (isLattice_span_basis (Pi.basisFun E (Fin n))) _
    (isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h))
  refine ⟨r, hr, e, z, ?_⟩
  have hqE : algebraMap A E (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) = (qOf P : E) := by
    rw [map_natCast, map_natCast]
  ext y
  have hy := SetLike.ext_iff.1 hz y
  rw [mem_normalForm_iff, hqE] at hy
  simp only [IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.moveBy, Submodule.mem_map, mem_span_basis_iff, hA, Module.Basis.map_repr,
    LinearEquiv.trans_apply, Pi.basisFun_repr, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hy
  simp only [Set.mem_image, Set.mem_setOf_eq, IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, mem_stdAt_iff, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨l, hl, rfl⟩, s, hs⟩ := hy.1 ⟨h v, by simpa [IntV] using hv, rfl⟩
    exact ⟨l, hl, fun i => algebraMap A E (s i), fun i => (hA _).1 ⟨_, rfl⟩, by simpa only [algebraMap_smul] using hs⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    choose t ht using fun i => (hA _).2 (hs i)
    obtain ⟨v, hv, hv'⟩ := hy.2 ⟨_, ⟨l, hl, rfl⟩, t, by simp only [← ht, algebraMap_smul]⟩
    refine ⟨h.symm v, hv, ?_⟩
    rw [← hv']
    simp

end GlobalTheory.QNormalShape
end
end

section
namespace GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable

theorem finsum_quot_eq {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by
  classical
  haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx
  letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _
  let φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M :=
    fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := by
    intro v
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    have := hf v _ (hMN h)
    simpa using this
  rw [finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
      have : ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s := by
        intro s _
        have : ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s := by
          intro q
          simp only [φ]
          rw [hout, hf _ _ (q.out).2]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
    · rintro ⟨s, q⟩ hp ⟨s', q'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      simp only [φ, QuotientAddGroup.eq] at h
      have hs : s = s' := by
        apply hinj s hp.1 s' hp'.1
        have h1 := N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))
        convert h1 using 1
        abel
      subst hs
      have hq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        convert h using 1
        push_cast
        abel
      rw [hq]
  · intro c hc
    obtain ⟨s, hs, hn⟩ := hcov c.out hc
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩
    have h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out
        + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N := by
      rw [← QuotientAddGroup.eq]; simp
    rw [AddSubgroup.mem_addSubgroupOf] at h
    conv_rhs => rw [← Quotient.out_eq c]
    apply QuotientAddGroup.eq.2
    convert h using 1
    push_cast
    abel

theorem sum_reps_ne_zero_iff : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  intro V K _ _ _ f N N' S S' h1 h2 hf hf' hi hc hi' hc'
  have e1 : (N ⊓ N').relIndex N ≠ 0 := by rwa [AddSubgroup.inf_relIndex_left]
  have e2 : (N ⊓ N').relIndex N' ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have a := finsum_quot_eq f (N ⊓ N') N S inf_le_left e1 hf hi hc
  have b := finsum_quot_eq f (N ⊓ N') N' S' inf_le_right e2 hf' hi' hc'
  have c1 : (((N ⊓ N').relIndex N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e1
  have c2 : (((N ⊓ N').relIndex N' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e2
  rw [← mul_ne_zero_iff_left c1, ← a, b, mul_ne_zero_iff_left c2]

end GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_coset_reps_ne_zero_iff_commensurable : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  first | exact @GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff | exact GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff | (intros; apply GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFractions_represent_primeNormQuotient : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  first | exact @GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | exact GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | (intros; apply GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y) := by
  first | exact @GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | exact GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators | (intros; apply GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxSum_ne_zero_invariant_affineChange : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  first | exact @GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | exact GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | (intros; apply GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  first | exact @GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | exact GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | (intros; apply GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  first | exact @GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | exact GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action | (intros; apply GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∃ d : F, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) = Loc.chArg (Loc.xx1 xj t) + d := by
  first | exact @GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | exact GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp | (intros; apply GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.parahoric_le_integral_gl

theorem inX_mem_nfLat_iff {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ)
    (e : Fin c → ℤ) (z : Sp E n) (x : Sp E n) :
    Loc.inX E n c x ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z ↔ x ∈ stdAt E n P := by
  constructor
  · rintro ⟨l, hl, s, -, h⟩
    have hs : ∀ b, s b = 0 := by
      intro b
      have h1 := congrFun h (Fin.natAdd n b)
      have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
      have h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0 := fun y => by
        rw [inX_apply, dif_neg (by simp)]
      have h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) =
          if b = i then ((qOf P : E) ^ e i) else 0 := by
        intro i
        unfold IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen
        rw [Pi.smul_apply, Pi.add_apply]
        have h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0 := by
          split_ifs
          · exact h2 z
          · rfl
        rw [h4]
        simp [Loc.eN, Fin.val_inj]
      rw [Pi.add_apply, h2, h2, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h
    rwa [inX_injective h]
  · intro hx
    exact ⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  rintro X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) sharp j P := by
    have := Subgroup.mem_comap.1 hr
    simpa using this
  unfold Jat at hJ
  rw [if_neg hP] at hJ
  have hk := hJ.1
  have key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P := by
    intro y
    rw [← hnf, mem_stdAt_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : h⁻¹ (h w) = w := h.symm_apply_apply w
      rw [this]
      exact (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw
    · intro hy
      exact ⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩
  rw [← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key,
    ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]
  have : (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x)) := by
    change h⁻¹ (r (h (h.symm _))) = _
    rw [h.apply_symm_apply]
  rw [this]

end GlobalTheory.Proof.parahoric_le_integral_gl
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_le_integral_gl : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  first | exact @GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint | exact GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint | (intros; apply GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_eq_parahoric_category : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h ρ : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1) → (∀ (g : ↥lev.H) (r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h → (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) → ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r) → ∃ lev' : LevI X.E X.K (R.N j) P.1, lev'.H = (prCat (Pr := Pr) cst.sharp j P.1 (ρ * h)).subgroupOf (GLint X.E (R.N j) P.1) ∧ (∀ (g : ↥lev'.H) (r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (ρ * h) → (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) → ((lev'.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P (ρ * h) r) := by
  first | exact @GlobalTheory.Proof.level_eq_parahoric_category.main | exact GlobalTheory.Proof.level_eq_parahoric_category.main | (intros; apply GlobalTheory.Proof.level_eq_parahoric_category.main <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_reduction_of_valuation_eq_one (P : HeightOneSpectrum (𝓞 E)) {b : E} (hb : P.valuation E b = 1) :
    IsUnit (redP P b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have h1 : IntAt P b := (IntegralPowerExpansion.intAt_iff_val P b).2 hb.le
  have h2 : IntAt P b⁻¹ := (IntegralPowerExpansion.intAt_iff_val P _).2 (by rw [map_inv₀, hb, inv_one])
  have h3 := reduction_mul h1 h2
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [mul_inv_cancel₀ hb0, h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem exists_isUnit_reduction_div_pow {P : HeightOneSpectrum (𝓞 E)} (hP : GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {a : E} (ha : a ≠ 0) :
    ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
  have hv : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  refine ⟨-WithZero.log (P.valuation E a), isUnit_reduction_of_valuation_eq_one P ?_⟩
  rw [map_div₀, map_zpow₀, IntegralPowerExpansion.val_q hP, ← WithZero.exp_zsmul]
  simp only [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, mul_neg, neg_mul]
  rw [WithZero.exp_log hv, div_self hv]

theorem locChar_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 →
      LocE.locChar (qOf P) cq χ a ≠ 0 := by
  intro E _ _ K _ P hP cq χ a hcq ha
  have h : IsUnit (redP P (a / (qOf P : E) ^ LocE.vP P (qOf P) a)) :=
    Classical.epsilon_spec (exists_isUnit_reduction_div_pow hP ha)
  unfold LocE.locChar LocE.unitV
  rw [dif_pos h]
  exact mul_ne_zero (zpow_ne_zero _ hcq) (Units.ne_zero _)

end GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCharacter_ne_zero_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 → LocE.locChar (qOf P) cq χ a ≠ 0 := by
  atlas_forward_decl GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNormal

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section General

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem IntHom.comp {a b c : ℕ} {x : (Fin b → E) →ₗ[E] (Fin c → E)} {y : (Fin a → E) →ₗ[E] (Fin b → E)}
    (hx : IntHom P x) (hy : IntHom P y) : IntHom P (x ∘ₗ y) := fun v hv => hx _ (hy v hv)

theorem IntHom.pow_mono {a b : ℕ} {x : (Fin a → E) →ₗ[E] (Fin b → E)} {N N' : ℕ} (h : N ≤ N')
    (hx : IntHom P (((qOf P : E) ^ N) • x)) : IntHom P (((qOf P : E) ^ N') • x) :=
  fun v hv l => Proof.NormalFormAtPrime.intAt_pow_mono h (hx v hv l)

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem intAt_chArg {n' c' n c : ℕ} {x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} {u : E} (hx : IntHom P (u • x)) :
    IntAt P (u * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h
  · exact hx _ (intV_eN P _ _) _
  · simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfNe_transfer [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {n' c' n c : ℕ} (hc : 1 ≤ c) (hc' : c' = c + 1)
    {psi : E → K} {D N : ℕ} (hN : N ≤ D) (hpsi : CharTo P D psi) {Psi Psi' : Loc.SF E K (n' + c') (n + c)}
    (h1 : HomBdd P N Psi) (h2 : HomBdd P N Psi') {C : K} (hC : C ≠ 0)
    {r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} {r' : (Fin (n' + c') → E) ≃ₗ[E] (Fin (n' + c') → E)}
    (hr : r ∈ Loc.R1 E n c) (hr' : r' ∈ Loc.R1 E n' c')
    (hrel : ∀ x, Psi' x = C * Psi (r.toLinearMap ∘ₗ x ∘ₗ r'.toLinearMap)) (H : UnfNe P psi Psi) : UnfNe P psi Psi' := by
  obtain ⟨A₀, B₀, H⟩ := H
  obtain ⟨xj', hx⟩ := Function.ne_iff.1 (H (max A₀ N) (max B₀ N) (le_max_left _ _) (le_max_left _ _))
  obtain ⟨xj, T, b, hT⟩ := GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions E n' c' n c hc hc' r hr r' hr' xj'
  obtain ⟨d, hd⟩ := GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions E n' c' n c hc hc' r hr r' hr'
  have I1 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi hN hpsi h1 xj'
  have I2 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi' hN hpsi h2 xj
  obtain ⟨A₁, B₁, hA⟩ := GlobalTheory.T.boxSum_ne_zero_invariant_affineChange GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime GlobalTheory.T.sum_coset_reps_ne_zero_iff_commensurable GlobalTheory.T.rationalFractions_represent_primeNormQuotient E K P hP _ (integrand psi Psi xj') N I1.1 T b
  refine ⟨max A₁ N, max B₁ N, fun A B hA' hB' => Function.ne_iff.2 ⟨xj, ?_⟩⟩
  have h3 : boxSum P A B (integrand psi Psi xj') ≠ 0 := by
    rw [GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz E K P hP.1 _ _ N I1.1 A B (le_of_max_le_right hA') (le_of_max_le_right hB'),
      ← GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz E K P hP.1 _ _ N I1.1 (max A₀ N) (max B₀ N) (le_max_right _ _) (le_max_right _ _)]
    exact hx
  have h4 := (hA A B (le_of_max_le_left hA') (le_of_max_le_left hB')).2 h3
  have hdep : ∀ t, Psi (Loc.xx1 xj' (T t + b)) ≠ 0 → IntAt P ((qOf P : E) ^ D * d) ∧
      IntAt P ((qOf P : E) ^ D * -Loc.chArg (Loc.xx1 xj' (T t + b))) := by
    intro t ht
    have a1 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I1.2 _ ht)
    have a2 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I2.2 t (by rw [hrel, hT]; exact mul_ne_zero hC ht))
    refine ⟨?_, by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a1⟩
    have := a1.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a2)
    rw [← hT, hd] at this
    convert this using 1
    ring
  have hpt : ∀ t, integrand psi Psi' xj t = C * psi d * integrand psi Psi xj' (T t + b) := by
    intro t
    unfold integrand
    rw [hrel, hT]
    by_cases ht : Psi (Loc.xx1 xj' (T t + b)) = 0
    · simp [ht]
    · have e : -Loc.chArg (Loc.xx1 xj t) = d + -Loc.chArg (Loc.xx1 xj' (T t + b)) := by
        rw [← hT, hd]
        ring
      rw [e, hpsi.1 _ _ (hdep t ht).1 (hdep t ht).2]
      ring
  have hd0 : psi d ≠ 0 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h4)
    have a := (hdep t (left_ne_zero_of_mul ht)).1
    have := hpsi.1 d (-d) a (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at this
    exact left_ne_zero_of_mul (this ▸ one_ne_zero)
  change boxSum P A B (integrand psi Psi' xj) ≠ 0
  have e : boxSum P A B (integrand psi Psi' xj) =
      C * psi d * boxSum P A B (fun t => integrand psi Psi xj' (T t + b)) := by
    unfold boxSum
    simp only [hpt, ← Finset.mul_sum]
    ring
  rw [e]
  exact mul_ne_zero (mul_ne_zero hC hd0) h4

theorem homBdd_translate {a b i : ℕ} {Φ Psi : Loc.SF E K a b} {C : K} {g : (Fin a → E) ≃ₗ[E] (Fin a → E)}
    {h : (Fin b → E) ≃ₗ[E] (Fin b → E)} (hΦ : ∀ x, Φ x ≠ 0 → IntHom P x)
    (hΦ' : ∀ x y, IntHom P y → Φ (x + (qOf P : E) • y) = Φ x)
    (g1 : IntHom P g.symm.toLinearMap) (g2 : IntHom P (((qOf P : E) ^ i) • g.toLinearMap))
    (h1 : IntHom P h.symm.toLinearMap) (h2 : IntHom P (((qOf P : E) ^ (i + 1)) • h.toLinearMap))
    (e : ∀ x, Psi x = C * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)) : HomBdd P (i + 1) Psi := by
  refine ⟨fun x hx v hv => ?_, fun x y hy => ?_⟩
  · rw [e] at hx
    have := h2 _ (hΦ _ (right_ne_zero_of_mul hx) _ (g1 v hv))
    simpa using this
  · rw [e, e, ← hΦ' (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ (h1.comp (hy.comp g2))]
    congr 2
    refine LinearMap.ext fun v => ?_
    simp [pow_succ', mul_smul]

end General

section Chain

open IndefiniteRowSideFullHecke.SandwichNormalForm

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def Between (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  IntHom P h.symm.toLinearMap ∧ IntHom P (((qOf P : X.E) ^ j) • h.toLinearMap)

theorem between_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (h : AutY X R j) :
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P) ↔ Between j P h := by
  simp only [mem_lamYat hP]
  exact ⟨fun H => ⟨fun v hv => (H v hv).1, fun v hv => (H v hv).2⟩, fun H v hv => ⟨H.1 v hv, H.2 v hv⟩⟩

theorem between_of_nf {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) {h : AutY X R j} (H : NF Pr j P h) :
    Between j P h := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.latticeSandwich_of_latticeNormalForm X Pr R j P hP h 1 H (one_mem _)
  rw [mul_one] at h1 h2
  refine (between_iff hP h).1 fun x hx => ⟨?_, h2 x hx⟩
  obtain ⟨y, hy, rfl⟩ := h1 x hx
  rwa [show h⁻¹ (h y) = y from h.symm_apply_apply y]

theorem sameDC_symm {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h' : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h') : SameDC (Pr := Pr) sharp j P h' h := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  exact ⟨r⁻¹, inv_mem hr, k⁻¹, inv_mem hk, by group⟩

theorem sameDC_mul (sharp : Bool) {j : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) {r : AutY X R j}
    (hr : r ∈ Loc.R1 X.E (R.N j) (cOf R j)) : SameDC (Pr := Pr) sharp j P h (r * h) :=
  ⟨r, hr, 1, one_mem _, (mul_one _).symm⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def omScal (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu cst i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu cst i P (LinearEquiv.det h : X.Eˣ))⁻¹ *
    cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * (R.N (i + 1) + cOf R (i + 1) : ℕ)) *
    cst.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det h : X.Eˣ) * (R.N i + cOf R i : ℕ))

theorem omPhi_eq (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P hal h x =
      omScal Ch sel mu cst i P hal h * PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) := rfl

theorem localUnfoldingNonvanishing_iff_eventuallyNonzero (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ UnfNe P.1 (cst.psi P) (omPhi Ch sel mu cst i P hal h) := Iff.rfl

variable {Ch sel mu cst}

theorem omScal_ne_zero (hc : cst.Ok) {i : ℕ} {P : rowSG Pr sel mu} (hd : DegOne P.1) (hm : cst.muq (i + 1) P ≠ 0)
    (hal : AutY X R i) (h : AutY X R (i + 1)) : omScal Ch sel mu cst i P hal h ≠ 0 := by
  have hq : cst.sq P ≠ 0 := by
    intro e
    have := hc.sq_sq P
    rw [e, zero_pow two_ne_zero] at this
    exact hd.1.ne_zero (by exact_mod_cast this.symm)
  have hmu : ∀ a : X.Eˣ, muAt Ch sel mu cst i P a ≠ 0 := fun a => GlobalTheory.T.localCharacter_ne_zero_of_ne_zero X.E X.K P.1 hd _ _ _ hm a.ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu _) (inv_ne_zero (hmu _))) (zpow_ne_zero _ hq)) (zpow_ne_zero _ hq)

theorem rank_le (R : Ranks) (j : ℕ) : R.k ≤ R.N j ∧ R.r ≤ R.N j + cOf R j := by
  have : j ≤ j * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold Ranks.N Ranks.r cOf
  omega

theorem phiAt_prop {sharp : Bool} {i : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (∀ x, PhiAt Ch mu sharp i P x ≠ 0 → IntHom P x) ∧
      ∀ x y, IntHom P y → PhiAt Ch mu sharp i P (x + (qOf P : X.E) • y) = PhiAt Ch mu sharp i P x := by
  unfold PhiAt
  rw [if_neg hP]
  exact GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant X.E X.K P _ _ _ _ _ _ _ (rank_le R i).1 (rank_le R (i + 1)).1 (rank_le R i).2 (rank_le R (i + 1)).2

theorem omPhi_bdd {i : ℕ} {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h1 : Between i P.1 hal) (h2 : Between (i + 1) P.1 h) : HomBdd P.1 (i + 1) (omPhi Ch sel mu cst i P hal h) :=
  homBdd_translate (phiAt_prop hP).1 (phiAt_prop hP).2 h1.1 h1.2 h2.1 h2.2 (omPhi_eq Ch sel mu cst i P hal h)

theorem omPhi_mul {i : ℕ} {P : rowSG Pr sel mu} {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h0 : omScal Ch sel mu cst i P hal h ≠ 0) (ρ' : AutY X R i) (ρ : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P (ρ' * hal) (ρ * h) x =
      omScal Ch sel mu cst i P (ρ' * hal) (ρ * h) / omScal Ch sel mu cst i P hal h *
        omPhi Ch sel mu cst i P hal h ((ρ⁻¹).toLinearMap ∘ₗ x ∘ₗ ρ'.toLinearMap) := by
  rw [omPhi_eq, omPhi_eq, ← mul_assoc, div_mul_cancel₀ _ h0]
  rfl

theorem first_unipotent_class_transfer (hc : cst.Ok) {i : ℕ} (hi : i + 1 ≤ R.m - 2) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hd : DegOne P.1)
    (hm : cst.muq (i + 1) P ≠ 0) (hD : i + 1 ≤ cst.D P) {hal hal' ρ' : AutY X R i} {h h' ρ : AutY X R (i + 1)}
    (hρ' : ρ' ∈ Loc.R1 X.E _ _) (hρ : ρ ∈ Loc.R1 X.E _ _) (e' : hal' = ρ' * hal) (e : h' = ρ * h)
    (a1 : Between i P.1 hal) (a2 : Between i P.1 hal') (b1 : Between (i + 1) P.1 h) (b2 : Between (i + 1) P.1 h')
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal' h' := by
  rw [localUnfoldingNonvanishing_iff_eventuallyNonzero] at H ⊢
  subst e e'
  exact unfNe_transfer hd (by unfold cOf; omega) (by unfold cOf; omega) hD ⟨hc.psi_add P, hc.psi_int P⟩
    (omPhi_bdd hP a1 b1) (omPhi_bdd hP a2 b2)
    (div_ne_zero (omScal_ne_zero hc hd hm _ _) (omScal_ne_zero hc hd hm _ _)) (inv_mem hρ) hρ'
    (omPhi_mul (omScal_ne_zero hc hd hm _ _) ρ' ρ) H

theorem lamYat_coe {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = {v | IntV P v} :=
  Set.ext fun v => mem_lamYat hP v

variable {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Chain

end GlobalTheory.QNormal
end
end
