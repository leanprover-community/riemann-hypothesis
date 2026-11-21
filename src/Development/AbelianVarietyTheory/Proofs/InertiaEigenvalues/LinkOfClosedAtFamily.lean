import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivision
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FactsAtMembershipStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OverNEOfNEb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtraBoundOfTwistingEigenFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingEigenOfDepthZeroSupport
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfFamilyFactsStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherMore
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.Adm4Tab

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty :=
  by apply _root_.UpperTheory.Reformulated.B.Qk8.exists_place <;> assumption

theorem sumOver_const (D : D7) (l : ℕ) (hl : l ≠ 0) (k : ℝ) :
    TwistedPlaces.sumOver D l (fun _ => k) = ((placesOver D.host.E l).ncard : ℝ) * k := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.sum_const, Set.ncard_eq_toFinset_card _ hf,
    nsmul_eq_mul]

theorem sumOver_mono (D : D7) (l : ℕ) (hl : l ≠ 0) {f g : HeightOneSpectrum (𝓞 D.host.E) → ℝ}
    (h : ∀ lam, f lam ≤ g lam) : TwistedPlaces.sumOver D l f ≤ TwistedPlaces.sumOver D l g := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  exact Finset.sum_le_sum fun lam _ => h lam

theorem le_supZ {D : D7} (i : D.nd.Loc) (f : D.nd.X i → ℝ) {π : D.nd.X i} (hπ : π ∈ D.nd.Zgood i) :
    f π ≤ KillingConditions.supZ i f := by
  unfold KillingConditions.supZ
  rw [dif_pos ⟨π, hπ⟩]
  exact Finset.le_sup' f hπ

end GlobalTheory.NLink.Adm4Tab

open GlobalTheory.NLink.Adm4Tab in

theorem GlobalTheory.NLink.admissible_table_of_conclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i,
      Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  intro D L P X C tf hC h23 i hi hg π hπ
  have key : ∀ b, Bd X.ρ i π b → b ≤ TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i →
      (D.nd.vcc i π : ℝ) ≤ (tab L X tf C).s i π + TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + (tab L X tf C).BB i + TwistedPlaces.epsL (D.nd.l i) := by
    intro b hb hle
    unfold Bd at hb
    have hs : (tab L X tf C).s i π = (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) := rfl
    rw [hs]
    linarith
  have hl0 : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hq3 : D.host.q ≠ 3 := D.host.q_ne_three
  have hd3 : D.host.d ≠ 3 := by have := D.host.hyp.2.2.2.1; omega
  have hzero : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
    rw [sumOver_const D _ hl0, mul_zero]
  by_cases h2 : D.nd.l i ∈ D.host.small
  · apply key _ (h23 i hi (Or.inl h2) π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    rw [hlen, hzero, hBB, zero_add]
  by_cases h3 : D.nd.l i = 3
  · apply key _ (h23 i hi (Or.inr h3) π hπ)
    have hBB : (tab L X tf C).BB i = 0 := by
      have hq : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by
        rw [h3]; rintro (h | h) <;> [exact hq3 h.symm; exact hd3 h.symm]
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg hq, if_neg hR]
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    rw [hBB, hlen, h3, sumOver_const D 3 (by norm_num)]
    have hf3 := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
    have hpos : 0 < (placesOver D.host.E 3).ncard :=
      (Set.ncard_pos hf3).2 (placesOver_nonempty D.host.E 3 Nat.prime_three)
    have hpos' : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_div_cancel₀ _ hpos', add_zero]
  by_cases hqd : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d
  · apply key _ (hC.ram i hi hqd π hπ)
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hqd
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, if_neg h2, if_pos hqd]
    rw [hlen, hzero, hBB, zero_add]
  by_cases hR : KillingConditions.RangeAD L X.exc (D.nd.l i)
  · have hm := hC.mid i hi hg hR π hπ
    have hb : Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) + X.errorBoundHub i π) := by
      unfold Bd
      linarith
    apply key _ hb
    have hlen : (tab L X tf C).len i = KillingConditions.lenR X.len0 i := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_pos hR]
    have hBB : (tab L X tf C).BB i = KillingConditions.supZ i (X.errorBoundHub i) := by
      simp only [tab, if_neg h2, if_neg hqd, if_pos hR]
    rw [hlen, hBB]
    have h1 : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) ≤ TwistedPlaces.sumOver D (D.nd.l i) (KillingConditions.lenR X.len0 i) :=
      sumOver_mono D _ hl0 fun lam => le_supZ i (fun π => X.len0 i π lam) hπ
    have h2' : X.errorBoundHub i π ≤ KillingConditions.supZ i (X.errorBoundHub i) := le_supZ i (X.errorBoundHub i) hπ
    linarith
  · have hlt : TwistedPlaces.lStar L < (D.nd.l i : ℝ) ∧ D.nd.l i ∉ X.exc := by
      by_contra hc
      exact hR ⟨fun h => h.elim h2 h3, hqd, hc⟩
    apply key _ (hC.large i hi hlt.1 hg hlt.2 π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = 0 := by
      simp only [tab, if_neg h2, if_neg hqd, if_neg hR]
    rw [hlen, hzero, hBB, add_zero]

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_table_of_local_bounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i, Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  atlas_forward_decl GlobalTheory.NLink.admissible_table_of_conclusion
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm5_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  classical
  intro D L P X C tf h i hi hl
  obtain ⟨h2, hq, hd, hg⟩ := hl
  have hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by tauto
  have hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by
    have := h.pos
    positivity
  show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0) ≤ _
  rw [if_neg h2, if_neg hqd]
  split_ifs with hR
  · unfold KillingConditions.supZ
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)
    · exact hR0
  · exact hR0

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  atlas_forward_decl GlobalTheory.NLink.adm5_tab
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm6_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  intro D L P X C tf hC
  refine ⟨?_, ?_⟩
  · intro i hi π hπ
    have hk := ((hC.kill i hi).1 π hπ).2
    show (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + TwistedPlaces.epsL (D.nd.l i) ≤ _
    unfold TwistedPlaces.epsL at hk ⊢
    have : (2 : ℝ) / (D.nd.l i : ℝ) ^ 2 = 1 / (D.nd.l i : ℝ) ^ 2 + 1 / (D.nd.l i : ℝ) ^ 2 := by ring
    rw [this]
    linarith
  · intro j _ l _
    show TwistedPlaces.epsL l + TwistedPlaces.epsL l ≤ 2 / (l : ℝ) ^ 2
    unfold TwistedPlaces.epsL
    apply le_of_eq
    ring

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  atlas_forward_decl GlobalTheory.NLink.adm6_tab
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem largePrimeLengthVanishing_and_exceptionalBounded_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ)
    (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  intro D L P X C tf h
  obtain ⟨h3, hq, hd, -, -, hsl⟩ := h.small
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hlt, -, hexc⟩ := hl
    have hexc' : D.nd.l i ∉ X.exc := hexc
    have h2 : D.nd.l i ∉ D.host.small := fun he => by linarith [hsl _ he]
    have h3' : D.nd.l i ≠ 3 := by
      rintro he; rw [he] at hlt; push_cast at hlt; linarith
    have hq' : D.nd.l i ≠ D.host.q := by
      rintro he; rw [he] at hlt; linarith
    have hd' : D.nd.l i ≠ D.host.d := by
      rintro he; rw [he] at hlt; linarith
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.2.2 ⟨hlt, hexc'⟩
    refine ⟨fun lam _ => ?_, ?_⟩
    · simp only [tab, h2, h3', hR, if_false]
    · simp only [tab, h2, hR, if_false]
      rw [if_neg (by rintro (he | he) <;> contradiction)]
  · exact h.exc.1
  · exact h.exc.2

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  atlas_forward_decl GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLinkAdmF

theorem placesOver_three_nonempty (D : D7) : (placesOver D.host.E 3).Nonempty := by
  have hl : Nat.Prime 3 := Nat.prime_three
  have hne : ((3 : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hnu : ¬ IsUnit ((3 : ℕ) : 𝓞 D.host.E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ ((3 : ℕ) : 𝓞 D.host.E) = ((3 : ℕ) : ℤ) ^ Module.finrank ℤ (𝓞 D.host.E) := by
      rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 D.host.E) ((3 : ℕ) : ℤ)]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hl.one_lt.ne' h1
  obtain ⟨M, hM, hlM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hnu)
  exact ⟨⟨M, hM.isPrime, fun h => hne (by simp [h] at hlM)⟩, hlM⟩

theorem sumOver_three_even (D : D7) (c : ℝ) :
    TwistedPlaces.sumOver D 3 (fun _ => c / ((placesOver D.host.E 3).ncard : ℝ)) = c := by
  have hfin : (placesOver D.host.E 3).Finite := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
  have hpos : 0 < (placesOver D.host.E 3).ncard :=
    (Set.ncard_pos hfin).2 (placesOver_three_nonempty D)
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin]
  have : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

theorem localBoundTableAllPrimes_conditionTwoThree : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  intro D L P X C tf _ hF i hi hl
  have hFi := hF i hi hl
  by_cases h2 : D.nd.l i ∈ D.host.small
  · have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    show TwistedPlaces.sumOver D _ ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    rw [hlen, hBB]
    have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by simp [TwistedPlaces.sumOver]
    rw [h0, zero_add]
    exact hFi
  · have h3 : D.nd.l i = 3 := hl.resolve_left h2
    have hq : D.host.q ≠ 3 := D.host.q_ne_three
    have hd : D.host.d ≠ 3 := by
      have := D.host.hyp.2.2.2.1
      omega
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    have hBB : (tab L X tf C).BB i = 0 := by
      have h1 : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by omega
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg h1, if_neg hR]
    show TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i ≤ _
    have hFi' : TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i ≤ _ := hFi
    rw [h3] at hFi'
    rw [hlen, hBB, h3, sumOver_three_even, add_zero]
    exact hFi'

end GlobalTheory.NLinkAdmF

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPrimeLengthBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.SmallPrimeLengthBound L tf C → TwistedPlaces.SmallPrimeLengthBound L (tab L X tf C) C := by
  atlas_forward_decl GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  atlas_forward_decl GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

open Classical

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_rowsAndBand : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  intro D L P X C tf h
  have hC := h.pos
  obtain ⟨nA, nB, nC, nD, nBand⟩ := h.num
  have h3 : ¬ TwistedPlaces.InertK D 3 := h.small.2.2.2.1
  have hR : ∀ i, D.nd.l i ≠ 3 → KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = (tabX L X).len i := by
    intro i h3 hr; funext lam
    have hs : D.nd.l i ∉ D.host.small := fun e => hr.1 (Or.inl e)
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg hs, if_neg h3, if_pos hr]; rfl
  have hN : ∀ i, D.nd.l i ≠ 3 → ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) →
      (tab L X tf C).len i = fun _ => 0 := by
    intro i h3 hr; funext lam
    show (if D.nd.l i ∈ D.host.small then (0 : ℝ) else if D.nd.l i = 3 then _
      else if KillingConditions.RangeAD L X.exc (D.nd.l i) then _ else 0) = _
    rw [if_neg h3, if_neg hr, ite_self]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hSc := L.Sc_pos
  have hEta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hx.le _
  have hB1 : 1 ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hwB : 0 ≤ TwistedPlaces.wB L := by
    have hb' : 0 < L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X'
      positivity
    have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
    unfold TwistedPlaces.wB
    exact le_trans (by linarith) (le_max_left _ _)
  have hetaP : 0 ≤ TwistedPlaces.eta₃ L := by unfold TwistedPlaces.eta₃; linarith
  have hwP : 0 ≤ TwistedPlaces.wP L := by unfold TwistedPlaces.wP; linarith
  have hGP : 0 ≤ TwistedPlaces.GP L := by unfold TwistedPlaces.GP; linarith
  have heP : ∀ l : ℕ, l.Prime → 0 ≤ TwistedPlaces.eP L C l := by
    intro l hl
    unfold TwistedPlaces.eP
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    have h1 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := Real.logb_nonneg hl1 hB1
    have h2 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith) (by linarith)
    exact mul_nonneg hC (by linarith)
  have hflat : ∀ (tb : TwistedPlaces.Tab L) i lam (l : ℕ), 0 ≤ TwistedPlaces.flatCD L tb i lam l := by
    intro tb i lam l
    unfold TwistedPlaces.flatCD
    have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := div_nonneg (by linarith) (Nat.cast_nonneg _)
    have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if tb.band i lam then 1 else 0) :=
      mul_nonneg hetaP (by split_ifs <;> norm_num)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hP
    have h5 := hP.1
    have h3' : D.nd.l i ≠ 3 := by omega
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nA i hi hP
    · rw [hN i h3' hr]
      have hl := (D.nd.lPrime i).out
      have h0 : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
        unfold TwistedPlaces.sumOver; simp
      rw [h0, mul_zero]
      unfold TwistedPlaces.sumOver
      apply finsum_nonneg; intro lam; apply finsum_nonneg; intro _
      exact mul_nonneg (by positivity) (heP _ hl)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nB i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl1 : (1 : ℝ) ≤ D.nd.l i := by exact_mod_cast (D.nd.lPrime i).out.one_lt.le
      have h1 : 0 ≤ TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) :=
        div_nonneg (by linarith) (pow_nonneg (by linarith) _)
      have h2 : 0 ≤ (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) :=
        mul_nonneg (by linarith) (by positivity)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nC i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) (by linarith))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · intro i hi hP
    have hI := hP.1
    have h3' : D.nd.l i ≠ 3 := fun e => h3 (by rw [e] at hI; exact hI)
    by_cases hr : KillingConditions.RangeAD L X.exc (D.nd.l i)
    · rw [hR i h3' hr]; exact nD i hi hP
    · rw [hN i h3' hr]
      intro lam _
      have hl := (D.nd.lPrime i).out
      have h1 : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
      have h2 := hflat (tab L X tf C) i lam (D.nd.l i)
      have h4 := heP _ hl
      exact add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h1)
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h2))
        (mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Nat.cast_nonneg _)) h4)
  · exact nBand

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admA_admB_inert_band_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.admA L (tab L X tf C) C ∧ TwistedPlaces.admB L (tab L X tf C) C ∧ TwistedPlaces.MediumInertPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tab L X tf C) C ∧ TwistedPlaces.BandPlaceWeightApproximation L (tab L X tf C) C := by
  atlas_forward_decl GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := GlobalTheory.T.admA_admB_inert_band_tab D L P X C tf h
  obtain ⟨hE, hExc⟩ := GlobalTheory.T.localBoundTableAllPrimes_vanishing_excluded D L P X C tf h
  obtain ⟨hG, hH⟩ := GlobalTheory.T.ramifiedPrimeLengthBound_and_generatorPrimeEtaBound_tab D L P X C tf h
  exact ⟨h.pass, h2, h.rank, GlobalTheory.T.admissible_table_of_local_bounds D L P X C tf h h23, GlobalTheory.T.localBoundTableAllPrimes_sizeConditionFive D L P X C tf h,
    GlobalTheory.T.localBoundTableAllPrimes_sizeConditionSix D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    GlobalTheory.T.smallPrimeLengthBound_tab D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ), Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  atlas_forward_decl GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linkN_along_family_of_localBounds : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  atlas_forward_decl GlobalTheory.LinkFam.main
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem linkN_row : Hypotheses₂ → ∀ (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle) (C : ℝ) (CT : ℕ), 0 ≤ C →
    GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch ∧ Extra D C CT) →
    GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) →
    GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP Q Lk C CT hC hE h23
  refine ((GlobalTheory.Fc.RowE.row hE).and h23).imp fun 𝒜 σ _ hh => ?_
  obtain ⟨hA, ε1, hε, hcl⟩ := hh
  refine ⟨ε1, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hcl e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  have hF : FactsF Fm C CT := fun x hx i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i
  exact GlobalTheory.T.linkN_along_family_of_localBounds Fm (GlobalTheory.T.conclusion_of_family_facts hP Fm C CT hC hc.1.2 hF (hK Fm CH hc hL))

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_closure_linking : Hypotheses₂ → ∀ (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch ∧ Extra D C CT) → GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  atlas_forward_decl GlobalTheory.NLink.linkN_row
end

section
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem linkN_at : Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D _ _ _ => Extra D C CT) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP hL p C CT hC h1 h2 h3
  obtain ⟨R1, r1, e1⟩ := h1
  obtain ⟨R2, r2, e2⟩ := h2
  obtain ⟨R3, r3, e3⟩ := h3
  refine ⟨_, r1.and (r2.and r3), ?_⟩
  refine GlobalTheory.T.row_closure_linking hP _ _ C CT hC ?_ ?_
  · exact (GlobalTheory.Fc.RowE.and
      (GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) e1)
      (GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.2.1⟩) e2))
  · exact GlobalTheory.Fc.Row.strengthen (fun _ _ _ _ _ t => ⟨t.1, t.2.2.2⟩) e3

end GlobalTheory.NLink
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_closure_at_prime : Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D _ _ _ => Extra D C CT) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  atlas_forward_decl GlobalTheory.NLink.linkN_at
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.NLink.CloseMem

theorem main : GlobalTheory.NLink.Hypotheses₂ → GlobalTheory.HeightCounting.HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → (AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NFacts.Facts (w.D Z) nch) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hPr hHt hPrN hW hS hL N S Γ hWit hNE hFacts hAt23
  obtain ⟨C, CT, hC, hEx⟩ := GlobalTheory.T.extra_bound_of_twisting_eigen_facts hPr
  have hTf := GlobalTheory.T.twisting_eigen_of_depth_zero_support hHt hPrN hW hS hL
  have hExM : AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NLink.Extra (w.D Z) C CT :=
    GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.HeightCounting.Up.Model.AtMem.and hFacts hTf)
      fun _ _ _ _ w Z _ _ _ nch _ _ h => hEx (w.D Z) nch h.1 h.2
  have hTr := (GlobalTheory.Mem.AtPtTransport.atMem_at_wit hL N S Γ hWit hNE).2
  exact GlobalTheory.T.row_closure_at_prime hPr hL (prmR N S Γ) C CT hC
    (hTr (fun D nch => GlobalTheory.NFacts.Facts D nch) hFacts)
    (hTr (fun D _ => GlobalTheory.NLink.Extra D C CT) hExM) hAt23

end GlobalTheory.NLink.CloseMem
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_at_of_nonempty_exceptional : GlobalTheory.NLink.Hypotheses₂ → GlobalTheory.HeightCounting.HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → (AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NFacts.Facts (w.D Z) nch) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  atlas_forward_decl GlobalTheory.NLink.CloseMem.main
end

section
noncomputable section

namespace GlobalTheory.NLink.Final

section Slot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem movable_pin (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (Γ : GeoP) :
    PositionMv (prmR (NEl hL cDep) SExt.none (geoCl Γ)).s := by
  intro K B f T w Z O x N h O' hO' col n
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨nch', xd', -, hnx, -, -, hmv⟩ := GlobalTheory.T.exists_kept_choice_upper_lattice hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, c.2, ⟨hlp⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩

end Slot

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts

theorem main : GlobalTheory.NLink.Hypotheses₂ → PrN → GlobalTheory.NRows.HypothesesX → SerN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ), RL.At (prm1 hL cDep) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prm1 hL cDep) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP prN hX serN dzw dzs lf ltd lec hL cDep hAt
  have hF := GlobalTheory.T.facts_at_membership prN hX serN dzw dzs lf ltd lec hL
  have hW : WitMv (prmR (NEl hL cDep) SExt.none (geoCl anyGeometry)).s :=
    GlobalTheory.T.witnesses_pass_along_set_division _ (movable_pin hL cDep anyGeometry)
  exact GlobalTheory.T.residual_at_of_nonempty_exceptional hP hX.ht prN dzw dzs hL (NEl hL cDep) SExt.none (geoCl anyGeometry) hW
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ e => ⟨e.1⟩) hF hAt

end GlobalTheory.NLink.Final

end
end
