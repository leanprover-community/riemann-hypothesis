import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStripsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfThetaStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBetaInvHeckeU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetLeftTransversalOfRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransversalLeftTranslateInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumEigenvectorBlockLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaDatumPresentationLevelNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqUnderOfIdemAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeOfIsIdemAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeUNuInvEqOneOfCong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongOneInvMulIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondESupConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdSumFixEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorFixedPrincipalCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorBlockLevelUnimodularEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomNonvanishingFromInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearCombinationLogBoundRealInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCompLeSumOfInjOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRatios
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StepRatioAbsVwProd
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LocalArcIntegralityOfCmNormalisedTrivialisation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RootsOfUnityDivisibility
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatchingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistenceOfThetaStatement

section
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem om_sum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem exists_bottom_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P (condE G.pl) 0 ∧ IsBlockLevel P (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χβ hβ χν hν hn
  have hd : Even (botBig D i j + botSmall D i j) := by
    obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
    exact ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  have had : botBig D i j ≤ botBig D i j + botSmall D i j := Nat.le_add_right _ _
  obtain ⟨e0, vac, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht _ _ (hd.mul_left (botBig D i j))
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 vac.1 h0 χβ χν
  have hm : condE G.pl ≠ ⊥ := condE_ne_bot _
  have hcop := GlobalTheory.FunObj.StdDatum.condE_isCoprime_conj G.pl
  have hnu : ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → W.chV'.f u = 1 := by
    rw [hW2]; exact GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong hL G i j χν hν
  obtain ⟨hi0, -⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j)
  obtain ⟨R, hR1, hR2'⟩ := GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) (congLev_le _ _) hi0
  have hR2 : ∀ k ∈ intG D (botBig D i j), ∃! r, r ∈ R ∧ CongOne D (condE G.pl) (r⁻¹ * k) := by
    intro k hk
    obtain ⟨r, ⟨hr, hrk⟩, hu⟩ := hR2' k hk
    refine ⟨r, ⟨hr, ((GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hrk).2⟩, fun r' ⟨hr', h'⟩ => hu r' ⟨hr', (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).2
      ⟨mul_mem (inv_mem (hR1 r' hr')) hk, h'⟩⟩⟩
  have hcv := GlobalTheory.FunObj.CosetTT.cosetV_mem_TT D δ hc (condE G.pl) hm 0 _ _ e0 vac.1
  have hfix : ∀ k ∈ intG D (botBig D i j), W.Om k 1 (stdSum W (condE G.pl) 0 R) = stdSum W (condE G.pl) 0 R := by
    intro k hk
    unfold stdSum
    rw [om_sum W k 1 R _ fun r _ => W.maps _ _ _ hcv]
    have e1 : ∀ r, W.Om k 1 (W.Om r 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) = W.Om (k * r) 1 (cosetV D δ (condE G.pl) 0 _ _ e0) := by
      intro r
      have := W.mul k r 1 1 _ hcv
      rw [mul_one] at this
      exact this.symm
    simp_rw [e1]
    refine GlobalTheory.sum_transversal_left_translate_invariant (intG D (botBig D i j)) (congLev D (condE G.pl) (botBig D i j)) R
      (fun g => W.Om g 1 (cosetV D δ (condE G.pl) 0 _ _ e0)) hR1 hR2' (fun r _ c hc' => ?_) k hk
    have := W.mul r c 1 1 _ hcv
    rw [mul_one] at this
    obtain ⟨hc1, hc2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hc'
    rw [this, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W (condE G.pl) hm hcop hnu 0 (by omega) c hc1 hc2]
  have hle : congLev D (condE G.pl) (botBig D i j + botSmall D i j) ≤
      blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.FunObj.StdDatum.mem_congLev_iff _ _ _ _).1 hk
    refine (GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ _).2 ⟨hk1, fun a b hb ha => ?_⟩
    have hab : a ≠ b := fun e => by rw [e] at ha; omega
    have := hk2 a b
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at this
  obtain ⟨hj0, hj1⟩ := GlobalTheory.congLev_relIndex_le D (condE G.pl) hm (botBig D i j + botSmall D i j)
  have hQ : 0 < levQ G.pl := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]; exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hm)
  let n : D.what₂.Tau → ℕ := fun τ => ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2).toNat
  have hwt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by
    intro τ
    rw [hW4, hW2, one_mul]
    obtain ⟨r, hr⟩ := χν.par τ
    have h1 := hn τ
    have h2 : ((χν.n τ - (botBig D i j + botSmall D i j : ℕ)) / 2) = r := by omega
    simp only [n, h2]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hpres : Pres D ⊤ δ (levQ G.pl) e0 (stdSum W (condE G.pl) 0 R) := by
    rw [← GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact GlobalTheory.T.standardTheta_datum_presentation_level_norm D δ t0 hc e0 vac had W _ hm hcop hb hnu R hR1 hR2 hfix
  have hidx_ne : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≠ 0 := fun h =>
    hj0 (Subgroup.relIndex_eq_zero_of_le_left hle h)
  have hidx_le : (blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)).relIndex
      (intG D (botBig D i j + botSmall D i j)) ≤ levQ G.pl ^ ((botBig D i j + botSmall D i j) ^ 2 + 4) := by
    refine (Subgroup.relIndex_le_of_le_left hle hj0).trans (hj1.trans ?_)
    rw [GlobalTheory.FunObj.NormLevel.absNorm_condE]
    exact Nat.pow_le_pow_right hQ (by omega)
  have heig := GlobalTheory.T.standardThetaDatum_eigenvector_blockLevel D δ t0 hc e0 vac had W _ hm hcop hnu R hR1 hR2 hfix
  let P : Pair D ⊤ δ t0 (levQ G.pl) :=
    { crv := hc
      pt0 := ht
      a := botBig D i j
      d := botBig D i j + botSmall D i j
      a_le := had
      d_even := hd
      e0 := e0
      vac := vac
      W := W
      n := n
      wt := hwt
      F := stdSum W (condE G.pl) 0 R
      pres := hpres
      fix := hfix
      J := blockLev D (condE G.pl) (botBig D i j + botSmall D i j) (botBig D i j)
      J_le := blockLev_le _ _ _
      idx_ne := hidx_ne
      idx_le := hidx_le
      eig := heig }
  refine ⟨P, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩, fun h => GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff _ _ _ _ h⟩
  · show W.chV.f x ^ W.ep = _
    rw [hW1, hW3, zpow_one, hβ]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW2, hW4, zpow_one, hν]

end GlobalTheory.FunObj.StdDatum

end
end

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottomPair_bigMember_reference_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χβ : HeckeU D (botBig D i j)), (∀ x, χβ.f x = (betaH G i j)⁻¹.1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P.a = botBig D i j ∧ P.d = botBig D i j + botSmall D i j ∧ HasChars P (betaH G i j)⁻¹ (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P (condE G.pl) 0 ∧ IsBlockLevel P (condE G.pl) (botBig D i j) := by
  atlas_forward_decl GlobalTheory.FunObj.StdDatum.exists_bottom_big
end

section
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall

open GlobalTheory.BotPairSmall in

theorem smallPair_exists : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (D.host.conj • condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L μ₀ i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L μ₀ i j) (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • condE G.pl) (botBig D i j) ∧ IsBlockLevel P' (condE G.pl) (botBig D i j) := by
  intro D T L sc μ₀ hL G hb δ t0 hc ht i j χα hα χν hν hn
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have hd : Even (botBig D i j + botSmall D i j) :=
    ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, hv, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht (botSmall D i j) (botBig D i j + botSmall D i j)
    (hd.mul_left _)
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 hv.1 h0 χα χν
  have hm := condE_ne_bot G.pl
  have hcop := GlobalTheory.FunObj.SqNum.condE_sup_conj G.pl
  have hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) →
      W.chV'.f u = 1 := by
    intro u hu h
    rw [hW2, hν, GlobalTheory.BotPairSmall.CondNu.nuH_inv_eq_one_of_cong hL G i j u hu h]
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.CongReps.exists_reps D (botSmall D i j) _ (conj_smul_ne_bot D hm)
  have hTT := GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hK := GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hS := GlobalTheory.StdSumFix.stdSum_fix_eig D δ _ _ e0 W _ _ hTT hK R hR1 hR2
  have hN := GlobalTheory.ModulusNorm.absNorm_condE G.pl
  have hidx := GlobalTheory.BotPairSmall.blockJ_relIndex D (condE G.pl) hm (botBig D i j) (botBig D i j + botSmall D i j)
  have hQ : 1 ≤ levQ G.pl := by
    rw [← hN]; exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 hm)
  have heig : ∀ h ∈ blockJ D (condE G.pl) (botBig D i j) (botBig D i j + botSmall D i j), ∃ c : ℂ, ‖c‖ = 1 ∧
      W.Om 1 h (∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j) (botSmall D i j)
        (botBig D i j + botSmall D i j) e0)) = c • ∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j)
          (botSmall D i j) (botBig D i j + botSmall D i j) e0) := by
    intro h hh
    obtain ⟨k, hk, c, hc1, e⟩ := GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl h hh
    exact ⟨c, hc1, hS.2 h k c hk e⟩
  refine ⟨{
      crv := hc, pt0 := ht, a := botSmall D i j, d := botBig D i j + botSmall D i j, a_le := Nat.le_add_left _ _,
      d_even := hd, e0 := e0, vac := hv, W := W,
      n := fun τ => ((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat, wt := ?_,
      F := ∑ r ∈ R, W.Om r 1 (cvec D δ (D.host.conj • condE G.pl) (botBig D i j) (botSmall D i j)
      (botBig D i j + botSmall D i j) e0),
      pres := GlobalTheory.T.conjugateModulus_standardTheta_presentation D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hb hcond (botBig D i j) rfl _ hN R hR1 hR2,
      fix := hS.1,
      J := blockJ D (condE G.pl) (botBig D i j) (botBig D i j + botSmall D i j),
      J_le := blockJ_le _ _ _ _,
      idx_ne := hidx.1,
      idx_le := hidx.2.trans (by rw [hN]; exact Nat.pow_le_pow_right hQ (by omega)),
      eig := heig }, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩,
    fun h => GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet _ _ _ _ h⟩
  · intro τ
    show 2 * (((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat : ℤ) = W.ep' * W.chV'.n τ - _
    rw [hW4, hW2]
    obtain ⟨r, hr⟩ := χν.par τ
    have := hn τ
    omega
  · show W.chV.f x ^ W.ep = _
    rw [hW3, zpow_one, hW1, hα]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW4, zpow_one, hW2, hν]

end GlobalTheory.BotPairSmall
end
end

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottomPair_smallMember_reference_tuple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc), IsCoprime (D.host.conj • condE G.pl) D.host.𝔟 → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L μ₀ i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L μ₀ i j) (nuH G μ₀ i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • condE G.pl) (botBig D i j) ∧ IsBlockLevel P' (condE G.pl) (botBig D i j) := by
  atlas_forward_decl GlobalTheory.BotPairSmall.smallPair_exists
end

section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.SqNum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem exists_isBottom_of_isCoprime (hL : L.Is μ₀) (G : GridData L sc)
    (hm : IsCoprime (condE G.pl) D.host.𝔟) (hm' : IsCoprime (D.host.conj • condE G.pl) D.host.𝔟) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' := by
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D ⊤ δ hδ).1
  refine ⟨δ, t0, fun i j => ?_⟩
  obtain ⟨χν, hν, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨χβ, hβ⟩ := exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := exists_heckeU_alphaH hL G i j
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_reference_tuple hL G hm hδ ht i j χβ hβ χν hν hw
  obtain ⟨P', h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_reference_tuple hL G hm' hδ ht i j χα hα χν hν hw
  exact ⟨P, P', ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

theorem exists_isBottom (hL : L.Is μ₀) (G : GridData L sc) (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' :=
  exists_isBottom_of_isCoprime hL G (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).1
    (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).2

end GlobalTheory.FunObj.SqNum
end
end

section
section
open GlobalTheory.SqTop Formalism.BasicNotions

namespace GlobalTheory.SqTop

theorem botEx_holds (_ : ∀ D, GlobalTheory.NormSum.Inp D) : BotEx := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  obtain ⟨δ, t0, h⟩ := GlobalTheory.FunObj.SqNum.exists_isBottom hL G ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  exact ⟨δ, t0, fun ij => h ij.1 ij.2⟩

end GlobalTheory.SqTop
end

open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairs_exist_baseTuple : (∀ D, GlobalTheory.NormSum.Inp D) → BotEx := by
  atlas_forward_decl GlobalTheory.SqTop.botEx_holds
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses : (∀ D, GlobalTheory.NormSum.Inp D) → BotExT := by
  first | exact @GlobalTheory.SqTop.botExT_holds | exact GlobalTheory.SqTop.botExT_holds | (intros; apply GlobalTheory.SqTop.botExT_holds <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp c_vp delta_vp a0 n_vp IsClassZetaVals)
open GlobalTheory.CMVal (OF IsBaseCond expIn)

namespace GlobalTheory.DenExist

section Field

variable {E : Type} [Field E] [NumberField E]

theorem finite_support (d s : ℕ) {I : Type} [Fintype I] (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : 𝔣 ≠ ⊥)
    (z : ClassGroup (OF E) → ℚ) :
    {l : ℕ | l.Prime ∧ (⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) ≠ 0}.Finite := by
  set A : Set ℕ := {l | l.Prime ∧ ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal} with hAdef
  have hA : A.Finite :=
    GlobalTheory.FunObj.SqNum.finite_primes_under (K := maximalRealSubfield E) (p := fun v => v.asIdeal ∣ 𝔣)
      (Ideal.finite_factors h𝔣)
  let B : Finset ℕ := (Finset.univ.biUnion fun C =>
    (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)).den.primeFactors) ∪ (discr E).natAbs.primeFactors
  refine (hA.union B.finite_toSet).subset ?_
  rintro l ⟨hl, hn⟩
  by_contra hc
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hc
  obtain ⟨hlA, hlB⟩ := hc
  apply hn
  have hv : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → ¬ v.asIdeal ∣ 𝔣 :=
    fun v h1 h2 => hlA ⟨hl, v, h2, h1⟩
  have ha0 : a0 𝔣 l = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro _ ⟨v, h1, rfl⟩
    simp [expIn, multiplicity_eq_zero.2 (hv v h1)]
  have hcv : c_vp 𝔣 l = 0 := by
    have hd : ¬ l ∣ (discr E).natAbs := fun h => hlB (Finset.mem_union_right _
      (Nat.mem_primeFactors.2 ⟨hl, h, by simpa using discr_ne_zero E⟩))
    rw [c_vp, if_neg (fun ⟨v, h1, h2⟩ => hv v h1 h2), delta_vp]
    simp [padicValInt, padicValNat.eq_zero_of_not_dvd hd]
  have hcE : cE_vp l z = 0 := by
    rw [cE_vp, ← bot_eq_zero, Finset.sup_eq_bot_iff]
    intro C _
    set q := z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)
    have hd : ¬ l ∣ q.den := fun h => hlB (Finset.mem_union_left _ (Finset.mem_biUnion.2
      ⟨C, Finset.mem_univ _, Nat.mem_primeFactors.2 ⟨hl, h, q.den_ne_zero⟩⟩))
    show (-padicValRat l q).toNat = 0
    rw [Int.toNat_eq_zero, padicValRat, padicValNat.eq_zero_of_not_dvd hd]
    simp
  simp [betaBound_vp, hcE, hcv, ha0, n_vp]

end Field

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem exists_denom (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hb : IsBaseCond (condF G.pl)) (i j : Fin D.R.m) (s : ℕ) (hs : 1 ≤ s) :
    ∃ n, IsDenom G i j s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite := by
  obtain ⟨⟨z, hz'⟩, -⟩ := @hz D.host.E _ _ hcm s hs
  refine ⟨fun l => ((⌈betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) z l / 12⌉₊ : ℕ) : ℝ),
    ⟨z, hz', fun l _ => rfl⟩, ?_⟩
  refine (finite_support D.host.d s (kap D sc.cGap i j s) (condF G.pl) hb.1 z).subset ?_
  rintro l ⟨hl, h⟩
  exact ⟨hl, fun h' => h (by simp only [h', Nat.cast_zero])⟩

theorem denEx (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hF : FieldDat) : DenEx := by
  obtain ⟨CF0, h⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, -, -, hb, -⟩ := h C hC D large₂ he hx hR T Lc μ₀ hL G
  exact fun i j s hs _ => exists_denom hz G hcm hb i j s hs

end GlobalTheory.DenExist

end
end

section
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw)

noncomputable section

namespace GlobalTheory.SqTop.OneSqProof

theorem vw_ratio_le {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e p q e0 h0 : ℕ)
    (he : e0 + p = e + q) (hle : e0 ≤ h0) (rq ζ γ zA zA' : K) (tk : Fin (p + q) → K) (ρ : ℤ → K) (a n0 : ℤ → ℝ)
    (er dl B : ℝ)
    (heq : rq * ∏ k ∈ range q, ρ ((e : ℤ) + k + 1) = ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k))
    (hρ0 : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ (h0 : ℤ) + p + q → ρ s ≠ 0)
    (hζ : ζ ≠ 0 ∧ vw w ζ = 0) (ht : ∀ k, tk k ≠ 0 ∧ |(vw w (tk k) : ℝ)| ≤ B) (hγ : γ ≠ 0) (hzA : zA ≠ 0)
    (hγv : (vw w γ : ℝ) ≤ vw w (zA * ∏ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s) + vw w zA' + 6 * dl)
    (her : 0 ≤ er)
    (hs : ∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q →
      0 ≤ a s ∧ 0 ≤ n0 s ∧ (vw w (ρ s) : ℝ) ≤ a s + er ∧ -(vw w (ρ s) : ℝ) ≤ a s + n0 s)
    (hsym : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) :
    rq ≠ 0 ∧ (vw w rq : ℝ) ≤ |(vw w zA : ℝ)| + |(vw w zA' : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) +
      ((2 * (h0 + p + q) : ℕ) : ℝ) * er + 6 * dl + ((p + q : ℕ) : ℝ) * B := by
  have hq0 : ∀ k ∈ range q, ρ ((e : ℤ) + k + 1) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hp0 : ∀ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hI0 : ∀ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s ≠ 0 := fun s hs => by
    rw [mem_Icc] at hs; exact hρ0 _ hs.1 (by omega)
  have hT : ∀ k ∈ (univ : Finset (Fin (p + q))), tk k ≠ 0 := fun k _ => (ht k).1
  have hPq := prod_ne_zero_iff.2 hq0
  have hPp := prod_ne_zero_iff.2 hp0
  have hPT := prod_ne_zero_iff.2 hT
  have hPI := prod_ne_zero_iff.2 hI0
  have hR : ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp
  have hrq : rq ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact hR heq.symm
  refine ⟨hrq, ?_⟩
  have hv := congrArg (vw w) heq
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hrq hPq, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hq0,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hζ.1 hPT) hγ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hζ.1 hPT,
    Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hT, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hp0, hζ.2] at hv
  have hz := Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hzA hPI
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hI0] at hz
  rw [hz] at hγv
  have hc := GlobalTheory.Square.count_factors e p q e0 h0 he hle (fun s => (vw w (ρ s) : ℝ)) a n0 er her
    (fun s h1 h2 => hs s h1 h2) (fun s h1 h2 => by simp only [hsym s h1 h2])
  have hvR : (vw w rq : ℝ) + ∑ k ∈ range q, (vw w (ρ ((e : ℤ) + k + 1)) : ℝ) =
      (∑ k, (vw w (tk k) : ℝ)) + vw w γ + ∑ k ∈ range p, (vw w (ρ ((e : ℤ) + q - k)) : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hv
    push_cast at this
    linarith
  have hTB : (∑ k, (vw w (tk k) : ℝ)) ≤ ((p + q : ℕ) : ℝ) * B := by
    calc (∑ k, (vw w (tk k) : ℝ)) ≤ ∑ _k : Fin (p + q), B :=
          sum_le_sum fun k _ => (le_abs_self _).trans (ht k).2
      _ = ((p + q : ℕ) : ℝ) * B := by simp
  have hIc : ((∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), vw w (ρ s) : ℤ) : ℝ) =
      ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ) := by push_cast; rfl
  have hγv' : (vw w γ : ℝ) ≤ vw w zA + (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ)) + vw w zA' + 6 * dl := by
    have := hγv; push_cast at this; linarith
  have a1 := le_abs_self (vw w zA : ℝ)
  have a2 := le_abs_self (vw w zA' : ℝ)
  linarith

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem wt_at {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ} {l : ℕ}
    (hS : ∀ l' ∈ S, l'.Prime) (hl : l.Prime) (hw : (l : 𝓞 K) ∈ w.asIdeal) (hc : l ∉ S → c l = 0) :
    Formalism.PairingDivisionLocalBalance.wt S c w = c l * (vw w (l : K) : ℝ) := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : l ∈ S
  · refine sum_eq_single_of_mem l h fun l' hl' hne => ?_
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp
  · rw [hc h, zero_mul]
    refine sum_eq_zero fun l' hl' => ?_
    have hne : l' ≠ l := fun e => h (e ▸ hl')
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp

theorem wt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ}
    (hc : ∀ l ∈ S, 0 ≤ c l) : 0 ≤ Formalism.PairingDivisionLocalBalance.wt S c w :=
  sum_nonneg fun l hl => mul_nonneg (hc l hl) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w l)

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem exists_prime_mem' {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar _))

end GlobalTheory.SqTop.OneSqProof

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop

namespace GlobalTheory.SqTop.OneSqProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SqTop.OneSqProof
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormPos

theorem norm_ne_zero_of_coord : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q), (∃ h T, P.coord h T ≠ 0) → P.norm ≠ 0 := by
  intro D hI δ t0 Q P h
  exact ((GlobalTheory.NormSum.RepInv.rep_indep D hI ⊤ δ t0 Q P.crv P.pt0 P P.level_pos).2.2.2.2 h).ne'

end GlobalTheory.NormPos
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaPair_norm_ne_zero_of_coord_ne_zero : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q), (∃ h T, P.coord h T ≠ 0) → P.norm ≠ 0 := by
  atlas_forward_decl GlobalTheory.NormPos.norm_ne_zero_of_coord
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqNoSmall

theorem oneSqSt_of_claims' : (∀ D, GlobalTheory.NormSum.Inp D) → LNe → TorEx → BotSmall → BotExT → NormBig → BotNe → TriEx → Tower → BotConst → Refl → RhoLow → OneSqSt := by
  intro hInp h1 h2 h3 h4 h5 h5' h6 h7 h8 h9 h10
  obtain ⟨c, hc⟩ := Model.gBig_and h1 (Model.gBig_and h2 (Model.gBig_and h3 (Model.gBig_and h4 (Model.gBig_and h5
    (Model.gBig_and h5' (Model.gBig_and h6 (Model.gBig_and h7 (Model.gBig_and h8 (Model.gBig_and h9 h10)))))))))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ₀ hL G => ?_⟩
  obtain ⟨H1, H2, H3, H4, H5, H5', H6, H7, H8, H9, H10⟩ := h C hC D large₂ a b r T Lc μ₀ hL G
  clear h hc h1 h2 h3 h4 h5 h5' h6 h7 h8 h9 h10
  intro W S ρ hstd hnum C' μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw hThA hSq w ij

  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := Model.tower_numbers ij.1 ij.2

  have hN0 : ∀ s : ℤ, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) → ∀ l ∈ Sd, 0 ≤ N0 ij s l := by
    intro s h1 h2 l hl
    obtain ⟨z, -, hz⟩ := (hSq.inside ij s.toNat (by omega) (by omega)).2
    have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
    rw [e] at hz
    rw [hz l ((hSq.den l).1 hl).1]
    positivity
  have hdl : 0 ≤ dl w := by
    obtain ⟨S', del, hE, -, -, e⟩ := hSq.int
    rw [e]; exact wt_nonneg w fun l _ => hE.2.1 l
  have hEr : 0 ≤ wt Se (fun l => 1 / (l : ℝ) ^ 2) w := wt_nonneg w fun l _ => by positivity
  have hlast : 0 ≤ ((D.R.m - 1 - ij.2 : ℕ) : ℝ) * (2 * ∑ q ∈ G.pl.S0, (condExp G.pl q : ℝ) *
      (vw w (Ideal.absNorm q.asIdeal : D.what₂.LL) : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sum_nonneg fun q _ =>
      mul_nonneg (Nat.cast_nonneg _) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w _)))
  by_cases hne : μ w = μ₀
  · rw [hne, hSq.rq_base ij, Formalism.DivisionValues.ValuationRepresentative.vw_one]
    refine ⟨one_ne_zero, ?_⟩
    have s1 : 0 ≤ ∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
        |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|) := sum_nonneg fun _ _ => by positivity
    have s2 : 0 ≤ ∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), wt Sd (N0 ij s) w := sum_nonneg fun s hs => by
      rw [mem_Icc] at hs; exact wt_nonneg w (hN0 s hs.1 hs.2)
    have s3 := mul_nonneg (Nat.cast_nonneg (2 * halfRank D ij.1 ij.2)) hEr
    rw [Int.cast_zero]
    have a1 := abs_nonneg (vw w (zA ij) : ℝ)
    have a2 := abs_nonneg (vw w (zA' ij) : ℝ)
    linarith

  · set t := μ w with ht
    obtain ⟨hQn, hThl⟩ := hThA w hne
    obtain ⟨l, hl, hlw⟩ := exists_prime_mem' w
    obtain ⟨HL1, HL2⟩ := H1 ij.1 ij.2
    obtain ⟨Λ, hΛ, hΛne⟩ := HL1 t
    obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := HL1 μ₀
    obtain ⟨Λd, hΛd, hΛdne⟩ := HL2 (some (ch w))
    have hΛd' : IsHeckeL (nuH G μ₀ ij.1 ij.2 * Lc.C.delAt l) Λd := by
      rw [← hSq.delOf_ch hl hlw]; exact hΛd
    have hTd : ∀ s : ℕ, 1 ≤ s → s ≤ halfRank D ij.1 ij.2 →
        D.what₂.embLL (zTd ij (ch w) s) * Λ₀ s = Λd s ∧ Λd s ≠ 0 := by
      intro s h1' h2'
      obtain ⟨x, hx, hx0, hxc, -⟩ := (hSq.inside ij s h1' h2').1
      obtain ⟨y, hy, hy0, hyΛ, -⟩ := H2 ij.1 ij.2 s h1' h2' none
      obtain ⟨y', hy', hy'0, hy'Λ, -⟩ := H2 ij.1 ij.2 s h1' h2' (some (ch w))
      have e1 : x = y := hx.2.unique hy.2
      have e2 : D.what₂.embLL (zTd ij (ch w) s) * x = y' := (hxc (ch w)).2.unique hy'.2
      rw [← hyΛ Λ₀ hΛ₀, ← hy'Λ Λd hΛd, ← e1]
      exact ⟨e2, e2 ▸ hy'0⟩
    have hzψ : ∀ s : ℤ, ∃ z : D.what₂.LL, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) →
        D.what₂.embLL z * Λ₀ s = Λ s := by
      intro s
      by_cases hs : 1 ≤ s ∧ s ≤ (halfRank D ij.1 ij.2 : ℤ)
      · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        have h0 : Λ₀ s ≠ 0 := hΛ₀ne s (by omega) hs.2
        obtain ⟨z, hz⟩ := hnum.ratios ij.1 ij.2 t Λ Λ₀ hΛ hΛ₀ s.toNat (by omega) (by omega) (by rw [e]; exact h0)
        refine ⟨z, fun _ _ => ?_⟩
        rw [hz, e, div_mul_cancel₀ _ h0]
      · exact ⟨0, fun h1' h2' => absurd ⟨h1', h2'⟩ hs⟩
    choose zψ hzψ using hzψ
    have hEp : ∀ s : ℤ, ∃ E : D.what₂.LL, 1 - (e0 D ij.1 ij.2 : ℤ) ≤ s → s ≤ 0 →
        GlobalTheory.Square.IsAwayUnit (Qn G t) E ∧
          Λ s * Λ₀ ((1 - s : ℤ) : ℂ) = D.what₂.embLL E * (Λ ((1 - s : ℤ) : ℂ) * Λ₀ s) := by
      intro s
      by_cases hs : 1 - (e0 D ij.1 ij.2 : ℤ) ≤ s ∧ s ≤ 0
      · obtain ⟨E, hE⟩ := H9 W S hnum ij.1 ij.2 t Λ Λ₀ hΛ hΛ₀ s hs.1 hs.2
        exact ⟨E, fun _ _ => hE⟩
      · exact ⟨0, fun h1' h2' => absurd ⟨h1', h2'⟩ hs⟩
    choose Ep hEp using hEp
    have hwSd : ∀ s, wt Sd (N0 ij s) w = N0 ij s l * (vw w (l : D.what₂.LL) : ℝ) :=
      fun s => wt_at w (fun l' hl' => ((hSq.den l').1 hl').1) hl hlw fun h => by
        by_contra h'; exact h ((hSq.den l).2 ⟨hl, ij, s, h'⟩)
    have hwSe : wt Se (fun l => 1 / (l : ℝ) ^ 2) w = 1 / (l : ℝ) ^ 2 * (vw w (l : D.what₂.LL) : ℝ) :=
      wt_at w (fun l' hl' => ((hSq.err l').1 hl').1) hl hlw fun h => absurd ((hSq.err l).2 ⟨hl, w, hne, hlw⟩) h
    have hmid : ∀ s : ℤ, 1 ≤ s → s ≤ (halfRank D ij.1 ij.2 : ℤ) → zT ij s ≠ 0 ∧ zTd ij (ch w) s ≠ 0 ∧
        D.what₂.embLL (zψ s) * Λ₀ s = D.what₂.embLL (zT ij s) * Λ s ∧
        -(wt Sd (N0 ij s) w) ≤ ((vw w (zψ s) + gT ij s w : ℤ) : ℝ) ∧
        (vw w (zψ s) : ℝ) ≤ (vw w (zTd ij (ch w) s) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w := by
      intro s h1' h2'
      have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg (by omega)
      have eC : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by rw [← Int.cast_natCast, e]
      obtain ⟨hTd1, hTd2⟩ := hTd s.toNat (by omega) (by omega)
      rw [eC, e] at hTd1
      rw [eC] at hTd2
      have hψ := hzψ s h1' h2'
      have hTd0 : zTd ij (ch w) s ≠ 0 := fun h0 => hTd2 (by rw [← hTd1, h0, map_zero, zero_mul])
      have hψ0 : zψ s ≠ 0 := fun h0 => hΛne s (by omega) h2' (by rw [← hψ, h0, map_zero, zero_mul])
      refine ⟨by rw [hSq.base]; exact one_ne_zero, hTd0, by rw [hSq.base, map_one, one_mul]; exact hψ, ?_, ?_⟩
      · have hin := hSq.inside ij s.toNat (by omega) (by omega)
        have := H10 ij.1 ij.2 s.toNat (by omega) (by omega) t Λ Λ₀ (zψ s) _ _ _ hΛ hΛ₀ (by rw [eC]; exact hψ)
          hin.1 hin.2 w l hl hlw hQn
        rw [e] at this
        rw [hwSd]; exact this
      · have hz := hThl l hl hlw ij.1 ij.2 s.toNat Λ Λd (zψ s / zTd ij (ch w) s) (by omega) (by omega) hΛ hΛd' (by
          rw [eC, ← hTd1, ← hψ, map_div₀]; field_simp [(map_ne_zero _).2 hTd0])
        have hv := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (zψ s / zTd ij (ch w) s) (zTd ij (ch w) s) (div_ne_zero hψ0 hTd0) hTd0
        rw [div_mul_cancel₀ _ hTd0] at hv
        rw [hwSe, hv]
        have : (vw w (l : D.what₂.LL) : ℝ) / (l : ℝ) ^ 2 = 1 / (l : ℝ) ^ 2 * (vw w (l : D.what₂.LL) : ℝ) := by ring
        push_cast
        linarith
    obtain ⟨rr, hr1, hr2, hr3⟩ := GlobalTheory.Square.Ratio.exists_ratios D.what₂.LL D.what₂.embLL w (Qn G t) hQn
      (e0 D ij.1 ij.2) (halfRank D ij.1 ij.2) (by omega) (fun s => Λ₀ s) (fun s => Λ s) (zT ij) (zTd ij (ch w)) zψ Ep
      (fun s => gT ij s w) (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w)
      (fun s h1' h2' => ⟨hΛ₀ne s h1' h2', hΛne s h1' h2'⟩) hmid (fun s h1' h2' => hEp s h1' h2')

    have hrat : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D ij.1 ij.2 → Λ (n : ℂ) / Λ₀ (n : ℂ) = D.what₂.embLL (rr n) := by
      intro n h1' h2'
      have := (hr1 n (by omega) (by omega)).2
      have h0 := hΛ₀ne n (by omega) (by omega)
      simp only [Int.cast_natCast] at this h0
      rw [← this, mul_div_cancel_right₀ _ h0]
    obtain ⟨cf, hcf0, hcf⟩ := hSq.ratio ij
    obtain ⟨sn, sc, hrq⟩ := hcf t (Or.inr ⟨w, ht.symm⟩)
    obtain ⟨sn₀, sc₀, -⟩ := hcf μ₀ (Or.inl rfl)
    obtain ⟨A₁, A₁', WW, X, c0, hX, hXc⟩ := H6 W hstd ij.1 ij.2
    obtain ⟨u, hu, ζ, hζ, hT⟩ := H7 W S ρ hstd hnum ij.1 ij.2 t (cf t) (cf μ₀) A₁ A₁' WW X c0 Λ Λ₀ sn sc sn₀ sc₀ hX hXc
      hΛ hΛ₀
    obtain ⟨δ, t0, hN⟩ := hSq.norms
    obtain ⟨P₀, P₀', hB₀, hzA, hzA'⟩ := hN ij
    obtain ⟨P, P', hB⟩ := H4 δ t0 (levQ G.pl) P₀ t ij.1 ij.2
    have hmod : modT G μ₀ = SqNum.condE G.pl := (Model.base_tuple G hL).2.2
    have hB₀' : IsBottom G μ₀ ij.1 ij.2 (modT G μ₀) P₀ P₀' := by rw [hmod]; exact hB₀
    obtain ⟨A, hA, hNA⟩ := H5 δ t0 ij.1 ij.2
    have eP := hNA t _ P P' Λ hB hΛ
    have eP₀ := hNA μ₀ _ P₀ P₀' Λ₀ hB₀' hΛ₀
    have hIcc : ∀ s ∈ Icc (1 - (e0 D ij.1 ij.2 : ℤ)) (h0 D ij.1 ij.2 : ℤ),
        1 - (e0 D ij.1 ij.2 : ℤ) ≤ s ∧ s ≤ (halfRank D ij.1 ij.2 : ℤ) := fun s hs => by
      rw [mem_Icc] at hs; omega
    set z : D.what₂.LL := zA ij * ∏ s ∈ Icc (1 - (e0 D ij.1 ij.2 : ℤ)) (h0 D ij.1 ij.2 : ℤ), rr s with hzdef
    have hz : D.what₂.embLL z = (P.norm : ℂ) := by
      rw [eP, hzdef, map_mul, hzA, eP₀, map_prod, mul_assoc, ← prod_mul_distrib]
      congr 1
      refine prod_congr rfl fun s hs => ?_
      obtain ⟨a1, a2⟩ := hIcc s hs
      rw [mul_comm]; exact (hr1 s a1 a2).2
    have hzne : z ≠ 0 := by
      intro h0
      have : (P.norm : ℂ) = 0 := by rw [← hz, h0, map_zero]
      rw [eP] at this
      refine mul_ne_zero hA (prod_ne_zero_iff.2 fun s hs => ?_) this
      obtain ⟨a1, a2⟩ := hIcc s hs
      exact hΛne s a1 a2
    have hzAne : zA ij ≠ 0 := by
      intro h0
      have : (P₀.norm : ℂ) = 0 := by rw [← hzA, h0, map_zero]
      rw [eP₀] at this
      refine mul_ne_zero hA (prod_ne_zero_iff.2 fun s hs => ?_) this
      obtain ⟨a1, a2⟩ := hIcc s hs
      exact hΛ₀ne s a1 a2
    have hz'ne : zA' ij ≠ 0 := by
      intro h0
      have hne' : P₀'.norm ≠ 0 := GlobalTheory.T.definiteThetaPair_norm_ne_zero_of_coord_ne_zero D (hInp D) δ t0 (levQ G.pl) P₀' (H5' δ t0 (levQ G.pl) P₀ P₀' ij.1 ij.2 hB₀).2
      have : (P₀'.norm : ℂ) = 0 := by rw [← hzA', h0, map_zero]
      exact hne' (by exact_mod_cast this)
    obtain ⟨γ, hγ0, hc00, hγc, hγv⟩ := H8 W S hstd hnum ij.1 ij.2 t A₁ A₁' WW X c0 δ t0 P₀ P₀' P P' z (zA' ij) C' dl
      hX hXc hB₀ hB hz hzA' hzne hz'ne hSq.int
    have hS0 : ∀ v ∈ G.pl.S0, 0 < Ideal.absNorm v.asIdeal := fun v _ =>
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    have htk := fun k => GlobalTheory.Square.stepRatio_vw_bound D.what₂.LL D.what₂.embLL w (Qn G t) hQn _ G.pl.S0
      (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) hS0 (u k) 1 (hu k)
    choose tk htk0 htku htkv using htk
    obtain ⟨hζ0, hζv⟩ := hζ.ne_zero_and_vw w hQn

    have hq' : ∏ k ∈ range (qq D ij.2), Λ ((eTop D ij.1 ij.2 + k + 1 : ℕ) : ℂ) / Λ₀ ((eTop D ij.1 ij.2 + k + 1 : ℕ) : ℂ) =
        D.what₂.embLL (∏ k ∈ range (qq D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + k + 1)) := by
      rw [map_prod]
      refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [hrat _ (by omega) (by omega)]
      push_cast; rfl
    have hp' : ∏ k ∈ range (pp D ij.2), Λ ((eTop D ij.1 ij.2 + qq D ij.2 - k : ℕ) : ℂ) /
        Λ₀ ((eTop D ij.1 ij.2 + qq D ij.2 - k : ℕ) : ℂ) =
        D.what₂.embLL (∏ k ∈ range (pp D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + qq D ij.2 - k)) := by
      rw [map_prod]
      refine prod_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      rw [hrat _ (by omega) (by omega)]
      rw [Nat.cast_sub (by omega)]
      push_cast; rfl
    have hc0 : cf μ₀ ≠ 0 := hcf0
    have e1 : cf t / cf μ₀ = D.what₂.embLL (rq t ij) := by rw [← hrq, mul_div_cancel_right₀ _ hc0]
    have e2 : c0 t / c0 μ₀ = D.what₂.embLL γ := by rw [← hγc, mul_div_cancel_right₀ _ hc00]
    have e3 : ∏ k, u k = D.what₂.embLL (∏ k, tk k) := by
      rw [map_prod]; exact prod_congr rfl fun k _ => by rw [htku k, mul_one]
    rw [e1, e2, e3, hq', hp'] at hT
    have heqLL : rq t ij * ∏ k ∈ range (qq D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + k + 1) =
        ζ * (∏ k, tk k) * γ * ∏ k ∈ range (pp D ij.2), rr ((eTop D ij.1 ij.2 : ℤ) + qq D ij.2 - k) := by
      apply D.what₂.embLL.injective
      simp only [map_mul]
      exact hT
    have key := vw_ratio_le w (eTop D ij.1 ij.2) (pp D ij.2) (qq D ij.2) (e0 D ij.1 ij.2) (h0 D ij.1 ij.2) n1 n5.le
      (rq t ij) ζ γ (zA ij) (zA' ij) tk rr
      (fun s => |((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| + |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)
      (fun s => wt Sd (N0 ij s) w) (wt Se (fun l => 1 / (l : ℝ) ^ 2) w) (dl w)
      (2 * ∑ v ∈ G.pl.S0, (condExp G.pl v : ℝ) * (vw w (Ideal.absNorm v.asIdeal : D.what₂.LL) : ℝ))
      heqLL (fun s h1' h2' => (hr1 s h1' (by rw [n2]; push_cast; omega)).1) ⟨hζ0, hζv⟩ (fun k => ⟨htk0 k, htkv k⟩)
      hγ0 hzAne (hγv w hQn) hEr (fun s h1' h2' => by
        have h2'' : s ≤ (halfRank D ij.1 ij.2 : ℤ) := by rw [n2]; push_cast; omega
        obtain ⟨b1, b2⟩ := hr2 s h1' h2''
        refine ⟨by positivity, wt_nonneg w (hN0 s h1' h2''), b1, ?_⟩
        have := abs_nonneg ((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)
        linarith) hr3
    rw [n2, ← n3]
    exact key

end GlobalTheory.SqTop.OneSqNoSmall

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_ratio_valuation_without_norm_formula : (∀ D, GlobalTheory.NormSum.Inp D) → LNe → TorEx → BotSmall → BotExT → NormBig → BotNe → TriEx → Tower → BotConst → Refl → RhoLow → OneSqSt := by
  atlas_forward_decl GlobalTheory.SqTop.OneSqNoSmall.oneSqSt_of_claims'
end

section
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.NormTower

open IntermediateField

theorem abs_norm_coeff_zero_pow (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X])
    (h : GlobalTheory.FunObj.SqNum.IsMinPol σ β p) (hβ : IsAlgebraic ℚ β) :
    |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree =
      |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  obtain ⟨hm, hirr, hev⟩ := h
  haveI := Fact.mk hirr
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot p) := pb.finite
  haveI : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans K (AdjoinRoot p)
  set r := AdjoinRoot.root p
  have hNK : Algebra.norm K r = (-1) ^ p.natDegree * p.coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hm, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at this
  let φ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ β hev
  have hφ : φ r = β := AdjoinRoot.lift_root hev
  have hmin : minpoly ℚ r = minpoly ℚ β := by
    rw [← hφ]; exact (minpoly.algHom_eq φ.toRatAlgHom φ.injective r).symm
  have hint : IsIntegral ℚ r := .of_finite ℚ r
  have h1 : Algebra.norm ℚ r = Algebra.norm ℚ ((-1) ^ p.natDegree * p.coeff 0 : K) := by
    rw [← hNK, Algebra.norm_norm]
  have h2 := Algebra.norm_eq_norm_adjoin ℚ r
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ r) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  have hdeg : Module.finrank ℚ (AdjoinRoot p) = p.natDegree * Module.finrank ℚ K := by
    rw [← Module.finrank_mul_finrank ℚ K (AdjoinRoot p), pb.finrank, AdjoinRoot.powerBasis_dim, mul_comm]
  have hdeg2 : Module.finrank ℚ (AdjoinRoot p) = (minpoly ℚ β).natDegree * Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮r⟯ (AdjoinRoot p), IntermediateField.adjoin.finrank hint, hmin]
  have hn1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]; simp
  have key : |Algebra.norm ℚ (p.coeff 0)| = |(minpoly ℚ β).coeff 0| ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    have e := congrArg abs (h1.symm.trans (h2.trans (congrArg (· ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p)) h3)))
    rw [map_mul, map_pow, abs_mul, abs_pow, hn1, one_pow, one_mul, abs_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul] at e
    exact e
  rw [key, ← pow_mul, mul_comm, ← hdeg2, hdeg]

end GlobalTheory.NormTower
end

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → IsAlgebraic ℚ β → |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree = |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  atlas_forward_decl GlobalTheory.NormTower.abs_norm_coeff_zero_pow
end

section
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory

theorem meanInf_log_norm_embedding (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : K) (ha : a ≠ 0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) a
  have hmult : ∀ v : InfinitePlace K, v.mult = 2 := fun v => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
  have hpos : ∀ v : InfinitePlace K, 0 < v a := fun v => by
    rw [InfinitePlace.pos_iff]; exact ha
  have hsum : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log (v a) := by
    rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← hprod, Real.log_prod]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [hmult, Real.log_pow]; push_cast; ring
    · intro v _; exact pow_ne_zero _ (hpos v).ne'
  have he : ∀ v : InfinitePlace K, ‖v.embedding a‖ = v a := fun v => InfinitePlace.norm_embedding_eq v a
  simp only [he]
  rw [hsum, ← Finset.mul_sum]
  ring

end GlobalTheory
end

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : K), a ≠ 0 → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  atlas_forward_decl GlobalTheory.meanInf_log_norm_embedding
end

section
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum.LowVal

theorem coeff_zero_mul_pow_mem {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {β : ℂ} {p : K[X]}
    (h : IsMinPol σ β p) {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral ℤ ((c : ℂ) * β)) :
    ∃ a : 𝓞 K, p.coeff 0 * (c : K) ^ p.natDegree = (a : K) := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hβ : IsIntegral K β := ⟨p, h.1, h.2.2⟩
  have es : (c : K) • β = (c : ℂ) * β := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
  have hγ : IsIntegral (𝓞 K) ((c : K) • β) := by
    rw [es]; exact hc.tower_top
  have e1 := IsIntegrallyClosed.minpoly_smul (R := K) hc0 hβ
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' K hγ
  rw [← h.eq_minpoly] at e1
  refine ⟨(minpoly (𝓞 K) ((c : K) • β)).coeff 0, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, ← coeff_map, ← e2, e1, coeff_scaleRoots, Nat.sub_zero]

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] {w : Formalism.PairingDivisionLocalBalance.Pl K} {l n : ℕ} (hn : n.Coprime l)
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro h
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using hw))

theorem vw_coeff_zero_ge : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ),
    GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) →
    ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  intro K _ _ _ σ β p l N h hl ⟨n, hn, hi⟩ w hw
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.1 hn)
  have hc : IsIntegral ℤ (((n * l ^ N : ℕ) : ℂ) * β) := by
    convert hi using 1
    push_cast
    rw [zpow_natCast]
    ring
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hn0' : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hc0 : ((n * l ^ N : ℕ) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hn0' (pow_ne_zero _ hl0)
  obtain ⟨a, ha⟩ := coeff_zero_mul_pow_mem h hc0 hc
  have h1 : 0 ≤ vw w (p.coeff 0 * ((n * l ^ N : ℕ) : K) ^ p.natDegree) := by
    rw [ha]; exact Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w a
  have hvn : vw w (n : K) = 0 := by
    have := Formalism.DivisionValues.ReductionFirst.vw_unit w (n : 𝓞 K) (natCast_not_mem hn hw)
    simpa using this
  have hvl := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
  by_cases hp0 : p.coeff 0 = 0
  · rw [hp0, Formalism.DivisionValues.ValuationRepresentative.vw_zero]
    have : (0 : ℤ) ≤ ((N * p.natDegree : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  · rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hp0 (pow_ne_zero _ hc0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hc0] at h1
    push_cast at h1
    rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hn0' (pow_ne_zero _ hl0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hl0, hvn] at h1
    push_cast
    nlinarith

end GlobalTheory.FunObj.SqNum.LowVal
end

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  atlas_forward_decl GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge
end

section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_smul | exact GlobalTheory.FunObj.SqNum.meanVal_vw_smul | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_smul <;> assumption)
end

section
section
noncomputable section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
open GlobalTheory.FunObj.SqNum (IsMinPol meanVal_vw)

namespace GlobalTheory.HeightMeanValueBounds

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (w : Formalism.PairingDivisionLocalBalance.Pl K) : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  set n := Ideal.absNorm w.asIdeal with hn
  have h0 : n ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (n : 𝓞 K) ∈ w.asIdeal := Ideal.absNorm_mem _
  have e : ((n : ℕ) : 𝓞 K) = ∏ p ∈ n.primeFactors, ((p : 𝓞 K)) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self h0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast; rfl
  rw [e] at hmem
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, w.isPrime.mem_of_pow_mem _ hpw⟩

theorem height_meanVal [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (n : ℕ → ℕ) (A B : ℝ)
    (hp : IsMinPol σ β p) (hβ : β ≠ 0) (halg : IsAlgebraic ℚ β)
    (hlow : ∀ l, l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ ((12 * n l : ℕ) : ℤ) * β))
    (harch : Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ (minpoly ℚ β).natDegree * (12 * A))
    (hden : ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (n l : ℝ) * Real.log l ≤ B) :
    (Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |meanVal_vw w p / 12|).Finite ∧
      ∑ᶠ w : Formalism.PairingDivisionLocalBalance.Pl K, lw w * |meanVal_vw w p / 12| ≤ A + 2 * B := by
  obtain ⟨ha0, hd0⟩ := hp.ne_zero hβ
  set a := p.coeff 0 with ha
  set d := p.natDegree with hd
  have hfin : {w : Formalism.PairingDivisionLocalBalance.Pl K | vw w a ≠ 0}.Finite := by
    have := Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a))
    simpa [vw] using this
  set S : Finset ℕ := (GlobalTheory.FunObj.SqNum.finite_primes_under (p := fun w => vw w a ≠ 0) hfin).toFinset with hSdef
  have hS : ∀ l ∈ S, l.Prime := fun l hl => by
    rw [hSdef, Set.Finite.mem_toFinset] at hl; exact hl.1
  set N0 : ℕ → ℝ := fun l => ((12 * n l * d : ℕ) : ℝ) with hN0
  have hwt : ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, 0 ≤ Formalism.PairingDivisionLocalBalance.wt S N0 w := fun w =>
    Finset.sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l)
  have hlowv : ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, -(Formalism.PairingDivisionLocalBalance.wt S N0 w) ≤ ((vw w a : ℤ) : ℝ) := by
    intro w
    by_cases h : vw w a = 0
    · rw [h]; simpa using hwt w
    · obtain ⟨l, hl, hlw⟩ := exists_prime_mem w
      have hlS : l ∈ S := by
        rw [hSdef, Set.Finite.mem_toFinset]; exact ⟨hl, w, h, hlw⟩
      have key := GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral K σ β p l (12 * n l) hp hl (hlow l hl) w hlw
      have h1 : N0 l * (vw w (l : K) : ℝ) ≤ Formalism.PairingDivisionLocalBalance.wt S N0 w :=
        Finset.single_le_sum (f := fun l => N0 l * (vw w (l : K) : ℝ))
          (fun l' _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l')) hlS
      have h2 : -(N0 l * (vw w (l : K) : ℝ)) ≤ (vw w a : ℝ) := by
        have : (-(((12 * n l * d : ℕ) : ℤ) * vw w (l : K)) : ℝ) ≤ (vw w a : ℝ) := by exact_mod_cast key
        simpa [hN0] using this
      linarith
  have HC := Formalism.PairingDivisionLocalBalance.height_bound_essential K a 1 0 1 (fun _ => 0) (fun w => vw w a) S N0 ha0 one_ne_zero
    (fun w => by simp [vw, FractionalIdeal.count_one]) (fun w => by simp) (fun w => by simp) (fun l _ => by positivity) hlowv
  have hm : Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding (a ^ 12 * ((1 : K) ^ 0)⁻¹)‖) =
      12 * Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) := by
    simp only [pow_zero, inv_one, mul_one, map_pow, norm_pow, Real.log_pow, Formalism.PairingDivisionLocalBalance.meanInf]
    rw [← Finset.mul_sum]; push_cast; ring
  rw [hm, GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div K a ha0] at HC

  set e := (minpoly ℚ β).natDegree with he
  have he0 : 0 < e := minpoly.natDegree_pos halg.isIntegral
  have hnorm := GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField K σ β p hp halg
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlogN : (e : ℝ) * Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      ((d * Module.finrank ℚ K : ℕ) : ℝ) * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| := by
    have := congrArg (fun x : ℚ => Real.log (x : ℝ)) hnorm
    simpa [Real.log_pow] using this
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have harch' : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K ≤ d * (12 * A) := by
    rw [div_le_iff₀ hK]
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have : (e : ℝ) * Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| ≤ e * (d * (12 * A) * Module.finrank ℚ K) := by
      rw [hlogN]; push_cast
      have := mul_le_mul_of_nonneg_left harch (by positivity : (0 : ℝ) ≤ d * Module.finrank ℚ K)
      nlinarith
    exact le_of_mul_le_mul_left this heR
  have hsum : ∑ l ∈ S, N0 l * Real.log l = 12 * d * ∑ l ∈ S, (n l : ℝ) * Real.log l := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; simp [hN0]; ring
  have hB := hden S hS
  have hmain : ∑ᶠ w : Formalism.PairingDivisionLocalBalance.Pl K, lw w * |((vw w a : ℤ) : ℝ)| ≤ 12 * d * (A + 2 * B) := by
    have := HC.2
    rw [hsum] at this
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    nlinarith
  have efun : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |meanVal_vw w p / 12|) =
      fun w => (12 * d : ℝ)⁻¹ * (lw w * |((vw w a : ℤ) : ℝ)|) := by
    funext w
    simp only [meanVal_vw, ← ha, ← hd]
    rw [div_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * 12)]
    field_simp
  rw [efun]
  have hsupp : (Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => (12 * d : ℝ)⁻¹ * (lw w * |((vw w a : ℤ) : ℝ)|)) =
      Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |((vw w a : ℤ) : ℝ)| :=
    by
      have h12 : (12 * d : ℝ)⁻¹ ≠ 0 := by positivity
      ext w; simp only [Function.mem_support, ne_eq, mul_eq_zero, h12, false_or]
  refine ⟨hsupp ▸ HC.1, ?_⟩
  rw [← mul_finsum]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hmain

theorem lw_nonneg [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) : 0 ≤ lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  exact div_nonneg (Real.log_nonneg this) (Nat.cast_nonneg _)

theorem htLe_of_real [StarRing K] (g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ) (y y' : Formalism.PairingDivisionLocalBalance.Pl K → ℝ) (z : K) (H : ℝ)
    (hg : ∀ w, g w = GlobalTheory.LeafRestExamples.truncZero (y w)) (hy' : ∀ w, y' w = vw w z + y w)
    (h1 : (Function.support fun w => lw w * |y w|).Finite) (h2 : (Function.support fun w => lw w * |y' w|).Finite)
    (s1 : ∑ᶠ w, lw w * |y w| ≤ H) (s2 : ∑ᶠ w, lw w * |y' w| ≤ H) :
    Formalism.PairingDivisionLocalBalance.HtLe g z (2 * H) := by
  have hb : ∀ w, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ lw w * |y' w| + lw w * |y w| := fun w => by
    rw [← mul_add, hg, hy']
    exact mul_le_mul_of_nonneg_left (GlobalTheory.LeafRestExamples.abs_truncZero_le (y w) (vw w z)).2 (lw_nonneg w)
  have hfin : (Function.support fun w => lw w * |y' w| + lw w * |y w|).Finite :=
    (h2.union h1).subset (Function.support_add _ _)
  refine ⟨hfin.subset fun w hw => ?_, ?_⟩
  · intro h; apply hw
    have := hb w
    have h0 : 0 ≤ lw w * |((vw w z + g w : ℤ) : ℝ)| := mul_nonneg (lw_nonneg w) (abs_nonneg _)
    simp only [Function.mem_support, ne_eq, not_not] at h ⊢
    linarith
  · calc ∑ᶠ w, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ ∑ᶠ w, (lw w * |y' w| + lw w * |y w|) :=
          finsum_le_finsum' (hfin.subset fun w hw => by
            intro h; apply hw
            have := hb w
            have h0 : 0 ≤ lw w * |((vw w z + g w : ℤ) : ℝ)| := mul_nonneg (lw_nonneg w) (abs_nonneg _)
            simp only [Function.mem_support, ne_eq, not_not] at h ⊢
            linarith) hfin (fun w => hb w)
      _ = ∑ᶠ w, lw w * |y' w| + ∑ᶠ w, lw w * |y w| := finsum_add_distrib h2 h1
      _ ≤ 2 * H := by linarith

end GlobalTheory.HeightMeanValueBounds

namespace GlobalTheory.SqTop
open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid in

theorem thbSt_of_inputs : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  intro hTD hFD hTor _ hDS hBA
  obtain ⟨F1, hF⟩ := hFD
  obtain ⟨F2, hT⟩ := hTor
  obtain ⟨F4, hS⟩ := hDS
  obtain ⟨F5, hB⟩ := hBA
  refine ⟨max F1 (max F2 (max F4 F5)), fun ε CF hCF => ?_⟩
  obtain ⟨hf1, hf2, hf4, hf5⟩ : F1 ≤ CF ∧ F2 ≤ CF ∧ F4 ≤ CF ∧ F5 ≤ CF := by simpa [max_le_iff] using hCF
  obtain ⟨C1, y1, h1⟩ := hF ε CF hf1
  obtain ⟨C2, y2, h2⟩ := hT ε CF hf2
  obtain ⟨C4, y4, h4⟩ := hS ε CF hf4
  obtain ⟨C5, y5, h5⟩ := hB ε CF hf5
  refine ⟨6 * max C1 (max C2 (max C4 C5)), max y1 (max y2 (max y4 y5)), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => ?_⟩
  have hC' : max C1 (max C2 (max C4 C5)) ≤ C / 6 := by linarith
  obtain ⟨hc1, hc2, hc4, hc5⟩ : C1 ≤ C / 6 ∧ C2 ≤ C / 6 ∧ C4 ≤ C / 6 ∧ C5 ≤ C / 6 := by simpa [max_le_iff] using hC'
  obtain ⟨hx1, hx2, hx4, hx5⟩ : y1 ≤ large₂.sc.x ∧ y2 ≤ large₂.sc.x ∧ y4 ≤ large₂.sc.x ∧ y5 ≤ large₂.sc.x := by simpa [max_le_iff] using hx
  have H1 := h1 (C / 6) hc1 D large₂ hε hx1 hR T Lc μ₀ hμ G
  have H2 := h2 (C / 6) hc2 D large₂ hε hx2 hR T Lc μ₀ hμ G
  have H4 := h4 (C / 6) hc4 D large₂ hε hx4 hR T Lc μ₀ hμ G
  have H5 := h5 (C / 6) hc5 D large₂ hε hx5 hR T Lc μ₀ hμ G
  dsimp only at H1 H2 H4 H5 ⊢
  intro i j s hs1 hs2 zd g hTV
  obtain ⟨hCM, hAb, hFDat, hBase, -⟩ := H1
  obtain ⟨z, hz, HD⟩ := hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hFDat hs1
  obtain ⟨x, hx, hx0, hxc, Λ, p, hΛ, hp, hg⟩ := hTV
  set B' := bTH D (C / 6) large₂.sc.x large₂.sc.b with hB'
  have hB6 : bTH D C large₂.sc.x large₂.sc.b = 2 * (B' + 2 * B') := by rw [hB']; unfold bTH; ring
  set n : ℕ → ℕ := fun l => ⌈GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l / 12⌉₊ with hn
  have hden : IsDenom G i j s (fun l => (n l : ℝ)) := ⟨z, hz, fun l _ => rfl⟩
  have hd0 : 0 < D.host.d := hFDat.1.pos
  have beta_ne : ∀ y : ℂ, y ≠ 0 → GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y ≠ 0 := by
    intro y hy
    unfold GlobalTheory.CMVal.beta
    refine div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hy)) (pow_ne_zero _ (Formalism.L2.Th1.F.discNeZero Λ))
    exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos D.host.E hd0 (by omega) _).ne'
  have tor_ne : ∀ c y, IsTor G i j s (fam G μ₀ i j c) y → y ≠ 0 ∧
      IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y) := by
    intro c y hty
    obtain ⟨y', hy', hy'0, -, halg⟩ := H2 i j s hs1 hs2 c
    obtain rfl : y' = y := hy'.2.unique hty.2
    exact ⟨hy'0, halg Λ hΛ⟩
  have fam_bd : ∀ (c : Option Bool) (y : ℂ) (q : D.what₂.LL[X]), IsTor G i j s (fam G μ₀ i j c) y →
      IsMinPol D.what₂.embLL (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y) q →
      (Function.support fun w => lw w * |meanVal_vw w q / 12|).Finite ∧
        ∑ᶠ w, lw w * |meanVal_vw w q / 12| ≤ B' + 2 * B' := by
    intro c y q hty hq
    obtain ⟨hy0, halg⟩ := tor_ne c y hty
    refine GlobalTheory.HeightMeanValueBounds.height_meanVal D.what₂.embLL _ q n B' B' hq (beta_ne y hy0) halg ?_
      (H5 i j s hs1 hs2 c y Λ hty hΛ) fun S hS => (H4 i j s hs1 hs2 _ hden S hS).2
    intro l hl
    have hT' : GlobalTheory.CMVal.IsToricSum (cmPhi D) s (kap D (1 : ℝ) i j s) (GlobalTheory.CMVal.condQ (condF G.pl) ∅)
        (fam G μ₀ i j c * 1) y := by
      simpa [GlobalTheory.CMVal.condQ] using hty.2
    have hv := ((HD (kap D (1 : ℝ) i j s) (condF G.pl) Λ (fam G μ₀ i j c) hBase hΛ hty.1 l hl ∅
      (by simp [GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor]) (by simp)).2 1 y ⟨fun _ => rfl, fun _ _ => rfl⟩ hT')
    have hle : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l ≤
        (((12 * n l : ℕ) : ℤ) : ℝ) / ((1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l / 12)
      simp only [hn] at *
      push_cast
      linarith
    simpa using hv ((12 * n l : ℕ) : ℤ) 1 one_pos hle
  obtain ⟨fin0, sum0⟩ := fam_bd none x p hx hp
  have hB0 : 0 ≤ B' := by
    have : 0 ≤ ∑ᶠ w, lw w * |meanVal_vw w p / 12| :=
      finsum_nonneg fun w => mul_nonneg (GlobalTheory.HeightMeanValueBounds.lw_nonneg w) (abs_nonneg _)
    linarith
  rw [hB6]
  refine ⟨GlobalTheory.HeightMeanValueBounds.htLe_of_real g _ _ 1 _ hg (fun w => by simp [vw, FractionalIdeal.count_one]) fin0 fin0 sum0 sum0,
    fun c => ?_⟩
  have hxc' : IsTor G i j s (fam G μ₀ i j (some c)) (D.what₂.embLL (zd c) * x) := hxc c
  obtain ⟨hy0, halg⟩ := tor_ne (some c) _ hxc'
  have hz0 : zd c ≠ 0 := fun h => hy0 (by simp [h])
  obtain ⟨qc, hqc⟩ := exists_isMinPol (σ := D.what₂.embLL) halg
  have e12 : GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ (D.what₂.embLL (zd c) * x) =
      D.what₂.embLL (zd c ^ 12) * GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ x := by
    unfold GlobalTheory.CMVal.beta; rw [map_pow]; ring
  have hqc' := hqc
  rw [e12] at hqc'
  have hmv := GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation D.what₂.LL D.what₂.embLL _ (zd c ^ 12) p qc hp hqc' (beta_ne x hx0) (pow_ne_zero _ hz0)
  obtain ⟨finc, sumc⟩ := fam_bd (some c) _ qc hxc' hqc
  refine ⟨hz0, GlobalTheory.HeightMeanValueBounds.htLe_of_real g _ _ (zd c) _ hg (fun w => ?_) fin0 finc sum0 sumc⟩
  rw [hmv w, Formalism.PairingDivisionLocalBalance.vw_pow w _ hz0]
  push_cast; ring

end GlobalTheory.SqTop
end
end

open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  atlas_forward_decl GlobalTheory.SqTop.thbSt_of_inputs
end

section
namespace GlobalTheory.SqTop

theorem join_claims : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  intro hHD hPr hFE hTD hTr hZD hRefl hTI hLM
  have hS := GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hF : FieldDat := GlobalTheory.SqTop.fieldDat
  have hL : LNe := GlobalTheory.SqTop.lNe_of_functionalEquation hFE hS hF
  have hLB : LBound := GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE hFE hS hF
  have hTor : TorEx := GlobalTheory.ToricExist.torEx hTr hF hL
  have hBA : BetaArch := GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport hTr hF hLB hTor
  have hDE : DenEx := GlobalTheory.DenExist.denEx hZD hF
  have hDS : DenSum := GlobalTheory.DenSumPf.denSum hZD hF
  have hThb : ThbSt := GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans hTD hF hTor hDE hDS hBA
  have hBS : BotSmall := GlobalTheory.SqTop.BotSmallProof.botSmall_holds
  have hBC : BotConst := GlobalTheory.T.bottom_constant_of_theta hPr hTI hLM hInp hBS hL
  have hBE : BotEx := GlobalTheory.T.bottomPairs_exist_baseTuple hInp
  have hBET : BotExT := GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses hInp
  have hNB : NormBig := GlobalTheory.T.norm_big_of_nonvanishing hPr hInp hL
  have hRL : RhoLow := GlobalTheory.T.lValueRatio_lower_bound_gauge hTD hF hTor
  have hTri : TriEx := GlobalTheory.T.triple_existence_of_theta hHD hPr hTI hLM hL
  have hBN : BotNe := GlobalTheory.T.bottom_nonvanishing_from_inputs hPr hTI hLM hInp hL hBS hNB hTri
  have hTw : Tower := GlobalTheory.T.tower_of_theta_matching hPr hTI hLM hL
  have hOne : OneSqSt := GlobalTheory.T.square_ratio_valuation_without_norm_formula hInp hL hTor hBS hBET hNB hBN hTri hTw hBC hRefl hRL
  exact ⟨hDS, hThb, hOne, hBS, hBN, hF, hTor, hDE, hBE, hL, hTri, hTw⟩

end GlobalTheory.SqTop
end
