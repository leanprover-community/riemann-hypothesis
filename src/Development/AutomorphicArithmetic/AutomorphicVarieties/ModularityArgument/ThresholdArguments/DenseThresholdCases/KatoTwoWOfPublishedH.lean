module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.KatoTwoW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.WinPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfVanishOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.DecConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.IsFrobOfRs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphAtTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AlgNormDiag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobRoot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IrrOfTw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfNormVDvd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolarOfLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistNewform
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section




section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem locQ_of_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (hR : RowT) (hQ : Z.Bc.QuadBC2) : LocQ :=
  locQ plainRec plainOf recTExists (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.base_change_split_of_printed_quad_bc P hQ) potOf
    (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.local_k_of_printed_rec_compat_sph_frob P recTExists (compatTOf hR plainRec) plainRec (winPt Z.Gam.suppFacts Z.ImaginaryQuadraticEtaCharacter.winOf) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.recSph_alt P) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.recFrob_alt P))
theorem katoTwoW_of_printsH_of_rT_of_quadBC2 (P : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) (hQ : Z.Bc.QuadBC2) : KatoTwoW := by
  intro l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hW
  have hL := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ_of_alt P.toClassicalTheorems hR hQ
  obtain ⟨hdt, ha⟩ := u.adm hf
  refine twoS P.toClassicalTheorems.litN.coh (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt P (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew_alt P) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.frobRoot_alt P.toClassicalTheorems hL)) l Ω K e N θ ψ W u ι f hf ?_
  refine sphOfWit (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.twWit_alt P.toClassicalTheorems (_root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws Z.ImaginaryQuadraticEtaCharacter.winTw)) hL l u.l_odd Ω ι e u.e_pos W ha.cont
    (GlobalTheory.Ord2.IrrTransfer.isIrr_of_range W (W.comp (GlobalTheory.Ord2.H0g W).subtype) (fun s => ⟨(s : G ℚ Ω), rfl⟩) ha.irr) ?_ hW
  obtain ⟨M, hM, hMk⟩ := UpperTheory.V.CF.kwAbs Ω (GlobalTheory.Ord2.dt W).ker (GlobalTheory.Ord2.TwDet.ker_open ha.cont ha.det2)
    (Abelianization.commutator_subset_ker (GlobalTheory.Ord2.dt W))
  exact ⟨M, hM, fun s hs => hMk s hs⟩
theorem katoTwoW_of_printsH (P : _root_.UpperTheory.V.Af.HypothesesH') : KatoTwoW :=
  _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH_of_rT_of_quadBC2 P (_root_.UpperTheory.Gal.SV.rowOf' P.toClassicalTheorems.litN.aut.gal) UpperTheory.ConvolutionTheory.R2.quadBC2
end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
