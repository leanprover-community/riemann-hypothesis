module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ChoiceM
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ContinuousESp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.CpUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.GeomTr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.IsDecOfGlobLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LcLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LevInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.OffSec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RCountAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RIdent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RelIndexGlobNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockSA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Thin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EndoS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Enlarge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.HeckeEigenvaluesUnitaryOneFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.SeparatesUnitaryOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.StUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.HasOfSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigid
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.NeZeroOfFinprod
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.SpehSingleFactorEquiv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CuspidalMultiplicityOne
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem

@[expose] public section

open UpperTheory.V.Z.Tf UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.V.Z.Mult

theorem noData_free : NoData := fun _ _ _ _ hE _ hn _ π _ hd D h1 h2 _ h4 => h1 (SR.has_of_split hE hn π hd D h2 h4)

theorem compOf_free : CompOf := fun E _ _ _ hE n hn _ π _ hd σ hσ hun hae =>
  (UpperTheory.Gal.Desc.match_of UpperTheory.Gal.Desc.speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
    PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin hE hn π (GOne.unitOf E n hn π hd) σ hσ hun hae).3

theorem mult_free : Mult := by
  have hCount : CountAt := rCountAt compOf_free evalD cpUniq Asm.places
  have hEndo : EndoBlockS :=
    endoS
      (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor
        unitary_one_characters_separated_by_eigenvalues Asm.places)
      Asm.places (UpperTheory.Zero.ConvolutionTheory.EB.endoBlockG cuspReadI)
  have hIdent : Ident :=
    rIdent noData_free hCount geomTr UpperTheory.ConvolutionTheory.G2.g2s
      UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit
      hEndo stableBlockSA
  exact rMult hIdent hCount levTr geomTr levInd lcLev choiceM offSec muEx

end UpperTheory.V.Z.Mult
