module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DefQuatExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ClozelConjC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVPatch
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPCohC
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbsNormConj
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
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

@[expose] public section




section
open NumberField Formalism.GaloisCohomology UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Lit UpperTheory.V.Z.Bc
theorem published_hypotheses_from_patching_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (desc : Z.Desc.DescWeak) : _root_.UpperTheory.V.Af.HypothesesH' :=
  { litN := hN, cohC := _root_.UpperTheory.V.Af.clozelCohC_alt hN, conjC := Z.Coh.clozelConjC, borelC := Z.Coh.borelInjC,
    galR := _root_.UpperTheory.Gal.SV.galois_rep_exists_totally_real_rank_two_of_base_change hN UpperTheory.ConvolutionTheory.R2.quadBC2 admissibleReal, smoR := strongMultOneReal,
    gkR := gelfandKazhdanReal strongMultOneReal, admR := admissibleReal, bc := Br.quadBC0_of_two UpperTheory.ConvolutionTheory.R2.quadBC2,
    newform := newformRepOf cuspSemisimpleReal admissibleReal,
    descU := desc, cyc := cycC_holds, cyc2 := Or.inl UpperTheory.ConvolutionTheory.RankTwoDescent.descS, quat := defQuatExists, ssR := cuspSemisimpleReal }
end UpperTheory.V.HV.DescentVanishingReductions
end
