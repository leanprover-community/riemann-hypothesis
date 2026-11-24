module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.CoverExistsOf
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.Development
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.EquivariantSections.KeyIdentityHolds
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.HilbertSpaceRealisationHolds
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.ExplicitFunctionSquareIntegrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.RgDs.B

theorem dsExists : GlobalTheory.Dec.DSExists := dsExists_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

theorem kTypesAbove : GlobalTheory.Dec.KTypesAbove := kTypesAbove_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

theorem dsInfChar : GlobalTheory.Dec.DSInfChar := CompanionTheory.RgDsInf.dsInfChar'

theorem discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists := upqExists_of dsExists

theorem discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists := exists_of dsExists

theorem discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists := coverExists_of dsExists

theorem classUsed : ClassUsed := classUsed_of dsExists kTypesAbove dsInfChar

end CompanionTheory.RgDs.B
