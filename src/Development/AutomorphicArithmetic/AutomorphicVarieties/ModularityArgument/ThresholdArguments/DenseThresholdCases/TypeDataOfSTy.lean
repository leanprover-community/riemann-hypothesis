module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroGDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroKIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
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

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
abbrev _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty : Prop := ∀ (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp),
    _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt
end UpperTheory.NonzeroTypeTheory
end
end
