module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.AntitoneOfAppend
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.JointTypeLatticeSaturated
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

theorem nested_sets_lemma_of_admitted (D : Formalism.BasicNotions.D7) (h14 : JointComponentsPaths D) (h16 : PairedPathIndependence D) : ConclusionB3 D :=
  lemma_B3 D h16 (lemma_B2 D) (integral_joint_type_sum D h14 h16)

end Formalism.MainNotions.LemmaBAlt
