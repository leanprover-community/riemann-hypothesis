module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.LocalFields.FilteredSurj
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar partialLFunction coe_localChar continuous_localChar)
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.HeckePartial

end GlobalTheory.CompanionTheory.HeckePartial

end
