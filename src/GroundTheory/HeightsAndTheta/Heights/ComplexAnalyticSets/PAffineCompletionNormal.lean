module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAffineCompletionNormal
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ArtinHenselCompletionNoetherian
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFD
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem adicCompletion_isLocalRing_of_isMaximal {A : Type*} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (fg : m.FG) : IsLocalRing (AdicCompletion m A) := by
  have := AdicCompletion.isMaximal_map_of_le m m le_rfl fg
  have := AdicCompletion.isAdicComplete_self m fg
  exact isLocalRing_of_isAdicComplete_maximal (m.map (algebraMap A (AdicCompletion m A)))

theorem AffineCompletionNormal.proof (hF : FlatNormalFibres.Statement) (hR : FormalFibresRegular.Statement) :
    AffineCompletionNormal.Statement := by
  intro σ _ I m hI hIC hm
  have : I.IsPrime := hI
  have : m.IsMaximal := hm
  have hloc := adicCompletion_isLocalRing_of_isMaximal m (Ideal.fg_of_isNoetherianRing m)
  refine hF (MvPolynomial σ ℂ ⧸ I) (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) inferInstance inferInstance hloc
    inferInstance inferInstance hIC fun P _ => ?_
  have := hR ℂ (MvPolynomial σ ℂ ⧸ I) inferInstance m hm P
  exact ⟨inferInstance, GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed _⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
