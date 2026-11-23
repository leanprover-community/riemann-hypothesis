module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInputStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCountStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem kleimanNef_field_and_fibre : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  have hF : KleimanNefFStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNefF.kleimanNef_field_of_alt (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNef.proof hF, hF⟩

end GlobalTheory.CompanionTheory.Ar.Giv
