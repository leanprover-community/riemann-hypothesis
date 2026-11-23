module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianPrimeDerivations
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyDerivationsDetectSquare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCotangentBasisInPrime
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationMinorOfDetection
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGeneratorsClearDenominators
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
import Mathlib.RingTheory.SimpleRing.Principal
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem JacobianPrimeDerivations.proof (hDetect : PolyDerivationsDetectSquare.Statement)
    (hBasis : CotangentBasisInPrime.Statement) (hMinor : DerivationMinorOfDetection.Statement)
    (hClear : LocalGeneratorsClearDenominators.Statement) : JacobianPrimeDerivations.Statement := by
  intro k _ n p hp
  obtain ⟨h, f, hfp, hspan, hind⟩ := hBasis (MvPolynomial (Fin n) k) p
  obtain ⟨D, hD⟩ := hMinor (MvPolynomial (Fin n) k) p h f hfp hind
    (fun g hg hDg => hDetect k n p g hg hDg)
  obtain ⟨s, hs, hsp⟩ := hClear (MvPolynomial (Fin n) k) p h f hfp hspan
  exact ⟨h, f, D, s, hfp, hs, hsp, hD⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
