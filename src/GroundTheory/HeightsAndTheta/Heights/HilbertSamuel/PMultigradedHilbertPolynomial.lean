module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolynomial
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
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
import Mathlib.Order.CompletePartialOrder
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem MultigradedHilbertPolynomial.proof (h : EventualPolynomial.Statement) :
    MultigradedHilbertPolynomial.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim
  have hlt : ringKrullDim (MRing ι F ⧸ q) < (((d + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : d + Fintype.card K < d + 1 + Fintype.card K)
  have hdeg : DegLT (hilbFn q) (d + 1) :=
    HilbDegBound.full F K ι (d + 1) q hq.isPrime hq.multiHomog hlt
  exact h K d (hilbFn q) hdeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
