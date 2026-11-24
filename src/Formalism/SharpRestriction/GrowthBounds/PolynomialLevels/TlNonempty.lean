module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.PlaneCoeff
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwiceValuationFactorialProduct
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlanePairsOnBlocksAt
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd

@[expose] public section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

instance tlNonempty {J r : ℕ} [NeZero J] [NeZero r] (nL : ZMod J → ℕ) : Nonempty (TL J nL r) :=
  ⟨⟨0, Sum.inr 0⟩⟩

def gT {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) : ℤ → TL J nL r :=
  Function.invFun (posTL Fr)

def Rn {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) {K : ℕ}
    {O : Type} [CommRing O] [IsDomain O] (A : MvPolynomial (ℤ × Fin K) O) : MvPolynomial (TL J nL r × Fin K) (KK O) :=
  rename (fun v : ℤ × Fin K => (gT Fr nL v.1, v.2)) (MvPolynomial.map (algebraMap O (KK O)) A)

end Formalism.MainNotions.NormalSetCounting
