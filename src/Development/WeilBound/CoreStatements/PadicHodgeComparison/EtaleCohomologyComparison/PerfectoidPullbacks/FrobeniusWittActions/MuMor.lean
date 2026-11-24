module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb.Mid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) {N : ℕ}

abbrev HM (M : Model l K) (n j : ℕ) : Type 1 := CH.H (B.OM (Lm r M n) ((base l).cris n)) j

def muMor (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    CH.Mor (B.OM (Lm r M n) ((base l).cris n)) (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n))
      (RingHom.id _) :=
  B.omMor (mIn r M n hT) (RingHom.id _) fun _ => rfl

def nuMor (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    CH.Mor (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) (B.OM (Lm r M n) ((base l).cris n)) (phiA l N) :=
  B.omMor (mOut r M n hT) (phiA l N) (phiP_cris n N)

def mu (M : Model l K) (n j : ℕ) (hT : TeichmullerCongruence r N) :
    HM r M n j →ₗ[Acris l] CH.H (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) j :=
  (muMor r M n hT).pull j

def nu (M : Model l K) (n j : ℕ) (hT : TeichmullerCongruence r N) :
    CH.H (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) j →ₛₗ[phiA l N] HM r M n j :=
  (nuMor r M n hT).pull j

end CrystallineSemistableComparison.Pb.Mid
