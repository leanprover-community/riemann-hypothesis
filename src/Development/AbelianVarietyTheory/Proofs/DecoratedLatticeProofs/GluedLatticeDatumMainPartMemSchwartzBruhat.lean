module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum qvec)

namespace GlobalTheory.FinPl.Comm

theorem mainDatum_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (ε : 𝓀[k]ˣ) (P : Pair k n') (Q : Pair k n) : mainDatum q χ ε P Q ∈ SB (Matrix n n' k) := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0}
  have h : mainDatum q χ ε P Q = ∑ f' : {f : Module.Dual 𝓀[k] (Red P.ker) // f ≠ 0},
      χ (-((ε : 𝓀[k]) * f'.1 (qvec q P))) • phiOne (ofDual P.ker f') Q := by
    funext x
    rw [mainDatum, finsum_eq_sum_of_fintype, Finset.sum_apply]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun f' _ => Submodule.smul_mem _ _ (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)

end GlobalTheory.FinPl.Comm
