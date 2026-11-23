module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleiman.AtDim (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M A : HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j ≤ d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

def MixedKleiman.LowAt (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M A : HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j < d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

def MixedKleiman.TopAt (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι))
    (M : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    0 ≤ II K ι P d (fun _ => M)

theorem MixedKleiman.atDim_zero : MixedKleiman.AtDim 0 := by
  intro K _ ι _ P P0 M A a II _ h1
  exact absurd h1 (by norm_num)

def MixedKleimanLow.Statement : Prop :=
  ∀ d : ℕ, MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
