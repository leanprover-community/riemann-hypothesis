module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Basic

@[expose] public section

namespace GlobalTheory.LinearIndependentFixed

theorem linearIndepOn_of_fixed {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W]
    [Module.IsTorsionFree B W] (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), σ g (b • w) = a g b • σ g w)
    (hK : ∀ (b b' : B), b ≠ 0 → (∀ g : G, b * a g b' = a g b * b') →
      ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), σ g (v i) = v i)
    (s : Finset ι) (hs : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant <;> assumption

end GlobalTheory.LinearIndependentFixed
