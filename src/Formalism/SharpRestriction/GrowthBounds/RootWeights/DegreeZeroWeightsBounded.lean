module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def casimirConjugation (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) : Module.End K (Module.End K V) :=
  ∑ i ∈ s, (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

def casimirPower (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (q : ℕ) : Module.End K V :=
  ((casimirConjugation E c s) ^ q) 1

def casimirPowerScaled (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) (b q : ℕ) : Module.End K V :=
  ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) • casimirPower E c s q

def extremalProjector (E : GLOps n K V) (c : Fin n) (L : ℕ) : Module.End K V :=
  ∑ q ∈ range (L + 1), ((-1 : K) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q

def DegreeZeroWeightsBounded (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ ν : Fin n → ℤ, (∑ a, ν a = 0) → weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (L : ℤ)

end Formalism.MainNotions.G.GLWeightTheory
