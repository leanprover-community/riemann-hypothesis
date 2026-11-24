module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open scoped Classical

namespace GlobalTheory.LoopV

open NumberField Matrix Formalism.MainNotions.S

variable {K : Type} [Field K] {N : ℕ}

def StrUp (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, j ≤ i → x i j = 0

def StrLo (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, i ≤ j → x i j = 0

def expT (x : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  ∑ i ∈ Finset.range N, ((i.factorial : K)⁻¹) • x ^ i

def stabU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {a | IsUpUni a ∧ IsLoUni (Z * a * Z⁻¹)}

def lieU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {x | StrUp x ∧ StrLo (Z * x * Z.adjugate)}

def roots (w : Matrix (Fin N) (Fin N) K) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ ∃ i j, j < i ∧ w i q.1 ≠ 0 ∧ w j q.2 ≠ 0

def ofRoots (R : Finset (Fin N × Fin N)) (c : R → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if h : (i, j) ∈ R then c ⟨(i, j), h⟩ else if i = j then 1 else 0

def EntIn [NumberField K] (I : Ideal (𝓞 K)) (x : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = x i j

end GlobalTheory.LoopV

end
