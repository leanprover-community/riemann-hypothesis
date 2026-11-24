module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
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

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

def pluckerIdx {J : Type} (N : ℕ) (M : J → ℕ) : J × Fin (N + 1) → Type := fun k => Fin k.2 → Fin (M k.1)

instance pluckerIdx.fintype {J : Type} (N : ℕ) (M : J → ℕ) (k : J × Fin (N + 1)) :
    Fintype (pluckerIdx N M k) := inferInstanceAs (Fintype (Fin k.2 → Fin (M k.1)))

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V]

def pluckerCoord {J : Type} {N : ℕ} {M : J → ℕ} (φ : ∀ j, Fin (M j) → Module.Dual Ω V) (w : Fin N → V) :
    (Σ k, pluckerIdx N M k) → Ω :=
  fun p => flagMinor (φ p.1.1) w p.1.2 (Nat.lt_succ_iff.mp p.1.2.2) p.2

def pluckerDeg {K J : Type} [DecidableEq J] {N : ℕ} (a : K → ℤ) (j : J) (i : Fin N) :
    K ⊕ (J × Fin (N + 1)) → ℤ :=
  Sum.elim a ((Pi.single (j, i.castSucc) 1 : J × Fin (N + 1) → ℤ) - Pi.single (j, i.succ) 1)

end

end GlobalTheory.CompanionTheory.Ar.Num
