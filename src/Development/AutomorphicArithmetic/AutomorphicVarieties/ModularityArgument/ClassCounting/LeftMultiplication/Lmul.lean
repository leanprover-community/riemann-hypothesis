module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace UpperTheory.V.ZK.PM

variable (A : Type) [CommRing A] {G : Type} [Group G]

def cone (a : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G (m + 1) :=
  Finsupp.lmapDomain A A fun x => Fin.cons (α := fun _ => G) a x

def rmul (k : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G m := Finsupp.lmapDomain A A fun x i => x i * k

def lmul (h : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G m := Finsupp.lmapDomain A A fun x i => h * x i

def hbd (G : Type) [Group G] : ∀ m : ℕ, Ch A G (m + 1) →ₗ[A] Ch A G m
  | 0 => Finsupp.linearCombination A fun x => Finsupp.single (Fin.tail (α := fun _ => G) x) 1
  | m + 1 => Finsupp.linearCombination A fun x => Finsupp.single (Fin.tail (α := fun _ => G) x) 1 -
      cone A (x 0) m (hbd G m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def hp (k : G) : ∀ m : ℕ, Ch A G m →ₗ[A] Ch A G (m + 1)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination A fun x => cone A (x 0) (m + 1)
      (rmul A k (m + 1) (Finsupp.single x 1) - hp k m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def hd (k k' : G) : ∀ m : ℕ, Ch A G m →ₗ[A] Ch A G (m + 2)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination A fun x => cone A (x 0) (m + 2)
      (hp A k' (m + 1) (rmul A k (m + 1) (Finsupp.single x 1)) +
        hd k k' m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def pr (G : Type) [Group G] (m : ℕ) : Ch A G (m + 1) →ₗ[A] Ch A G m :=
  Finsupp.lmapDomain A A fun x i => (x i.castSucc)⁻¹ * x i.succ

end UpperTheory.V.ZK.PM

end
