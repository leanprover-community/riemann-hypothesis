module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial _ K))

def FirstColumnPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = 0 then P else 0) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous P ∧ rename (fun i => (i, (0 : Fin (m + 1)))) f = F)

def SignedMinorPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = Fin.last m then 0 else Q) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous Q ∧ aeval (covY K m) f = F)

def SignedMinorsAlgIndependent : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → AlgebraicIndependent K (covY K m)

def SignedMinorsCofactorTransform : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)), IsUnit g.det →
    rowAct K g (covY K m i) = C g.det * ∑ j, C (g⁻¹ j i) * covY K m j

def CovL5adj : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)),
    rowAct K g (covY K m i) = ∑ j, C (g.adjugate j i) * covY K m j

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
