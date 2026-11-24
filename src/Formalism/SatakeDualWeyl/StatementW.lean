module

public import Formalism.GradedWeylDivisibility.StatementA
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs
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

open MvPolynomial

namespace Formalism.UG

def dwAct (R : Type) [CommRing R] (r n : ℕ) (g : GL (Fin r) R) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  Formalism.GradedWeylDivisibility.rowAct R (n := n) ((g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)

def DwActMul : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (g h : GL (Fin r) R),
    dwAct R r n (g * h) = (dwAct R r n g).comp (dwAct R r n h) ∧ dwAct R r n 1 = AlgHom.id R _

def DwStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν

def WeylGLStable : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν

def WeylGLStableLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (g : GL (Fin r) R),
    ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν, dwAct R r n g f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν

end Formalism.UG
