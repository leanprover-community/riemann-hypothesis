module

public import Formalism.PeriodIntegrals.OddDualWeyl
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

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

def genM (R : Type*) [CommRing R] (k : ℕ) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R) :=
  Matrix.of fun a s => X (a, s)

def dualM (R : Type*) [CommRing R] (k : ℕ) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R) :=
  Matrix.of fun i j => adjugate (genM R k) (Fin.rev j) i

def dualSub (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial (Fin k × Fin k) R →ₐ[R] MvPolynomial (Fin k × Fin k) R :=
  aeval fun v => dualM R k v.1 v.2

def Rel (R : Type*) [CommRing R] (k M : ℕ) (f f' : MvPolynomial (Fin k × Fin k) R) : Prop :=
  dualSub R k f' = (genM R k).det ^ M * f

def pMinor (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ) (hs : s ≤ k) :
    MvPolynomial (Fin k × Fin k) R :=
  (Matrix.of fun p q : Fin s =>
    (X (σ (Fin.castLE hs p), Fin.castLE hs q) : MvPolynomial (Fin k × Fin k) R)).det

def pw (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (ν : Fin k → ℕ) :
    MvPolynomial (Fin k × Fin k) R :=
  ∏ s : Fin k, pMinor R σ (s.val + 1) s.isLt ^ (ν s - nuNext ν s)

def low (R : Type*) [CommRing R] {k : ℕ} (ν : Fin k → ℕ) : MvPolynomial (Fin k × Fin k) R :=
  pw R Fin.revPerm ν

def degW {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ s : Fin k, (s.val + 1) * (ν s - nuNext ν s)

def expM {m : ℕ} (lam : Fin (m + 1) → ℤ) : ℕ := m * nuOf lam 0 - ∑ t, nuOf lam t

def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0

def MH (R : Type*) [CommRing R] {k : ℕ} (f : MvPolynomial (Fin k × Fin k) R) : Prop :=
  ∀ a : Fin k, ∃ d : ℕ, IsWeightedHomogeneous (rowW a) f d

def sgnK (K : Type) [Field K] (m : ℕ) : K := (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det

end PI.OddDualWeyl
