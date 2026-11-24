module

public import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open AddSubgroup

section Def

variable (ℓ : ℕ) (A : Type*) [AddCommGroup A]

variable {ℓ A}

end Def

section Module

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

instance neZero_pow_prime (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.out.ne_zero⟩

end Module

section Lift

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

variable (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
include hcard

end Lift

section Basis

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

end Basis

section Curve

variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

end Curve

section Topology

variable {ℓ : ℕ} {A : Type*} [AddCommGroup A]

end Topology

section Action

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

end Action

section Galois

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

end Galois

end GroundTheory.Arith.Abelian
