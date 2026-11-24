module

public import Mathlib.LinearAlgebra.BilinearMap
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

namespace GlobalTheory.CompanionTheory.Ar

structure ProIso (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ n, 0 < n → ∀ x, (∃ y, a n x = n • y) ↔ ∃ y, x = n • y
  surj : ∀ n, 0 < n → ∀ y, ∃ x e, y = a n x + n • e
  isom : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ B' (a n x) (a n y) - B x y
  compat : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ e, a (n * m) x = a n x + n • e

structure ProIsoAt (p : ℕ) (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ k x, (∃ y, a k x = p ^ k • y) ↔ ∃ y, x = p ^ k • y
  surj : ∀ k y, ∃ x e, y = a k x + p ^ k • e
  isom : ∀ k x y, ((p : ℤ) ^ k) ∣ B' (a k x) (a k y) - B x y
  compat : ∀ k x, ∃ e, a (k + 1) x = a k x + p ^ k • e

variable {O : Type} [CommRing O] {L L' L'' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] [AddCommGroup L''] [Module O L''] {B : LinearMap.BilinForm ℤ L}
  {B' : LinearMap.BilinForm ℤ L'} {B'' : LinearMap.BilinForm ℤ L''}

def ProIso.IsInv (f : ProIso O B B') (g : ProIso O B' B) : Prop :=
  (∀ n, 0 < n → ∀ x, ∃ e, g.a n (f.a n x) = x + n • e) ∧ ∀ n, 0 < n → ∀ y, ∃ e, f.a n (g.a n y) = y + n • e

end GlobalTheory.CompanionTheory.Ar
