module

public import ReciprocityTheory.DualLattices.SqZeroOfSpan
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure DualPair (R : LAlg R₀) where
  D : LAlg R₀
  π : LHom D R
  σ : LHom R D
  η : (D : Type u)
  sect : ∀ r, π.1 (σ.1 r) = r
  η_sq : η * η = 0
  ker_eq : RingHom.ker π.1 = Ideal.span {η}
  free : ∀ r, σ.1 r * η = 0 → r = 0

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma η_mem : Dp.η ∈ Dp.π.ker := by
  show Dp.η ∈ RingHom.ker Dp.π.1
  rw [Dp.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma sqZero : Dp.π.SqZero := by
  refine ⟨fun r => ⟨Dp.σ.1 r, Dp.sect r⟩, ?_⟩
  rw [Dp.ker_eq, Ideal.span_singleton_pow, pow_two, Dp.η_sq, Ideal.span_singleton_eq_bot]

def ηk : Dp.π.ker := ⟨Dp.η, Dp.η_mem⟩

end DualPair

namespace BX

variable (B : BX R₀)

def IsHeight {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] R) : Prop :=
  ∀ v : B.gg, ∃ z : (Dp.D : Type u)ˣ,
    B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧ (z : Dp.D) = 1 + Dp.σ.1 (h v) * Dp.η

end BX

def HighestWeightVectorUniformBounds (B : BX R₀) : Prop :=
  ∀ (R : LAlg R₀) (Dp : DualPair R) (N : ℕ), (N : (R : Type u)) = 0 →
    (∀ (y : B.G R) (v : B.gg) (u : B.P Dp.D (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y)),
      HEq (B.pmap Dp.π u) (B.zero1 y) →
      HEq (B.nsmul1 u N) (B.zero1 (B.map Dp.σ y))) ∧
    (∀ y : B.G R, N • y = 0 → ∃! h : B.gg →ₗ[R₀] R, B.IsHeight Dp N y h) ∧
    (∀ (y y' : B.G R) (h h' : B.gg →ₗ[R₀] R), B.IsHeight Dp N y h → B.IsHeight Dp N y' h' →
      B.IsHeight Dp N (y + y') (h + h'))

end ReciprocityTheory.PGsh
