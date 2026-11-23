module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.hasOrdP :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (F r a : ℕ) [NeZero F], r ≠ 0 → ∀ (A₀ : ValuationSubring Ω) (u : Ω) (k : (ZMod F)ˣ → ℤ), HasOrd F r A₀ u k →
    (∀ (d : (ZMod F)ˣ) (δ : G ℚ Ω), Lifts F d δ → HasOrd F r A₀ (opP δ a u) fun t => k (t * d) - a * k t) ∧ ∀ n : ℕ, HasOrd F r A₀ (u ^ n) fun t => n * k t := by
  intro Ω _ _ _ F r a _ hr A₀ u k hk
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hv0 : A₀.valuation (r : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hr)
  have hk' : ∀ (t : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F t σ → A₀.valuation (σ u) = A₀.valuation (r : Ω) ^ k t := hk
  refine ⟨fun d δ hδ t σ hσ => ?_, fun n t σ hσ => ?_⟩
  · have hδ' : ∀ x : Ω, x ^ F = 1 → δ x = x ^ (d : ZMod F).val := hδ
    have hσ' : ∀ x : Ω, x ^ F = 1 → σ x = x ^ (t : ZMod F).val := hσ
    have hσδ : Lifts F (t * d) (σ * δ) := by
      show ∀ x : Ω, x ^ F = 1 → (σ * δ) x = x ^ ((t * d : (ZMod F)ˣ) : ZMod F).val
      intro x hx
      rw [AlgEquiv.mul_apply, hδ' x hx, map_pow, hσ' x hx, ← pow_mul, Units.val_mul, ZMod.val_mul]
      conv_lhs => rw [← Nat.mod_add_div ((t : ZMod F).val * (d : ZMod F).val) F]
      rw [pow_add, pow_mul, hx, one_pow, mul_one]
    have h1 := hk' (t * d) (σ * δ) hσδ
    have h2 := hk' t σ hσ
    rw [AlgEquiv.mul_apply] at h1
    show A₀.valuation (σ (δ u / u ^ a)) = _
    rw [map_div₀, map_pow, map_div₀, map_pow, h1, h2, ← zpow_natCast, ← zpow_mul, zpow_sub₀ hv0, mul_comm (k t)]
  · show A₀.valuation (σ (u ^ n)) = _
    rw [map_pow, map_pow, hk' t σ hσ, ← zpow_natCast, ← zpow_mul, mul_comm (k t)]
