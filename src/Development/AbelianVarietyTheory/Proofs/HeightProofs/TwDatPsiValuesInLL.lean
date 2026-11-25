module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory

theorem twDat_psi_valuesIn_LL : ∀ (B : Base) (T : TwDat B), Coh B T → ∀ v, (T.psi v).ValuesIn 0 B.embLL := by
  intro B T hC v w _
  obtain ⟨z, hz⟩ := hC.roots v
  haveI : NeZero (B.places.resChar v ^ T.k v) := ⟨pow_ne_zero _ (B.places.resChar_prime v).ne_zero⟩
  have hpow : ∀ (χ : Formalism.L2.Host.HChar B.host.E) (m : ℕ), (χ ^ m).val w = χ.val w ^ m := by
    intro χ m
    induction m with
    | zero => rw [pow_zero, pow_zero]; rfl
    | succ m ih => rw [pow_succ, Formalism.L2.Host.HChar.val_mul, ih, pow_succ]
  have h1 : (((T.psi v).val w : ℂˣ) : ℂ) ^ (B.places.resChar v ^ T.k v) = 1 := by
    have hord : T.psi v ^ (B.places.resChar v ^ T.k v) = 1 := T.psi_ord v
    have h0 : (T.psi v ^ (B.places.resChar v ^ T.k v)).val w = (1 : Formalism.L2.Host.HChar B.host.E).val w := by rw [hord]
    rw [hpow] at h0
    rw [← Units.val_pow_eq_pow_val, h0]
    rfl
  have hz' := hz.map_of_injective B.embLL.injective
  obtain ⟨i, -, hi⟩ := hz'.eq_pow_of_pow_eq_one h1
  refine ⟨z ^ i, ?_⟩
  simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rw [map_pow, hi]

end GlobalTheory
