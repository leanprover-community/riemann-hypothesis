module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem coeff_prod_one_sub_C_mul_X (c : ℂ) (α : Multiset ℂ) (k : ℕ) :
    ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C (c * a) * Polynomial.X).prod).coeff k
      = (-1 : ℂ) ^ k * c ^ k * α.esymm k := by
  induction α using Multiset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [Multiset.esymm]
    | succ k => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, one_mul, mul_assoc, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    cases k with
    | zero => rw [ih]; simp [Multiset.esymm]
    | succ k =>
      have h : (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      rw [Polynomial.coeff_X_mul, ih, ih, h]
      ring

theorem normalised_esymm_eq_coeff :
    ∀ (r : ℕ) (q : ℝ), 0 < q → ∀ (α : Multiset ℂ), Multiset.card α = r → ∀ k, k ≤ r → (-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2) * α.esymm k) = ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * a) * Polynomial.X).prod).coeff k := by
  intro r q hq α _ k _
  rw [coeff_prod_one_sub_C_mul_X]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  have h : (q : ℂ) ^ (k * (k - 1) / 2) * (q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2)
      = ((q : ℂ) ^ (((r : ℂ) - 1) / 2)) ^ k := by
    rw [← Complex.cpow_natCast (q : ℂ) (k * (k - 1) / 2), ← Complex.cpow_add _ _ hq0, hk,
      ← Complex.cpow_nat_mul]
    congr 1
    ring
  rw [← h]
  ring

end GlobalTheory
