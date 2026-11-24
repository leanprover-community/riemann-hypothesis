module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe

@[expose] public section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem sum_addChar_ofMul_mul_ofMul_inv (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (a b : G) :
    ∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      ψ (Additive.ofMul (a * b⁻¹)) := by
    intro ψ
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite]
  have hc : Fintype.card (Additive G) = Fintype.card G :=
    Fintype.card_congr Additive.ofMul.symm
  simp only [hc, ofMul_eq_zero, mul_inv_eq_one]

end GlobalTheory.CompanionTheory.PartialZeta
