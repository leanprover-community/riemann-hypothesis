module

public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangeSt

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FreeQuotientRank MvPolynomial

namespace FinKey

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def detZ (Dw : Datum H) : MvPolynomial (ArcLt Dw) ℤ :=
  ∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => (X (⟨τ, i, l⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℤ)).det


open Classical in
def subA {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (y x : ArcLt Dw) : K :=
  ∑ k : Fin (Dw.mult y.1), if x = ⟨y.1, y.2.1, k⟩ then A y.1 k y.2.2 else 0

theorem subA_sum {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (y : ArcLt Dw) :
    (∑ x : ArcLt Dw, C (subA A y x) * (X x : MvPolynomial (ArcLt Dw) K)) =
      ∑ k : Fin (Dw.mult y.1), C (A y.1 k y.2.2) * X ⟨y.1, y.2.1, k⟩ := by

  simp only [subA, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single ⟨y.1, y.2.1, k⟩]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end FinKey

end Formalism.L2.Pj.QAt
