module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
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

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Ix (Dw : Datum H) : Type := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ))

def ex (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Ix Dw → ℕ
  | none => n
  | some x => a (x.1, x.2)

theorem ex_add (Dw : Datum H) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    ex Dw (a + a') (n + n') = ex Dw a n + ex Dw a' n' := by
  funext i; cases i <;> rfl

def Dom (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop := (∀ τ, Antitone fun i => a (τ, i)) ∧ Even n

variable {l : Level H} (c : Coeff l)

instance : NumberField c.F where
  to_charZero := inferInstance
  to_finiteDimensional := c.fin

def embF (τ : E →+* ℂ) : E →+* c.F := τ.codRestrict c.F (c.conj τ)

def embK (τ : E →+* ℂ) : 𝓞 E →+* c.F := (embF c τ).comp (algebraMap (𝓞 E) E)

theorem embK_coe (τ : E →+* ℂ) (a : 𝓞 E) : ((embK c τ a : c.F) : ℂ) = τ (a : E) := rfl

end Formalism.L2.Pj
