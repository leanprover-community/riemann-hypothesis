module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Columns.GoodXgFin
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section E

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [CharZero K]

def XgESet (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : Set (G → K) :=
  {χ | IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1)}

theorem XgESet_finite (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : (XgESet σ e).Finite :=
  (absIrrChar_finite (G := G) (K := K)).subset fun _ h => h.1

def XgE (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : Finset (G → K) := (XgESet_finite σ e).toFinset

theorem mem_XgE {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} {χ : G → K} :
    χ ∈ XgE σ e ↔ IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1) :=
  Set.Finite.mem_toFinset _

theorem XgE_irr {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} : ∀ χ ∈ XgE σ e, IsAbsIrrChar χ :=
  fun _ h => (mem_XgE.1 h).1

end E

end Formalism.L2.Col
