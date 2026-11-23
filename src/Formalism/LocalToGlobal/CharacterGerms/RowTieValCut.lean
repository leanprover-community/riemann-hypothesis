module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieVal
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

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def rowOf {n : ℕ} (b : Fin n) (F : MvPowerSeries (WVO I) C) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) F

def toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) F

end Defs

def LeafSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (H : X.Hyps V) (n : ℕ) (Po : MvPolynomial (Fin n × WV I) C)
    (kind : Fin n → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt Po kind →
    ∀ gr : Fin n → MvPowerSeries (WV I) C,
      jetAt0 Po (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) = ValOf (X.rowData H).hL Po kind gr

end Formalism.L2.FormalSeriesBounds
