module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def SecBC (Xo : Moduli Dw l) {c c' : Coeff l} (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ f' ∈ sec Xo c' a n, ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c),
    (∀ i, fs i ∈ sec Xo c a n) ∧ IsBC hle f' as fs

def SecBCAll (Xo : Moduli Dw l) {c c' : Coeff l} (hle : c.F ≤ c'.F) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SecBC Xo hle a n

def IsBCTest {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F)
    (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (p' : TRing c'.F) [Algebra c.F p'.R] (h : AlgOver c c' hle p'.R) (y' : FrPt Xo c' p'.R)
    (p : TRing c.F) (φ : p.R →ₐ[c.F] p'.R) (y : FrPt Xo c p.R), FrMap φ y (y'.res hle h) →
    f' p' y' = ∑ i, algebraMap c'.F p'.R (as i) * φ (fs i p y)

def SecBCTest (Xo : Moduli Dw l) {c c' : Coeff l} (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ f' ∈ sec Xo c' a n, ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c),
    (∀ i, fs i ∈ sec Xo c a n) ∧ IsBCTest hle f' as fs

end GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests
