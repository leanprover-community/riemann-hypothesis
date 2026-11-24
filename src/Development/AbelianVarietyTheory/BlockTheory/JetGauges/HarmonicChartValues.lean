module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) : Type :=
  LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))

def colSum {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, v b (colOf m b)

def sysVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) {n : ℕ}
    (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F) : S :=
  colSum c (fun b α => nab y (k : ℤ) (F b) α) P

def IsHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
    ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
      (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues
