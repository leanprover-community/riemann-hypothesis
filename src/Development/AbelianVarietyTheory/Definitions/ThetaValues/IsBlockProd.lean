module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.BlockTh

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Bk (Dw : Datum H) (n : ℕ) where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col

variable {Dw : Datum H} {n : ℕ}

def Bk.poly (K : Type) [CommRing K] (B : Bk Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c

def IsBlockProd {K : Type} [CommRing K] (P : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → Bk Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P = ∏ j, (bs j).poly K

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def ContainsTh (nab : NabV Xo c) (s : c.F) (P : MvPolynomial (LtN Dw n) c.F) {J : Type} (w : J → Rul Xo c) : Prop :=
  ∃ jb : (Fin n → LevQ Dw l) → J, Function.Injective jb ∧
    ∀ q, ∃ f : Rul Xo c, IsThRule Xo c nab (fun b => levRep (q b)) P f ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), w (jb q) p y = algebraMap c.F p.R s * f p y


variable (E) in
def p14 (r n m : ℕ) : ℝ :=
  (Real.log Real.pi + n * (Real.log 24 + (I2.dstar (E := E) m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) m : ℝ))) +
    (r + 2) * Real.log 2) / 2

end GlobalTheory.BlockTh
