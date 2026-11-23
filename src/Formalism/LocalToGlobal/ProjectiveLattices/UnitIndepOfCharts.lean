module

public import Formalism.LocalToGlobal.ProjectiveLattices.FrameProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
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

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Clauses

variable (Xo : Moduli Dw l) (c : Coeff l)

def FrChartF : Prop :=
  FrChart (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)

def BorChartF : Prop :=
  BorChart (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')

end Clauses

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem evalWD_fr (h : FrChartF Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_of_frChart h

theorem wtField_of_borChart (h : BorChartF Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  exact wtAll_of_borChart h (ex Dw a n) hf.1 hf.2 S t y y' hy hy' hb

theorem unitIndep_of_charts (h : BorChartF Xo c) (hL : IntLatU Xo c) : UnitIndep Xo c :=
  unitIndep_of (wtField_of_borChart h) (intDiagUnit_of hL)

end Proofs

end Formalism.L2.Pj
