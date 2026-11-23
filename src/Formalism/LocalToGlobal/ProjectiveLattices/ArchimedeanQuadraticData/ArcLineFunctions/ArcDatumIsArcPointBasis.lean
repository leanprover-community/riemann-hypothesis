module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

variable {D : D7} {T : Core D}

structure ArcDatumAt (T : Core D) (j : ℕ) (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] where

  Wp : ValuationSubring ℂ
  Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype
  a : ArcIn (T.Q.Dw j) T.Q.l (RingHom.id T.Q.c.F) K₁ (algebraMap T.Q.c.F K₁)
  χ : Sp (PowerSeries K₁) ⟶ Y.X

  chiOver : χ ≫ Y.s = spMap ((PowerSeries.C (R := K₁)).comp
    ((algebraMap T.Q.c.F K₁).comp (T.Q.c.V Wp).subtype))
  W : ArcWit Y (a.restrict (T.Q.c.V Wp).subtype) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁))
    PowerSeries.X χ
  e : ∀ τ, Fin ((T.Q.Dw j).mult τ) →
    ReciprocityTheory.ChartRestriction.G.Out.GtPt (a.restrict (T.Q.c.V Wp).subtype).D₀ (epsR K₁)
  yF : FrPt (T.Q.Xo j) T.Q.c (ArcS (T.Q.Dw j) K₁)

  th : (a.restrict (T.Q.c.V Wp).subtype).D₀.P.L.Sec
  arcDatum_isArc_point_basis : IsArcPointPowerSeries Y (a.restrict (T.Q.c.V Wp).subtype) χ W e yF
  isArc3 : IsArcPt3At Y (a.restrict (T.Q.c.V Wp).subtype) χ W yF th
  μ : ArcLt (T.Q.Dw j) →₀ ℕ
  jj : ℤ

end Formalism.L2.Pj.QAt
