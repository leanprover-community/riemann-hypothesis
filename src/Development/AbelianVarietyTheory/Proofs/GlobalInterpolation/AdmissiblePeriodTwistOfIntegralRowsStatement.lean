module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistOfIntegralRows
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissible_period_twist_of_integral_rows : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → ∀ Y : DivX (I.rec7 l Z), Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (I.rec7 l Z) Y (I.tw l l0 Z) := by
  first | exact @GlobalTheory.PerTwClose.twistedPeriodAdmissible_of_rowInt | exact GlobalTheory.PerTwClose.twistedPeriodAdmissible_of_rowInt | (intros; apply GlobalTheory.PerTwClose.twistedPeriodAdmissible_of_rowInt <;> assumption)
