module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

theorem _root_.GlobalTheory.T.trueColumns_row_sharp_bounds : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl, (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ → μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  first | exact @GlobalTheory.LvT.Built.TrueCols.row_true | exact GlobalTheory.LvT.Built.TrueCols.row_true | (intros; apply GlobalTheory.LvT.Built.TrueCols.row_true <;> assumption)
