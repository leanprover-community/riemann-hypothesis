module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  first | exact @GlobalTheory.DefArith.two_defBound_ge | exact GlobalTheory.DefArith.two_defBound_ge | (intros; apply GlobalTheory.DefArith.two_defBound_ge <;> assumption)
