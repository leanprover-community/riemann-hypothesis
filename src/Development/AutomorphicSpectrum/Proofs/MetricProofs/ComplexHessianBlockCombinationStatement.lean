module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianBlockCombination
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

theorem _root_.GlobalTheory.T.complex_hessian_block_combination : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre <;> assumption)
