module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.branchingHypotheses_gridParameters_largeScale : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ) (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε → IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧ Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  first | exact @GlobalTheory.SepPer.realInputPar | exact GlobalTheory.SepPer.realInputPar | (intros; apply GlobalTheory.SepPer.realInputPar <;> assumption)
