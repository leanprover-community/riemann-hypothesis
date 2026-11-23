module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBounds
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  first | exact @GlobalTheory.GridReal.num_real_bounds | exact GlobalTheory.GridReal.num_real_bounds | (intros; apply GlobalTheory.GridReal.num_real_bounds <;> assumption)
