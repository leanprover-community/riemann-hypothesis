module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCloudUnitLower
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_del_ge_cloudUnit_and_count_bounds : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * D.R.m) ^ 3 / D.div.etaF ^ C.P.CDel ≤ (D.s.Del : ℝ) ∧ C.P.CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧ (D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)) ∧ (((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ (D.s.Del : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_cloudUnit_lower | exact GlobalTheory.EX.szRow_cloudUnit_lower | (intros; apply GlobalTheory.EX.szRow_cloudUnit_lower <;> assumption)
