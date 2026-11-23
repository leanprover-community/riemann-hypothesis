module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGap
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_node_bounds_le_h0 : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  first | exact @GlobalTheory.EX.szRow_nodeGap | exact GlobalTheory.EX.szRow_nodeGap | (intros; apply GlobalTheory.EX.szRow_nodeGap <;> assumption)
