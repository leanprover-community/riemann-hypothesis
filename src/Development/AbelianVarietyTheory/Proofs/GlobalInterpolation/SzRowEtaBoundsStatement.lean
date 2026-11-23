module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
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

theorem _root_.GlobalTheory.T.sizes_etaSz_le_b_div_and_log_etaSz_le_and_t_le : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  first | exact @GlobalTheory.EX.szRow_eta_bounds | exact GlobalTheory.EX.szRow_eta_bounds | (intros; apply GlobalTheory.EX.szRow_eta_bounds <;> assumption)
