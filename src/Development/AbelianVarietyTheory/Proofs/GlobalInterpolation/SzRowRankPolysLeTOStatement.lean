module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankPolysLeTO
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

theorem _root_.GlobalTheory.T.sizes_rank_and_poly_counts_le_TOv : SzRow (fun C D L => (((D.R.f * D.R.r.choose 2 : ℕ) + 2) * (nWv D.R L.sc : ℕ) + 2 * D.R.r ≤ (TOv L.sc : ℕ)) ∧ (40 * ((D.R.f * D.R.r.choose 2 : ℕ) + 2) ≤ (TOv L.sc : ℕ)) ∧ (11 * (D.R.f * D.R.r.choose 2 : ℕ) ^ 2 ≤ (TOv L.sc : ℕ)) ∧ (D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * ((D.R.f * D.R.r.choose 2 : ℕ) + 1) ≤ (TOv L.sc : ℕ))) := by
  first | exact @GlobalTheory.EX.szRow_rank_polys_le_TO | exact GlobalTheory.EX.szRow_rank_polys_le_TO | (intros; apply GlobalTheory.EX.szRow_rank_polys_le_TO <;> assumption)
