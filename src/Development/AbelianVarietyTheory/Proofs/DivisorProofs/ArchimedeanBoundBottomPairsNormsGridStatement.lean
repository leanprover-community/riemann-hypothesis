module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBoundBottomPairsNormsGrid
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

theorem _root_.GlobalTheory.T.archimedeanBound_bottomPairs_norms_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  first | exact @GlobalTheory.ArchGrid.arch_grid | exact GlobalTheory.ArchGrid.arch_grid | (intros; apply GlobalTheory.ArchGrid.arch_grid <;> assumption)
