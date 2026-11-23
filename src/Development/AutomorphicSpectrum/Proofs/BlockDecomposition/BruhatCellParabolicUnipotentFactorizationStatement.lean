module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorization
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

open scoped Matrix

theorem _root_.GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  first | exact @GlobalTheory.CompanionTheory.DCell.main | exact GlobalTheory.CompanionTheory.DCell.main | (intros; apply GlobalTheory.CompanionTheory.DCell.main <;> assumption)
