module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerProdOrthogonalBlocks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.latticeIntertwiner_prod_orthogonal_blocks : ∀ (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)), IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m)) → F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) → relIdx (stdLat L m) Λ ≠ 0 → IsSemiChar (stdH L (ι × m)) (blkLat Λ) (alphaQ c (stdH L (ι × m))) ∧ F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) ∧ relIdx (stdLat L (ι × m)) (blkLat Λ) ≠ 0 ∧ ∀ w, inter (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) (blkLat Λ) (F0 L ω₀ (ι × m)) w = ∏ k, inter (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) Λ (F0 L ω₀ m) (fun v => w (k, v)) := by
  first | exact @GlobalTheory.BaseVacuum.prod_blk_inter | exact GlobalTheory.BaseVacuum.prod_blk_inter | (intros; apply GlobalTheory.BaseVacuum.prod_blk_inter <;> assumption)
