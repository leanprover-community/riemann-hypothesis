module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_of_size_matrix : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)), (∀ a, (x a).IsCusp) → (∀ a, (y a).IsCusp) → ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0 → ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspCell.exists_equiv_of_jhMult_cell_ne_zero | exact GlobalTheory.CompanionTheory.CuspCell.exists_equiv_of_jhMult_cell_ne_zero | (intros; apply GlobalTheory.CompanionTheory.CuspCell.exists_equiv_of_jhMult_cell_ne_zero <;> assumption)
