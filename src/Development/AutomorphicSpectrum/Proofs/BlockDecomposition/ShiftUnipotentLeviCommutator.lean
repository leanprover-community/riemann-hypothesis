module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.ThTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ShEmbUnip



theorem sh_emb_unip : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
    ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
      z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  intro D n ρ p hn M g₁ b hg y
  have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨g₁, hg⟩
  have hE := M.emb_mat g₁ _ _ _ _ hg
  refine ⟨⟨HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y), ?_⟩, HMul.hMul y b, ?_, rfl⟩
  · show adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]
  · apply mat_injective'
    rw [mat_mul' (M.sh y), mat_mul' _ (M.sh y), mat_mul' (M.nzx _ _), M.sh_mat, M.nzx_mat, hE, blockMatrix_zero, blockRowSubstitution_one,
      submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add,
      adj_mul, hb, Matrix.mul_neg, add_neg_cancel]

end GlobalTheory.CompanionTheory.ShEmbUnip

end
