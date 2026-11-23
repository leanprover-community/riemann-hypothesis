module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRows
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ValueFormula

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.parabolic_factorization_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | exact GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | (intros; apply GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep <;> assumption)
