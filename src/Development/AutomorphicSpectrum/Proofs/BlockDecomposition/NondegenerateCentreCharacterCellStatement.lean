module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCell
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


theorem _root_.GlobalTheory.T.nondegenerate_centre_character_cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.SmallZ.small | exact GlobalTheory.CompanionTheory.ZUnf.SmallZ.small | (intros; apply GlobalTheory.CompanionTheory.ZUnf.SmallZ.small <;> assumption)
