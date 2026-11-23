module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreserved
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

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_translation_preserved : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p), γ ∈ GF D p → ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Transport.transport | exact GlobalTheory.CompanionTheory.FJE.Transport.transport | (intros; apply GlobalTheory.CompanionTheory.FJE.Transport.transport <;> assumption)
