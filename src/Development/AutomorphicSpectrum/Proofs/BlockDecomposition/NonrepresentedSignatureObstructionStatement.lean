module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.nonrepresented_signature_obstruction : ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → ∃ (ρ : D.what₂.Tau) (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) ∧ GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.NonnegOn ε (β.1.map (tauE D ρ)) S ∧ ∀ T : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (gramAt D V ρ) T → Module.finrank ℂ T < Module.finrank ℂ S := by
  exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction
