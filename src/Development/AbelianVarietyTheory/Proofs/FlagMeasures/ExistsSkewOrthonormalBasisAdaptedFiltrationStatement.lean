module

public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewOrthonormalBasisAdaptedFiltration
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.exists_skew_orthonormal_basis_adapted_filtration : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (deg : Fin d → ℕ), (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ c, Module.finrank ℂ (A c) = Module.finrank ℂ (A (c + 1)) + Fintype.card {i : Fin d // deg i = c}) → ∃ B : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) ∧ (∀ i, Formalism.REAL.inG ε (B i)) ∧ ∀ c, A c = Submodule.span ℂ (B '' {i | c ≤ deg i}) := by
  first | exact @GlobalTheory.SkewBasis.exists_skew_basis | exact GlobalTheory.SkewBasis.exists_skew_basis | (intros; apply GlobalTheory.SkewBasis.exists_skew_basis <;> assumption)
