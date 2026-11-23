module

public import Formalism.RealPlaceAnalysis.Complexify
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankAndDetOfRealBasisSkewPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.finrank_and_det_of_real_basis_skew_part : ∀ (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) → LinearIndependent ℝ E → (∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ), (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) → LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  first | exact @GlobalTheory.RealFormBasis.finrank_and_det | exact GlobalTheory.RealFormBasis.finrank_and_det | (intros; apply GlobalTheory.RealFormBasis.finrank_and_det <;> assumption)
