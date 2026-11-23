module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.primitive_vector_extends_hyperbolic : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit
