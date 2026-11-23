module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenFlagSlopeBound
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

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.eigen_flag_slope_bound : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  exact @GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData
