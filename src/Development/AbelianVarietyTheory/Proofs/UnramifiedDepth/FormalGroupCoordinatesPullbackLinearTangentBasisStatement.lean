module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
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

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  first | exact @GlobalTheory.MainTerm.linPull_coords | exact GlobalTheory.MainTerm.linPull_coords | (intros; apply GlobalTheory.MainTerm.linPull_coords <;> assumption)
