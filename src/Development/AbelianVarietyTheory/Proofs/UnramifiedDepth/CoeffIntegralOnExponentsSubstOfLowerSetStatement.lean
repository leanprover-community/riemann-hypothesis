module

public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffIntegralOnExponentsSubstOfLowerSet
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
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Formalism.IncomingBounds.IncomingBound

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set : ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  first | exact @GlobalTheory.LowerSubst.subst_int_on_lower | exact GlobalTheory.LowerSubst.subst_int_on_lower | (intros; apply GlobalTheory.LowerSubst.subst_int_on_lower <;> assumption)
