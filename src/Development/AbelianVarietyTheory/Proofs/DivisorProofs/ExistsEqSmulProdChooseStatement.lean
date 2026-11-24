module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulProdChoose
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M], (∀ m : M, ∃ m', p • m' = m) → (∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun m : M => n • m) → ∀ (d : ℕ) (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M), (∀ a, a ≤ n → c a = c (n - a)) → (∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) = (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a) → ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g := by
  first | exact @GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose | exact GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose | (intros; apply GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose <;> assumption)
