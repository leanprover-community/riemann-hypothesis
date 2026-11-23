module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut
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

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut <;> assumption)
