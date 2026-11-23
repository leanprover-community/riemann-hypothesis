module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitive
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

open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries

theorem _root_.GlobalTheory.T.sum_hecke_indicator_integral_eq_primitive : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim | exact GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim | (intros; apply GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim <;> assumption)
