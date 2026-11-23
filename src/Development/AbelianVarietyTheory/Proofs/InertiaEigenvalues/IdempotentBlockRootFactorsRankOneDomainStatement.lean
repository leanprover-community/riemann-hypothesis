module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain : ∀ {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → e * e = e → e * X₀ = X₀ → X₀ * e = X₀ → Set.InjOn ρ (Finset.Icc 1 t : Set ℕ) → ∏ c ∈ Finset.Icc 1 t, (Polynomial.X - Polynomial.C (ρ c)) = blockPol e X₀ → ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧ ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  first | exact @GlobalTheory.RootFactor.rank_one_and_sq | exact GlobalTheory.RootFactor.rank_one_and_sq | (intros; apply GlobalTheory.RootFactor.rank_one_and_sq <;> assumption)
