module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerLatticeLocallyConstantData
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.eichlerLattice_locally_constant_data : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ : Submodule L.O S.V, IsSD L S.Hm Λ → ∀ c : ℕ, ∃ N : ℕ, ∀ (x x₁ u u₁ : S.V) (s s₁ : E), S.h x x = 0 → S.h u x = 0 → s + L.cj s = S.h u u → S.h x₁ x₁ = 0 → S.h u₁ x₁ = 0 → s₁ + L.cj s₁ = S.h u₁ u₁ → algebraMap F E ((S.ϖ : F) ^ c) • x ∈ Λ → u ∈ Λ → s ∈ L.O → (∃ y ∈ Λ, x₁ - x = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ Λ, u₁ - u = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ L.O, s₁ - s = algebraMap F E ((S.ϖ : F) ^ N) * y) → S.moved Λ x₁ u₁ s₁ = S.moved Λ x u s := by
  first | exact @GlobalTheory.HL.EichlerLocal.moved_locally_constant | exact GlobalTheory.HL.EichlerLocal.moved_locally_constant | (intros; apply GlobalTheory.HL.EichlerLocal.moved_locally_constant <;> assumption)
