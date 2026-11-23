module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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

open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Nsp (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {Z | ∃ g : GL A k, ∃ Ψ' ∈ SB (Matrix A D k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'}

variable {k}

theorem Nsp_le_SB (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Nsp k A D ν ≤ SB (Matrix A D k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, Ψ', hΨ', rfl⟩
  exact Submodule.sub_mem _ (GlobalTheory.SplitFlip.omB_mem_SB ν ν g 1 hΨ') hΨ'

theorem sub_mem_Nsp {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ)
    (g : GL A k) {Ψ : Matrix A D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A D k)) :
    GlobalTheory.SplitFlip.omB ν ν g 1 Ψ - Ψ ∈ Nsp k A D ν :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

end GlobalTheory.RankStrata
