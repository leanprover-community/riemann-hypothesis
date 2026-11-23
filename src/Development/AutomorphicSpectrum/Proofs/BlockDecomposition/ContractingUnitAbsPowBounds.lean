module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.TopNilp

theorem nabs_absPow_of_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  intro k _ _ _ _ t ht
  have hpos : 0 < nabs k t := nabs_pos' k t
  refine ⟨hpos, ?_, fun d => ?_⟩
  · by_contra hge
    have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (t : k) :=
      (nabs_le_iff 1 t).1 (by rw [nabs_one k]; exact not_lt.1 hge)
    rw [Units.val_one, map_one] at h1
    obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hr0 : r ≠ 0 := by simpa using hr
    have hnh : cball (Units.mk0 r hr0) ∈ 𝓝 (0 : k) :=
      (isOpen_cball _).mem_nhds (by simp [cball])
    obtain ⟨n, hn⟩ := (ht.eventually hnh).exists
    have h2 : valuation k ((t : k) ^ n) ≤ valuation k r := hn
    rw [map_pow] at h2
    exact absurd ((one_le_pow₀ h1).trans h2) (not_le.2 hr1)
  · rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le]

end GlobalTheory.CompanionTheory.TopNilp
