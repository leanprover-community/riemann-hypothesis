module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
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

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.MaxParabIwasawa

theorem iwasawa_stdMaxParab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r a b : ℕ) (h : a + b = r) (g : GL (Fin r) k),
    (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
      ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := by
  intro k _ _ _ _ r a b h g
  have key : ∀ x : GL (Fin r) k, ∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, x = κ * p := by
    intro x
    obtain ⟨k₀, p, hp, hx⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r x
    have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi =>
      hp (show j < i from by rw [Fin.lt_def]; omega)
    exact ⟨_, ⟨k₀, rfl⟩, p, hpP, hx⟩
  refine ⟨key g, ?_⟩
  obtain ⟨κ, hκ, p, hp, e⟩ := key g⁻¹
  refine ⟨p⁻¹, inv_mem hp, κ⁻¹, inv_mem hκ, ?_⟩
  rw [← mul_inv_rev, ← e, inv_inv]

end GlobalTheory.MaxParabIwasawa
