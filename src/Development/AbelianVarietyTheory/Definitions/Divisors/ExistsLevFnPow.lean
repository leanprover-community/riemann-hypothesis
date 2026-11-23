module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
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
import Formalism.LocalToGlobal.Divisibility.DefGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.L2.DIV

namespace GlobalTheory.AdeleEv

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le {E : Type} [Field E] [NumberField E] (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ x‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  by_contra h
  have h0 : (x : E) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, norm_zero] at h
    exact h zero_le_one
  have h1 : ‖τ (x : E)⁻¹‖ < 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ (not_le.1 h)
  have h2 := (hv _).2 h1
  rw [map_inv₀] at h2
  have h3 : v.valuation E (x : E) ≤ 1 := v.valuation_le_one x
  have h4 : v.valuation E (x : E) ≠ 0 := (map_ne_zero _).2 h0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 h4)).1 h2) (not_lt.2 h3)

end GlobalTheory.AdeleEv

end
