module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem sum_re_cmType_eq_half_trace (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (ν₀ : E) :
    ∑ τ : X.Ψ, (τ.1 ν₀).re = ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => ComplexEmbedding.involutive_conjugate E τ
  have h1 : ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) = ∑ τ : E →+* ℂ, (τ ν₀).re := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := ν₀)
    rw [← (RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp] at h
    have h' := congrArg Complex.re h
    rw [Complex.re_sum] at h'
    simpa using h'
  have h2 : ∑ τ : {τ : E →+* ℂ // τ ∉ X.Ψ}, (τ.1 ν₀).re = ∑ τ : X.Ψ, (τ.1 ν₀).re := by
    let e : {τ : E →+* ℂ // τ ∉ X.Ψ} ≃ X.Ψ :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
          rw [X.cmType, hcc]; exact τ.2⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, (X.cmType _).1 τ.2⟩
        left_inv := fun τ => Subtype.ext (hcc _)
        right_inv := fun τ => Subtype.ext (hcc _) }
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    change _ = (ComplexEmbedding.conjugate τ.1 ν₀).re
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  have h3 := Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ ∈ X.Ψ)
    (fun τ => (τ ν₀).re)
  have h4 : ∑ τ : X.Ψ, (τ.1 ν₀).re + ∑ τ : {τ : E →+* ℂ // τ ∉ X.Ψ}, (τ.1 ν₀).re
      = ∑ τ : E →+* ℂ, (τ ν₀).re := by
    convert h3
  rw [h1, ← h4, h2]
  ring

end GlobalTheory
