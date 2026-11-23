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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.TraceRealPartConjugateSum

open NumberField

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl

theorem sum_re_add_conj {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : E) :
    ∑ τ : ↥(ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X),
      Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) =
      (↑((Algebra.trace ℚ E : E → ℚ) x) : ℝ) := by
  classical
  set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ
  have hconj : ∀ τ : E →+* ℂ,
      τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x := by
    intro τ
    rw [map_add (f := _), ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc,
      IsCMField.complexEmbedding_complexConj]
  have himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E τ]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x := by
    rw [← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg,
      Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => hconj τ
  calc ∑ τ : ↥Ψ, Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))
      = Complex.re (∑ τ : ↥Ψ, (↑τ : E →+* ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := (Complex.re_sum _ _).symm
    _ = Complex.re (∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := by
      rw [Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]
    _ = _ := by
      rw [hsum, ← trace_eq_sum_ringHom x]
      simp

end GlobalTheory.TraceRealPartConjugateSum
