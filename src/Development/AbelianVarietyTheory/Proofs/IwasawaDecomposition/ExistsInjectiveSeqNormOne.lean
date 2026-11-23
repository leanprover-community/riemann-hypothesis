module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace GlobalTheory.InjectiveSeqNormOne

theorem exists_injective_seq_norm_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k : ℕ, a k * σ (a k) = 1 := by
  obtain ⟨-, hE, -, hσ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hσ, hσ, star_star])
  have hy : ∃ y, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hE.isComplex _
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [hcon] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  obtain ⟨y, hy⟩ := hy
  have h1 : ∀ k : ℕ, (k : E) + y ≠ 0 := by
    intro k hk
    apply hy
    have : y = -(k : E) := by linear_combination hk
    rw [this, map_neg, map_natCast]
  have h2 : ∀ k : ℕ, (k : E) + σ y ≠ 0 := by
    intro k hk
    apply h1 k
    have := congrArg σ hk
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine ⟨fun k => ((k : E) + y) / ((k : E) + σ y), ?_, ?_⟩
  · intro k m hkm
    have hkm' := (div_eq_div_iff (h2 k) (h2 m)).1 hkm
    have h3 : ((k : E) - m) * (σ y - y) = 0 := by linear_combination hkm'
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4) hy
  · intro k
    have a1 := h1 k
    have a2 := h2 k
    simp only [map_div₀, map_add (f := _), map_natCast, hinv]
    field_simp

end GlobalTheory.InjectiveSeqNormOne
