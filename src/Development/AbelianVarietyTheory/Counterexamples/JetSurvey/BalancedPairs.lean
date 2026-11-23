module

public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
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

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.ChartJoints

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ (a : E) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem balanced_pairs (H : Host E) {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S]
    (τ τ' : E →+* ℂ) (v : S)
    (hv : ∀ a : 𝓞 E, algebraMap c.F S (embK c τ a) * v = algebraMap c.F S (embK c τ' (H.bar a)) * v)
    (hne : τ ≠ ComplexEmbedding.conjugate τ') : v = 0 := by
  have : ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' (H.bar a) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    have := congrArg (fun z : c.F => (z : ℂ)) (hcon a)
    simp only [embK_coe] at this
    rw [emb_bar] at this
    exact this
  obtain ⟨a, ha⟩ := this
  have hu : IsUnit (algebraMap c.F S (embK c τ a - embK c τ' (H.bar a))) :=
    (IsUnit.mk0 _ (sub_ne_zero.2 ha)).map _
  apply hu.mul_left_cancel
  rw [map_sub, sub_mul, hv a, sub_self, mul_zero]

end GlobalTheory.ChartJoints
