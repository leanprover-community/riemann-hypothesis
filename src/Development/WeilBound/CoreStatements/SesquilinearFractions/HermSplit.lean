module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.CoefZeroOfPer
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

def Hm : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k k' => if ty k = ty k' then 2 * Complex.I * ty k (G (blk hty k) (blk hty k')) else 0

def Q (σ : E →+* ℂ) (z w : Fin g → ℂ) : ℂ :=
  ∑ k : {k // ty k = σ}, ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k')

theorem herm_split (z w : Fin g → ℂ) : hermForm (Hm hty G) z w = ∑ σ, Q hty G σ z w := by
  have hF : ∀ σ : E →+* ℂ, ∀ k : {k // ty k = σ},
      ∑ k' : {k // ty k = σ}, z k * (2 * Complex.I * σ (G (blk hty k) (blk hty k'))) * conj (w k') =
      z k * (Hm hty G *ᵥ star w) k := by
    intro σ ⟨k, hk⟩
    simp only [mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
    rw [Finset.mul_sum, ← Fintype.sum_subtype_add_sum_subtype (fun k' => ty k' = σ)]
    have h2 : ∑ k' : {k' // ¬ ty k' = σ}, z k * (Hm hty G k k' * conj (w k')) = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨k', hk'⟩ _
      have hne : ¬ ty k = ty k' := by
        rw [hk]
        exact fun h => hk' h.symm
      simp [Hm, hne]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    rintro ⟨k', hk'⟩ _
    have heq : ty k = ty k' := hk.trans hk'.symm
    simp only [Hm, Matrix.of_apply, heq, if_true]
    rw [hk']
    ring
  unfold hermForm
  rw [dotProduct, ← Fintype.sum_fiberwise ty]
  apply Finset.sum_congr rfl
  intro σ _
  unfold Q
  apply Finset.sum_congr rfl
  intro k _
  exact (hF σ k).symm

theorem Q_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin p, ∑ b : Fin p, z ((eP hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inl a) (.inl b))) * conj (w ((eP hty σ h).symm b)) := by
  have hb : ∀ a : Fin p, blk hty ((eP hty σ h).symm a : Fin g) = Sum.inl a := by
    intro a
    rw [blk_inl hty σ h _ ((eP hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eP hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

theorem Q_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (z w : Fin g → ℂ) :
    Q hty G σ z w = ∑ a : Fin q, ∑ b : Fin q, z ((eQ hty σ h).symm a) *
      (2 * Complex.I * σ (G (.inr a) (.inr b))) * conj (w ((eQ hty σ h).symm b)) := by
  have hb : ∀ a : Fin q, blk hty ((eQ hty σ h).symm a : Fin g) = Sum.inr a := by
    intro a
    rw [blk_inr hty σ h _ ((eQ hty σ h).symm a).2]
    simp
  unfold Q
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (eQ hty σ h).symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hb a, hb b]

end PositivityTheory.Xgf.DPer

end
