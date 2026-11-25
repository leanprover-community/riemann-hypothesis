module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm

open NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem zeta_pow_div {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : zeta n ^ (n / m) = zeta m := by
  obtain ⟨k, rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k hm]
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.Dvd l₂) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  · have hz : zeta l₂.A ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [SetLike.mem_coe, ← zeta_pow_div l₂.A_pos h.2.2]
    exact pow_mem hz _

end GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm
