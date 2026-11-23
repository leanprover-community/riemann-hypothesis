module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet

theorem isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by
  intro n
  rw [MulChar.mul_apply]
  by_cases h : IsUnit (n : ZMod (q₁ * q₂))
  · have h1 : ∀ {q : ℕ} (hq : q ∣ q₁ * q₂) (χ : DirichletCharacter ℂ q),
        DirichletCharacter.changeLevel hq χ (n : ZMod (q₁ * q₂)) = χ (n : ZMod q) := by
      intro q hq χ
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ := χ) hq h.unit
      rw [IsUnit.unit_spec] at this
      rw [this]
      congr 1
      first
        | exact ZMod.cast_natCast hq n
        | exact ZMod.cast_natCast hq _ n
        | exact ZMod.cast_nat_cast hq n
    rw [h1, h1]
  · rw [MulChar.map_nonunit _ h]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right] at h
    rcases not_and_or.mp h with h' | h'
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime])]
      simp
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime])]
      simp

theorem exists_product_character : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩

def characterModFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

theorem characterModFour_sq : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem characterModFour_ne_one : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3

theorem exists_real_nontrivial_character : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩

end Formalism.ZeroFreeDirichlet
