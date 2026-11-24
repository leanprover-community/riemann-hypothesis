module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

namespace GlobalTheory.Twist

theorem addChar_eq_mulShift_unit_of_isField :
    ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 →
      ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  intro κf _ _ hF ψ φ hψ _
  classical
  let _ : Field κf := hF.toField
  have _ : Fintype κf := Fintype.ofFinite κf

  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)

  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨a, ha⟩ := hbij.2 φ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ‹φ ≠ 1› (by rw [← ha, AddChar.mulShift_zero])
  refine ⟨Units.mk0 a ha0, fun t => ?_⟩
  rw [← ha, AddChar.mulShift_apply, Units.val_mk0]

end GlobalTheory.Twist
