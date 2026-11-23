module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.splitMod :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ w : ℕ, w.Prime →
      ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → ¬ A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ D.om.ker → l ∣ w - 1 := by
  intro Ω _ _ _ l _ c D hD w hw A hwA hlA hdec
  have hlw : l ≠ w := by
    rintro rfl; exact hlA hwA
  obtain ⟨-, -, γ, hγ, -, hcyc⟩ := UpperTheory.V.Chr.decCyc Ω w A hw hwA
  have hγl : ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = w := hcyc l hlw
  have hom : D.om γ = 1 := hdec hγ
  have hbar := hD.om_bar γ
  simp only [Raw.bar, hom, chiO, MonoidHom.comp_apply, Units.coe_map, Units.val_one, map_one,
    MonoidHom.coe_coe, hγl] at hbar
  have hbar' : residue c.O (algebraMap ℤ_[l] c.O (w : ℤ_[l])) = 1 := hbar.symm
  have hint : Algebra.IsIntegral ℤ_[l] c.O := by
    haveI := c.fin
    infer_instance
  have key : ((w : ℤ_[l]) - 1) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    have h0 : residue c.O (algebraMap ℤ_[l] c.O ((w : ℤ_[l]) - 1)) = 0 := by
      rw [map_sub, map_one, map_sub, map_one, hbar', sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    letI := hint
    have hmax : (IsLocalRing.maximalIdeal c.O).comap (algebraMap ℤ_[l] c.O) = IsLocalRing.maximalIdeal ℤ_[l] :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal c.O))
    rw [← hmax]
    exact hm
  have hcast : ((w : ℤ_[l]) - 1) = (((w : ℤ) - 1 : ℤ) : ℤ_[l]) := by push_cast; rfl
  rw [hcast, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_int_lt_one_iff_dvd] at key
  have h1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by
    rw [Nat.cast_sub hw.one_le, Nat.cast_one]
  rw [← h1] at key
  exact Int.natCast_dvd_natCast.mp key
