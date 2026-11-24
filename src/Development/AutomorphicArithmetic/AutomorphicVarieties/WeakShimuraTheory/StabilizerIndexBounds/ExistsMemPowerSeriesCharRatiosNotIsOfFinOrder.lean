module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CommonFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.OneUnitTF
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open IsLocalRing Polynomial Matrix UpperTheory.V

private lemma power_series_unit_eq_one_of_torsion (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l]
    (y : (PowerSeries K)ˣ) (m : ℕ) (hm : m ≠ 0)
    (hc : PowerSeries.constantCoeff (y : PowerSeries K) = 1) (hy : y ^ m = 1) : y = 1 := by
  have : CharP (PowerSeries K) l :=
    charP_of_injective_ringHom (f := PowerSeries.C) PowerSeries.C_injective l
  apply Units.ext
  refine UpperTheory.V.Pr.T.oneUnitTF l (y : PowerSeries K) m hm ?_ ?_
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp [hc]
  · rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]

theorem UpperTheory.V.Ws.exists_mem_powerSeries_char_ratios_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H K : Type) [Group H] [Field K] [Finite K] [CharP K l] (n : ℕ)
      (ψ : Fin n → H →* (PowerSeries K)ˣ) (N : Subgroup H),
      (∀ i j, i ≠ j → ∃ g ∈ N, PowerSeries.constantCoeff (ψ i g : PowerSeries K) = PowerSeries.constantCoeff (ψ j g : PowerSeries K) ∧
        ψ i g ≠ ψ j g) → ∃ g ∈ N, ∀ i j, i ≠ j → ¬ IsOfFinOrder (ψ i g / ψ j g) := by
  intro l _ H K _ _ _ _ n ψ N h
  classical
  have := Fintype.ofFinite K
  have hpos : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hunit : ∀ y : (PowerSeries K)ˣ, PowerSeries.constantCoeff (y : PowerSeries K) ≠ 0 := fun y =>
    (y.isUnit.map PowerSeries.constantCoeff).ne_zero
  have key := UpperTheory.V.Pr.commonFree N (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2}
    (fun p => (ψ p.1.1 / ψ p.1.2).comp N.subtype) (Fintype.card K - 1) hpos ?_ ?_
  · obtain ⟨g, hg⟩ := key
    refine ⟨g, g.2, fun i j hij hf => ?_⟩
    obtain ⟨m, hm, he⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    exact hg ⟨(i, j), hij⟩ m hm (by simpa using he)
  · intro p g m hm he
    refine power_series_unit_eq_one_of_torsion l K _ m hm.ne' ?_ ?_
    · rw [Units.val_pow_eq_pow_val, map_pow]
      exact FiniteField.pow_card_sub_one_eq_one _ (hunit _)
    · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · intro p
    obtain ⟨g, hg, hc, hne⟩ := h p.1.1 p.1.2 p.2
    refine ⟨⟨g, hg⟩, fun he => hne ?_⟩
    have h1 : ψ p.1.1 g / ψ p.1.2 g = 1 := by
      refine power_series_unit_eq_one_of_torsion l K _ _ hpos.ne' ?_ (by simpa using he)
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) * ψ p.1.2 g = ψ p.1.1 g := div_mul_cancel _ _
      have h3 := congrArg (fun y : (PowerSeries K)ˣ => PowerSeries.constantCoeff (y : PowerSeries K)) h2
      simp only [Units.val_mul, map_mul] at h3
      rw [hc] at h3
      exact mul_right_cancel₀ (hunit (ψ p.1.2 g)) (h3.trans (one_mul _).symm)
    exact div_eq_one.1 h1
