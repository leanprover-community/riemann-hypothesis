module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg


set_option synthInstance.maxHeartbeats 200000 in
theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
