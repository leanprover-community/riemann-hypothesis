module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRootAlt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

namespace GammaOnLevels

open PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem cancel_C {x a : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (ha : a ≠ 0) {g : O⟦X⟧}
    (h : C a * g ∈ Ideal.span {X - C x}) : g ∈ Ideal.span {X - C x} := by
  obtain ⟨c, t, rfl⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hx g
  have h2 : C (a * c) ∈ Ideal.span {X - C x} := by
    have e : C (a * c) = C a * ((X - C x) * t + C c) - (X - C x) * (C a * t) := by
      rw [map_mul]; ring
    rw [e]
    exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have h3 := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx h2
  have hc : c = 0 := (mul_eq_zero.1 h3).resolve_left ha
  rw [hc, map_zero, add_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem eval_eq_zero {x : O} (hx : x ∈ IsLocalRing.maximalIdeal O) (r : Polynomial O)
    (h : (r : O⟦X⟧) ∈ Ideal.span {X - C x}) : r.eval x = 0 := by
  apply Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hx
  have e := Polynomial.modByMonic_add_div r (Polynomial.X - Polynomial.C x)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at e
  generalize r /ₘ (Polynomial.X - Polynomial.C x) = d at e
  generalize r.eval x = c at e ⊢
  subst e
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C,
    Polynomial.coe_C] at h
  have e2 : (C c : O⟦X⟧) = (C c + (X - C x) * (d : O⟦X⟧)) - (X - C x) * (d : O⟦X⟧) := by ring
  rw [e2]
  exact Ideal.sub_mem _ h (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end GammaOnLevels


variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]



end Formalism.MainNotions.N.Ln17
