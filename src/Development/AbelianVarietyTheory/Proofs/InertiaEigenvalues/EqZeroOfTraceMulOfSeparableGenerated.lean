module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TraceNondeg

theorem isNilpotent_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (w : A) (h : ∀ y : A, Algebra.trace F A (w * y) = 0) : IsNilpotent w := by
  classical
  let b := Module.finBasis F A
  have hn : IsNilpotent (Algebra.leftMulMatrix b w) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ']
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact ⟨m, Algebra.leftMulMatrix_injective b hm⟩

theorem minpoly_dvd_P {K : UQ} (B : InvAlg K) : minpoly K.E B.g ∣ B.P := by
  have h1 : minpoly K.E (Algebra.lmul K.E B.A B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  rw [← h1]
  exact LinearMap.minpoly_dvd_charpoly _

theorem eq_zero_of_trace_mul_eq_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) →
    ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by
  intro K B hP hgen w hw
  obtain ⟨m, hm⟩ := isNilpotent_of_trace_mul w hw
  obtain ⟨f, rfl⟩ := hgen w
  have hd : minpoly K.E B.g ∣ f ^ m := minpoly.dvd K.E B.g (by rw [map_pow]; exact hm)
  have hsq : Squarefree (minpoly K.E B.g) := (hP.of_dvd (minpoly_dvd_P B)).squarefree
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    rw [pow_zero] at hm
    exact (subsingleton_of_zero_eq_one hm.symm).elim _ _
  have hf : minpoly K.E B.g ∣ f := (hsq.dvd_pow_iff_dvd h0.ne').mp hd
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma.TraceNondeg
