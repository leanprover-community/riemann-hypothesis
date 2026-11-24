module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.ClsReg

theorem eq_zero_of_commute_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C),
    (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  intro p _ G y₀ hsep hdeg x hx k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have h10 : (1 : G.C) = 0 := by simpa using hk
    rw [← one_mul x, h10, zero_mul]
  have hk0 : k ≠ 0 := hkpos.ne'
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hxmem : x ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hx.eq.symm
  rw [hc, Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have h1 : Polynomial.aeval y₀ (f ^ k) = 0 := by
    rw [map_pow]; exact hk
  have h2 : minpoly G.F y₀ ∣ f ^ k := minpoly.dvd G.F y₀ h1
  have hsq : Squarefree (minpoly G.F y₀) := hsep.squarefree
  have h3 : minpoly G.F y₀ ∣ f := (hsq.dvd_pow_iff_dvd hk0).1 h2
  obtain ⟨g, hg⟩ := h3
  show Polynomial.aeval y₀ f = 0
  rw [hg, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.LKCx.ClsReg
