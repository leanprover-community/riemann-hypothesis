module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionSetSubgroup
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem integral_of_mul_integral : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  intro L l _ hl ι h2 h3 hd z N hN hP
  have hg : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, by simp, ?_, ?_, ?_⟩
    · simpa using h2
    · simpa using h3
    · simpa [map_sub, map_mul, map_pow, map_ofNat] using hd
  obtain ⟨-, -, -, G, hG, -⟩ := GlobalTheory.Klein.not_red_addSubgroup l ι L 0 hg
  by_contra hc
  have hz : z ∈ G := by
    rw [hG]; intro h; exact hc (by simpa using h.2)
  have hNz : (N : ℂ) * z ∈ G := by
    have := G.nsmul_mem hz N
    simpa [nsmul_eq_mul] using this
  rw [hG] at hNz
  exact hNz ⟨hN, by simpa using hP⟩

end GlobalTheory.Honda
