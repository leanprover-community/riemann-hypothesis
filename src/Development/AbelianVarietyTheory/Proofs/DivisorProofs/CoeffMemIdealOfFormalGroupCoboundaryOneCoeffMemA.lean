module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  intro p _ O _ G d c I hp s hs α
  obtain ⟨c', hlaw, -, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by rwa [pow_one])
  have hpk : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hp
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ c.isLaw.const (O ⧸ I) (Ideal.Quotient.mk I)).1 s
  have hz : map (Ideal.Quotient.mk I) (cob1 c.μ s) = 0 := by
    ext β
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hs β
  rw [hz] at hmap
  have h0 := GlobalTheory.Katz.eq_zero_of_cob1_eq_zero p (O ⧸ I) hpk d (G.baseChange (O ⧸ I)) c'
    (fun i => map (Ideal.Quotient.mk I) (c.μ i)) hlaw (map (Ideal.Quotient.mk I) s) hmap.symm
  have := congrArg (coeff α) h0
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog
