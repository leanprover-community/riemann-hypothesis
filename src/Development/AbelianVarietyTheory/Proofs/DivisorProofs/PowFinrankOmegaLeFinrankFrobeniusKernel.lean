module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeFrobeniusKernelMulSpanPrimePowersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLeStatement
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.PDivGroup

theorem pow_finrank_omega_le_finrank_frobKer : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K), ∀ r : ℕ,
    (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  intro p _ K _ h G r
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hN : Module.finrank K (G.A r) = p ^ (r * G.height) := by
    have := G.rank_eq r (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hdim := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G).2.2.2
  have hord := GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers p K (G.A r) r
  have hspan := GlobalTheory.T.finrank_span_pow_pDivGroup_level_le p K h G r
  have hpos : 0 < (p ^ r) ^ Module.finrank K G.dual.omega :=
    pow_pos (pow_pos (Fact.out : p.Prime).pos _) _
  have key : (p ^ r) ^ Module.finrank K G.omega * (p ^ r) ^ Module.finrank K G.dual.omega ≤
      Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) * (p ^ r) ^ Module.finrank K G.dual.omega := by
    rw [← pow_add, hdim, ← pow_mul, ← hN]
    exact hord.trans (Nat.mul_le_mul_left _ hspan)
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory.PDivGroup
