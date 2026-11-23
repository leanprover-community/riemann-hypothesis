module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.AlgebraicTheory.StatementA

@[expose] public section

namespace GlobalTheory

open Formalism.L2.AlgTh

theorem tensorFourthPower_smul {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem locNormScale : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]

end GlobalTheory
