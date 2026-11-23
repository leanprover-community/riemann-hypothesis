module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.size_power_le_inverse_square_product : ∀ (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ), n * B + 2 ≤ N → (∀ i, cs.count i = N ∨ m i = 0) →
  sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq <;> assumption)
