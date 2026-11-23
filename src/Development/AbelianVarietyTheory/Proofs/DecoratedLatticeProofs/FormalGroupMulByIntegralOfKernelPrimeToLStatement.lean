module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToL
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

@[expose] public section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  first | exact @GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | exact GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | (intros; apply GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to <;> assumption)
