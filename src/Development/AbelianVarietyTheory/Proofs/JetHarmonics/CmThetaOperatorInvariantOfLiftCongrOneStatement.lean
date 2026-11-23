module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOne
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
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

@[expose] public section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.cmThetaOperator_invariant_of_lift_congr_one : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (n m s : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), S.Ok → (∀ i, b i ∈ S.La) → S.IsTheta e → IsIdem lam S.d m eps → 2 * n ≤ m → (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) → s ≡ 1 [MOD q ^ n] → opW S.d S.Hm ((s : ℂ) • liftY q n eps b y) (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b y) (opU S.Hm t e) ∧ ∀ v ∈ S.La, kap S.Hm v ((s : ℂ) • liftY q n eps b y) = kap S.Hm v (liftY q n eps b y) := by
  first | exact @GlobalTheory.MomOne.lift_change | exact GlobalTheory.MomOne.lift_change | (intros; apply GlobalTheory.MomOne.lift_change <;> assumption)
