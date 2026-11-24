module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmThetaEqSumProdTranslates
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.exists_cmTheta_eq_sum_prod_translates : ∀ (q : ℕ) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (θ : ℂ → ℂ), q.Prime → S.Ok → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → IsTh S.d θ → ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (Θ : (Fin g → ℂ) → ℂ), S.IsTheta Θ ∧ Θ ≠ 0 ∧ (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧ ∀ z : Fin g → ℂ, Θ (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  first | exact @GlobalTheory.MomOne.exists_theta_eq_sum_prod | exact GlobalTheory.MomOne.exists_theta_eq_sum_prod | (intros; apply GlobalTheory.MomOne.exists_theta_eq_sum_prod <;> assumption)
