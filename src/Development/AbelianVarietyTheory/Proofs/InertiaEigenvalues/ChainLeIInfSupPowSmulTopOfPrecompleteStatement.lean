module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChainLeIInfSupPowSmulTopOfPrecomplete
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

@[expose] public section


theorem _root_.GlobalTheory.T.chain_le_iInf_sup_pow_smul_top_of_precomplete : ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ) (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  first | exact @GlobalTheory.chain_le_iInf_sup_pow_smul_top | exact GlobalTheory.chain_le_iInf_sup_pow_smul_top | (intros; apply GlobalTheory.chain_le_iInf_sup_pow_smul_top <;> assumption)
