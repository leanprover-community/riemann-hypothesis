module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidue
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

@[expose] public section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_local_subring_monic_roots_residue : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  first | (exact @GlobalTheory.LocInField.exists_local_subring) | (exact GlobalTheory.LocInField.exists_local_subring) | (intros; apply GlobalTheory.LocInField.exists_local_subring  <;> assumption)
