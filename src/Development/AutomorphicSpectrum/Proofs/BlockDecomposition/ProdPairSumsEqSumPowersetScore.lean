module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
public import Mathlib.Data.Finset.Powerset
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_pairs_add_eq_sum_score {n : ℕ} (z : Fin n → ℂ) :
    ∏ p ∈ prs n, (z p.1 + z p.2) = ∑ T ∈ (prs n).powerset, ∏ a, z a ^ score T a := by
  have h1 : ∀ (S : Finset (Fin n × Fin n)) (f : Fin n × Fin n → Fin n),
      ∏ p ∈ S, z (f p) = ∏ a, z a ^ (S.filter fun p => f p = a).card := by
    intro S f
    rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => mem_univ _)]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), prod_const]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [h1 T Prod.fst, h1 (prs n \ T) Prod.snd, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  have : score T a = (((T.filter fun p => p.1 = a).card + ((prs n \ T).filter fun p => p.2 = a).card : ℕ) : ℤ) := by
    simp [score]
  rw [this, zpow_natCast, pow_add]

end GlobalTheory.CompanionTheory.CoefId
