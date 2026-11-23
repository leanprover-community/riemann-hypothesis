module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassComp

theorem esymm_isHomogeneous' (n k : ℕ) : (esymm (Fin n) ℝ k).IsHomogeneous k := by
  unfold esymm
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have h := IsHomogeneous.prod t (fun i => (X i : MvPolynomial (Fin n) ℝ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℝ i)
  rw [Finset.sum_const, (Finset.mem_powersetCard.mp ht).2] at h
  simpa using h

theorem chernRoots_monomial_isHomogeneous {ι : Type} (m : ι → ℕ) (s : (ι × ℕ) →₀ ℕ) (c : ℝ) :
    (chernRoots m (monomial s c)).IsHomogeneous (Finsupp.weight Prod.snd s) := by
  rw [chernRoots, aeval_monomial, Finsupp.weight_apply, Finsupp.sum]
  have hc : (algebraMap ℝ (MvPolynomial (Root m) ℝ) c).IsHomogeneous 0 := isHomogeneous_C _ _
  have := hc.mul (IsHomogeneous.prod (s.support) (fun x => (rename (Sigma.mk x.1) (esymm (Fin (m x.1)) ℝ x.2)) ^ s x)
    (fun x => x.2 * s x) (fun x _ => ((esymm_isHomogeneous' (m x.1) x.2).rename_isHomogeneous).pow (s x)))
  simpa [Finsupp.prod, smul_eq_mul, mul_comm] using this

theorem homogeneousComponent_chernRoots {ι : Type} (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ) :
    homogeneousComponent d (chernRoots m Q) = chernRoots m (weightedHomogeneousComponent Prod.snd d Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [homogeneousComponent_of_mem (chernRoots_monomial_isHomogeneous m s c),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end GlobalTheory.GrassComp
