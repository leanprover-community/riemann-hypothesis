module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem weight_fst_eq_mapDomain {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  refine Finsupp.sum_congr fun p _ => ?_
  simp

theorem substF_X_isWeightedHomogeneous {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by
  rw [substF_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun k _ => IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
  have h1 := isWeightedHomogeneous_X ℂ (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ)) (p.1, k, l)
  have h2 := (isWeightedHomogeneous_C (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
    (h p.1 k p.2.1 * g p.1 l p.2.2)).mul h1
  rwa [zero_add] at h2

theorem mapDomain_fst_eq_of_coeff_substF_ne_zero {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : AddMonoidAlgebra.coeff (substF h g (MvPolynomial.monomial k 1)) k' ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  have key : IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (MvPolynomial.monomial k 1)) (Finsupp.mapDomain Prod.fst k) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, ← weight_fst_eq_mapDomain, Finsupp.weight_apply,
      Finsupp.sum]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
    rw [map_pow]
    exact (substF_X_isWeightedHomogeneous h g p).pow (k p)
  rw [← weight_fst_eq_mapDomain]
  exact key hk

end GlobalTheory.CompactHowe

end
