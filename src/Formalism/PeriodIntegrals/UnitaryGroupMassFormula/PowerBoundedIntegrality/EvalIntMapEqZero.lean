module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace PI.PowBddIntWork

open Matrix Polynomial

theorem eval₂_int_map_eq_zero {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (p : ℤ[X]) (a : A)
    (h : p.eval₂ (algebraMap ℤ A) a = 0) : p.eval₂ (algebraMap ℤ B) (ψ a) = 0 := by
  have e : ψ.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [← e, ← Polynomial.hom_eval₂, h, map_zero]

theorem stepB : StepB := by
  intro E _ k γ hγ i
  obtain ⟨p, hpm, hp⟩ := hγ
  let F := AlgebraicClosure E
  let γ' : Matrix (Fin k) (Fin k) F := γ.map (algebraMap E F)
  have hp' : p.eval₂ (algebraMap ℤ (Matrix (Fin k) (Fin k) F)) γ' = 0 :=
    eval₂_int_map_eq_zero (algebraMap E F).mapMatrix p γ hp

  have hroot : ∀ μ ∈ γ'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have hs : μ ∈ spectrum F γ' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic γ').ne_zero).1 hμ
    have h1 := spectrum.subset_polynomial_aeval γ' (p.map (algebraMap ℤ F)) ⟨μ, hs, rfl⟩
    have h2 : Polynomial.aeval γ' (p.map (algebraMap ℤ F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp']
    rw [h2] at h1
    refine ⟨p, hpm, ?_⟩
    have h3 : (p.map (algebraMap ℤ F)).eval μ = p.eval₂ (algebraMap ℤ F) μ := Polynomial.eval_map _ _
    rw [← h3]
    by_contra hne
    rw [spectrum.mem_iff, sub_zero] at h1
    exact h1 ((Ne.isUnit hne).map _)
  have hcp : γ'.charpoly = γ.charpoly.map (algebraMap E F) := Matrix.charpoly_map γ _
  have hinj : Function.Injective ((algebraMap E F).toIntAlgHom) := (algebraMap E F).injective
  rw [← isIntegral_algHom_iff _ hinj]
  show IsIntegral ℤ (algebraMap E F (γ.charpoly.coeff i))
  rw [← Polynomial.coeff_map, ← hcp]

  have hq : γ'.charpoly.Monic := Matrix.charpoly_monic _
  have hcard : Multiset.card γ'.charpoly.roots = γ'.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  by_cases hi : i ≤ γ'.charpoly.natDegree
  · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hi, hq.leadingCoeff, one_mul]
    refine IsIntegral.mul (IsIntegral.pow (IsIntegral.neg isIntegral_one) _) ?_
    show _ ∈ integralClosure ℤ F
    unfold Multiset.esymm
    refine Subalgebra.multiset_sum_mem _ ?_
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hy
    refine Subalgebra.multiset_prod_mem _ ?_
    intro x hx
    exact hroot x (Multiset.mem_of_le (Multiset.mem_powersetCard.1 hs).1 hx)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact isIntegral_zero

end PI.PowBddIntWork
