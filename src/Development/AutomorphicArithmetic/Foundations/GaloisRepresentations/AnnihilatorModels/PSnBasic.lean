module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem form_map' {A A' ι : Type} [CommRing A] [CommRing A'] [Fintype ι] (ρ : A →+* A') (c : ι → A) :
    (form c).map (MvPolynomial.map ρ) = form (fun k => ρ (c k)) := by
  unfold form
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 2

  simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem form_eval' {A ι : Type} [CommRing A] [Fintype ι] (x y : ι → A) :
    Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k) (form y) =
      ∑ k, MvPolynomial.C (x k - y k) * MvPolynomial.X k := by
  unfold form
  show Polynomial.eval _ _ = _
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [map_sub, sub_mul]

private theorem form_natDegree' {A ι : Type} [CommRing A] [Fintype ι] [Nontrivial A] (v : Multiset (ι → A)) :
    ((v.map form).prod).natDegree = v.card := by
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_def, form, Polynomial.natDegree_X_sub_C]
    simp
  · intro f hf
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Polynomial.monic_X_sub_C _

theorem UpperTheory.Gal.crystallineComparison.snBasic_of :
    SameNormBasic := by
  intro A ι _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A' _ ρ u u' h
    unfold SameNorm at h ⊢
    have e := congrArg (Polynomial.map (MvPolynomial.map ρ)) h
    simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, form_map'] at e
    simpa [Multiset.map_map, Function.comp_def] using e
  · intro x u u' h
    simp only [SameNorm, Multiset.map_cons, Multiset.prod_cons] at h ⊢
    exact (show (form x).Monic from Polynomial.monic_X_sub_C _).isRegular.left h
  · intro _ u u' h
    unfold SameNorm at h
    have e := congrArg Polynomial.natDegree h
    rwa [form_natDegree', form_natDegree'] at e
  · intro x u u' h hx
    unfold SameNorm at h
    have e := congrArg (Polynomial.evalRingHom (∑ k, MvPolynomial.C (x k) * MvPolynomial.X k)) h
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map] at e
    simp only [Function.comp_def, form_eval'] at e
    rw [← e]
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.2 ⟨x, hx, by simp⟩
