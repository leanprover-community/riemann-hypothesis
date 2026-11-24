module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.AutomorphicForms.WhittakerRelevance
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.evOf :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι κ : Type) (a : ι → A) (b : κ → A) (S : Subalgebra ℂ A),
      (∀ i j, Commute (a i) (a j)) → (∀ i k, Commute (a i) (b k)) → (∀ k l, Commute (b k) (b l)) → (∀ i, a i ∈ S) → (∀ k, b k ∈ S) →
      ∃ ev : MvPolynomial κ (MvPolynomial ι ℂ) →+* A, (∀ c : ℂ, ev (C (C c)) = c • 1) ∧ (∀ i, ev (C (X i)) = a i) ∧
        (∀ k, ev (X k) = b k) ∧ ∀ P, ev P ∈ S := by
  intro A _ _ ι κ a b S haa hab hbb haS hbS
  have hcomm : ∀ x ∈ Set.range a ∪ Set.range b, ∀ y ∈ Set.range a ∪ Set.range b,
      x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨k, rfl⟩) y (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact (haa i j).eq
    · exact (hab i l).eq
    · exact (hab j k).symm.eq
    · exact (hbb k l).eq
  have hle : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) ≤ S := by
    apply Algebra.adjoin_le
    rintro x (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact haS i
    · exact hbS k
  have hmc : ∀ x y : Algebra.adjoin ℂ (Set.range a ∪ Set.range b), x * y = y * x := by
    intro x y
    apply Subtype.ext
    have h1 : ∀ z ∈ Set.range a ∪ Set.range b, Commute z (y : A) := fun z hz =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute y.2 (fun w hw => hcomm z hz w hw)
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute x.2
      (fun w hw => (h1 w hw).symm)).symm.eq
  letI : CommRing (Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) :=
    { (inferInstance : Ring (Algebra.adjoin ℂ (Set.range a ∪ Set.range b))) with
      mul_comm := hmc }
  let a' : ι → Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : κ → Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    fun k => ⟨b k, Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)⟩
  let e : MvPolynomial κ (MvPolynomial ι ℂ) →+* Algebra.adjoin ℂ (Set.range a ∪ Set.range b) :=
    eval₂Hom (eval₂Hom (algebraMap ℂ _) a') b'
  refine ⟨(Algebra.adjoin ℂ (Set.range a ∪ Set.range b)).val.toRingHom.comp e, ?_, ?_, ?_, ?_⟩
  · intro c
    show ((e (C (C c)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_C]
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  · intro i
    show ((e (C (X i)) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_C, eval₂Hom_X']
    rfl
  · intro k
    show ((e (X k) : Algebra.adjoin ℂ (Set.range a ∪ Set.range b)) : A) = _
    simp only [e, eval₂Hom_X']
    rfl
  · intro P
    exact hle (e P).2
