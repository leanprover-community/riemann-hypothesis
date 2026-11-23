module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveClHypercohomologySingletonZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HypercohomologyPostClEqClComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_middle_of_shortExact_acy :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₃, ∃ h : (free ℤ).obj P ⟶ S.X₂, h ≫ S.g = f := by
  intro Q S hS hA P hP f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) 0).2.1
  have hsub := hA P hP (0 + 1) (by norm_num)
  have h0 : HK.ext ℤ (sgl ((free ℤ).obj P)) z 0 (0 + 1) rfl (cl f) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (e (cl f)).1 h0
  obtain ⟨h, rfl⟩ := (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).2 y
  refine ⟨h, (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1 ?_⟩
  rw [← UpperTheory.hypercohomology_post_cl_eq_cl_comp]
  exact hy
