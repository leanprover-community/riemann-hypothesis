module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveClHypercohomologySingletonZero
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → (∀ U : Scheme.{0}, Q U → Subsingleton (Sec S.X₃ U)) → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₂, ∃ h : (free ℤ).obj P ⟶ S.X₁, h ≫ S.f = f := by
  intro Q S hS hQ P hP f
  have hsub := UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q S.X₃ hQ P hP 0
  have hz : f ≫ S.g = 0 := by
    apply (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1
    exact Subsingleton.elim _ _
  haveI := hS.mono_f
  exact ⟨hS.exact.lift f hz, hS.exact.lift_f f hz⟩
