module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Principalise

theorem comap_mul_idealSheaf : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (I J : X.IdealSheafData),
    (I * J).comap f = I.comap f * J.comap f := by
  intro X X' f I J
  have h : ∀ y : X', ∃ (U : X.affineOpens) (A : X'.affineOpens), y ∈ A.1 ∧ A.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨A, hA⟩, hyA, hAU⟩
  choose U A hyA hAU using h
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, comapIdealAffine _ f (U y) (A y) (hAU y),
      comapIdealAffine _ f (U y) (A y) (hAU y), comapIdealAffine _ f (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end GlobalTheory.Principalise
