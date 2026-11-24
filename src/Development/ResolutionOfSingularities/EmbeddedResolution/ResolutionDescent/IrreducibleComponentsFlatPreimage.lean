module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
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

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem apply_mem_irreducibleComponent_iff_of_generalizingMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hcont : Continuous (fun x : ↥X => f x) := f.base.hom.continuous
  constructor
  · intro hx
    obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    have hη' : closure ({η} : Set ↥Y) = C := hη
    have hxmem : (fun x : ↥X => f x) x ∈ closure ({η} : Set ↥Y) := by
      rw [hη']
      exact hx
    have hspec : η ⤳ (fun x : ↥X => f x) x := specializes_iff_mem_closure.mpr hxmem
    obtain ⟨x', hx'spec, hfx'⟩ := hf hspec
    refine ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x',
      ?_, ?_⟩
    · have hsub : closure ({x'} : Set ↥X) ⊆ irreducibleComponent x' :=
        closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent)
          isClosed_irreducibleComponent
      exact hsub (specializes_iff_mem_closure.mp hx'spec)
    · have hsub : C ⊆ closure ((fun x : ↥X => f x) '' irreducibleComponent x') := by
        rw [← hη']
        refine closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure
        exact subset_closure ⟨x', mem_irreducibleComponent, hfx'⟩
      have hirr : IsIrreducible (closure ((fun x : ↥X => f x) '' irreducibleComponent x')) :=
        (isIrreducible_irreducibleComponent.image (fun x : ↥X => f x)
          hcont.continuousOn).closure
      exact Set.Subset.antisymm (hC.2 hirr hsub) hsub
  · rintro ⟨C', -, hxC', rfl⟩
    exact subset_closure ⟨x, hxC', rfl⟩

theorem apply_mem_irreducibleComponent_iff_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by
  have hf : GeneralizingMap (fun x : ↥X => f x) :=
    AlgebraicGeometry.Flat.generalizingMap (f := f)
  exact apply_mem_irreducibleComponent_iff_of_generalizingMap f hf hC x

end FunctorialResolution.EmbeddedResolution
