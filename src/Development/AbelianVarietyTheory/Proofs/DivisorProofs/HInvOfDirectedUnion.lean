module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfFilteredColimitStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.UnionHInv

variable {A : Type} [CommRing A] {ι : Type} [Preorder ι] (S : ι → Subalgebra ℤ A) (hS : Monotone S)

noncomputable def diag : ι ⥤ CommRingCat.{0} where
  obj i := CommRingCat.of (S i)
  map {i j} h := CommRingCat.ofHom (Subalgebra.inclusion (hS (leOfHom h))).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

noncomputable def cocone : Cocone (diag S hS) where
  pt := CommRingCat.of A
  ι := { app := fun i => CommRingCat.ofHom (S i).val.toRingHom
         naturality := fun i j h => by ext x; rfl }

theorem cocone_isColimit [IsDirected ι (· ≤ ·)] [Nonempty ι] (hcov : ∀ a, ∃ i, a ∈ S i) :
    Nonempty (IsColimit (cocone S hS)) := by
  haveI : ReflectsColimitsOfShape ι (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change A at x
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i j xi xj h
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.UnionHInv


open GlobalTheory.UnionHInv in
theorem GlobalTheory.EtC.hInv_of_directed_union : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  intro q _ A _ ι _ _ _ S hS hcov hu hH
  obtain ⟨hc⟩ := cocone_isColimit S hS hcov
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit q ι (diag S hS) (cocone S hS) hc hu hH
