module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.CorePf2

theorem isClosedImmersion_of_cover {X Y : Scheme.{0}} (f : X ⟶ Y) {ι : Type} (O : ι → Y.Opens)
    (hcl : IsClosed (Set.range f)) (hcov : Set.range f ⊆ ⋃ i, (O i : Set Y))
    (hloc : ∀ i, IsClosedImmersion (f ∣_ O i)) : IsClosedImmersion f := by
  let O' : Option ι → Y.Opens := fun o => o.elim ⟨(Set.range f)ᶜ, hcl.isOpen_compl⟩ O
  refine IsZariskiLocalAtTarget.of_iSup_eq_top O' ?_ ?_
  · rw [eq_top_iff]
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ Set.range f
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
      exact ⟨some i, hi⟩
    · exact ⟨none, hy⟩
  · intro o
    cases o with
    | none =>
      have : IsEmpty (f ⁻¹ᵁ O' none).toScheme := ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
    | some i => exact hloc i

theorem range_closed {S X₁ P : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁] (q : P ⟶ S) {V : Scheme.{0}}
    (γ : V ⟶ pullback p₁ q) : IsClosed (Set.range (γ.imageι ≫ pullback.snd p₁ q)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact (pullback.snd p₁ q).isClosedMap _ γ.imageι.isClosedEmbedding.isClosed_range

end LateralTheory.E.CorePf2

end
