module

public import Mathlib.AlgebraicGeometry.Sites.Etale
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

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem mem_etaleTopology_of_pullback_finite : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  intro Z X f _ _ T hT hE
  let U : X.Opens := ⟨(Set.range f.base)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hU : IsEmpty (pullback f U.ι : Scheme.{0}) := by
    refine ⟨fun p => ?_⟩
    have h1 : (pullback.snd f U.ι ≫ U.ι).base p = (pullback.fst f U.ι ≫ f).base p := by
      rw [pullback.condition]
    have h2 : (pullback.snd f U.ι ≫ U.ι).base p ∈ U := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
      have hr := U.range_ι
      exact (Set.ext_iff.1 hr _).1 ⟨_, rfl⟩
    rw [h1, Scheme.Hom.comp_base, TopCat.comp_app] at h2
    exact h2 ⟨_, rfl⟩
  have hTU : T U.ι := hE U.ι hU
  let V : Bool → Scheme.{0} := fun b => Bool.rec U.toScheme Z b
  let j : ∀ b, V b ⟶ X := fun b => match b with
    | true => f
    | false => U.ι
  have hmem : Presieve.ofArrows V j ∈ Scheme.etalePrecoverage X := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : x ∈ Set.range f.base
      · obtain ⟨z, rfl⟩ := hx
        exact ⟨true, z, rfl⟩
      · exact ⟨false, ⟨x, hx⟩, rfl⟩
    · cases b
      · change Etale U.ι
        infer_instance
      · change Etale f
        infer_instance
  refine Scheme.etaleTopology.transitive (Precoverage.generate_mem_toGrothendieck hmem) _ ?_
  rintro W g ⟨Y, h, k, ⟨b⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine Scheme.etaleTopology.pullback_stable h ?_
  cases b
  · change T.pullback U.ι ∈ _
    rw [Sieve.pullback_eq_top_of_mem _ hTU]
    exact Scheme.etaleTopology.top_mem _
  · exact hT

end GlobalTheory.EtC.Tr
