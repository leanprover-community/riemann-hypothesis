module

public import Development.EtaleCohomology.EtaleSheaves.NbIsoPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
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

namespace LateralTheory.E.FlatMonoLimPf

theorem exists_lift {X Y T : Scheme.{0}} (m : X ⟶ Y) [Mono m] [Flat m] [QuasiCompact m] (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range m) : ∃ b : T ⟶ X, b ≫ m = t := by
  have hs : Surjective (pullback.fst t m) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩
  have : IsIso (pullback.fst t m) := Flat.isIso_of_surjective_of_mono _
  refine ⟨inv (pullback.fst t m) ≫ pullback.snd t m, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

theorem FlatMonoLim_of : LateralTheory.E.NbIsoPf.FlatMonoLim := by
  intro Y J _ _ D ι hι hc X m hm hf hq hr c hl
  have ho : ∀ j, IsOpenImmersion (ι j) := fun j => (hι j).1
  have hsub : ∀ j, Set.range m ⊆ Set.range (ι j) := fun j => hr ▸ Set.iInter_subset _ j
  have hind : ∀ j k, c.π.app j ≫ ι j = c.π.app k ≫ ι k := by
    intro j k
    rw [← c.w (IsCofiltered.minToLeft j k), ← c.w (IsCofiltered.minToRight j k), Category.assoc, Category.assoc,
      hc, hc]
  obtain ⟨j0⟩ : Nonempty J := IsCofiltered.nonempty
  have hp : Set.range (c.π.app j0 ≫ ι j0) ⊆ Set.range m := by
    rw [hr]
    refine Set.subset_iInter fun j => ?_
    rw [hind j0 j]
    rintro _ ⟨x, rfl⟩
    exact ⟨c.π.app j x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := exists_lift m _ hp
  let s : Cone D :=
    { pt := X
      π :=
        { app := fun j => IsOpenImmersion.lift (ι j) m (hsub j)
          naturality := fun j k f => by
            rw [← cancel_mono (ι k)]
            simp [hc] } }
  have hs : ∀ j, hl.lift s ≫ c.π.app j ≫ ι j = m := by
    intro j
    rw [hl.fac_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨b, hl.lift s, ?_, ?_⟩⟩
  · refine hl.hom_ext fun j => ?_
    rw [← cancel_mono (ι j)]
    simp only [Category.assoc]
    erw [hs j, hb, Category.id_comp]
    exact hind j0 j
  · rw [← cancel_mono m, Category.assoc, hb, hs, Category.id_comp]

end LateralTheory.E.FlatMonoLimPf
