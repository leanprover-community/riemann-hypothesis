module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesLimits : PreservesLimitsOfSize.{0, 0} sch := by
  unfold sch
  infer_instance

theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) :=
  h.map sch

theorem isPullback_resLE {Y X : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) :
    IsPullback (w ⁻¹ᵁ U).ι (w.resLE U (w ⁻¹ᵁ U) le_rfl) w U.ι := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict w U).flip

theorem LeafAbv_of : LeafAbv := by
  intro Y X w U' U h
  subst h
  have hP := sch_isPullback (isPullback_resLE w U)
  refine ⟨Arrow.isoMk hP.isoPullback (Iso.refl _) ?_, rfl, ?_⟩
  · simp [opn, abv]
  · apply Arrow.hom_ext
    · rw [Arrow.comp_left]
      exact hP.isoPullback_hom_snd
    · rw [Arrow.comp_right]
      exact Category.id_comp _

end LateralTheory.CohomologicalPurity.TubeCut
