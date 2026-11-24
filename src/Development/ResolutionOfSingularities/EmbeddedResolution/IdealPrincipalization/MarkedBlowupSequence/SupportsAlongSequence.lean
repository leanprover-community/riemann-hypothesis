module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem projectionToBase_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom := by
  have h0 : s.toSequenceOfBlowups.transitionMap (le_refl 0) = 𝟙 (s.toSequenceOfBlowups.schemeAt 0) := by
    rw [SequenceOfBlowups.transitionMap_def]
    have hid : (CategoryTheory.homOfLE (le_refl (0 : ℕ))).op = 𝟙 (Opposite.op (0 : ℕ)) := rfl
    rw [hid, CategoryTheory.Functor.map_id]
  rw [SequenceOfBlowups.projectionToBase_def, h0, Category.id_comp]

theorem projectionToBase_succ_apply (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (x : ↥(s.toSequenceOfBlowups.schemeAt (i + 1))) :
    (s.toSequenceOfBlowups.projectionToBase (i + 1)).base x =
      (s.toSequenceOfBlowups.projectionToBase i).base ((s.toSequenceOfBlowups.transitionMapSucc i).base x) := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i =
      s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)
  rw [← h]
  rfl

theorem comap_ideal_le_ideal_succ (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (hi : i < s.toSequenceOfBlowups.length) :
    (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) ≤ s.ideal (i + 1) := by
  rw [← s.ideal_succ i hi]
  exact fun U => Ideal.mul_le_right

theorem support_ideal_succ_subset_preimage (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (hi : i < s.toSequenceOfBlowups.length) :
    (((s.ideal (i + 1)).support : Set ↥(s.toSequenceOfBlowups.schemeAt (i + 1)))) ⊆
      ⇑(s.toSequenceOfBlowups.transitionMapSucc i).base ⁻¹'
        (((s.ideal i).support : Set ↥(s.toSequenceOfBlowups.schemeAt i))) := by
  refine subset_trans (SetLike.coe_subset_coe.mpr
    (Scheme.IdealSheafData.support_antitone (s.comap_ideal_le_ideal_succ i hi))) ?_
  exact (Scheme.IdealSheafData.support_comap _ _).le

end MarkedSequenceOfBlowups

theorem MarkedIdealWithBoundary.IsAdmissible.isNoetherian {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) :
    AlgebraicGeometry.IsNoetherian T.scheme := by
  have : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : AlgebraicGeometry.QuasiCompact T.structMap := hV.quasiCompact
  have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of T.base)) := inferInstance
  exact isNoetherian_of_locallyOfFiniteType T.structMap

end FunctorialResolution.EmbeddedResolution
