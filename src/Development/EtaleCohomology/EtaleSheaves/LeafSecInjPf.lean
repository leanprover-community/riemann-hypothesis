module

public import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
public import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
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
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafSecInjPf

universe u v w

instance evaluationLeftAdjoint_preservesMono {C : Type u} [Category.{0} C] (R' : Type 1) [Ring R'] (c : C) :
    (evaluationLeftAdjoint (ModuleCat.{1} R') c).PreservesMonomorphisms where
  preserves {d₁ d₂} f _ := by
    rw [NatTrans.mono_iff_mono_app']
    intro t
    have e : ((evaluationLeftAdjoint (ModuleCat.{1} R') c).map f).app t =
        Limits.Sigma.map (fun _ : c ⟶ t => f) := by
      apply Limits.Sigma.hom_ext; intro h
      erw [Limits.Sigma.ι_desc]
    rw [e]
    have : HasCoproducts.{0} (ModuleCat.{1} R') := hasCoproducts_shrink.{0, 1}
    have : AB4OfSize.{0} (ModuleCat.{1} R') := AB4OfSize_shrink.{0, 1} _
    have : HasExactColimitsOfShape (Discrete (c ⟶ t)) (ModuleCat.{1} R') := AB4OfSize.ofShape _
    have : (MorphismProperty.monomorphisms (ModuleCat.{1} R')).IsStableUnderCoproductsOfShape (c ⟶ t) :=
      MorphismProperty.isStableUnderColimitsOfShape_monomorphisms _ _
    exact MorphismProperty.colimMap (W := MorphismProperty.monomorphisms (ModuleCat.{1} R'))
      (J := Discrete (c ⟶ t)) _ (fun _ => (inferInstance : Mono f))

theorem secInj (R : Type) [CommRing R] (F : Shv R) (hF : Injective F) (U : Scheme.{0}) :
    Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
      (evaluation _ _).obj (op U)).obj F) :=
  ((evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))).map_injective _ hF

theorem LeafSecInj_of : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := by
  intro R _ F hF U
  have h := secInj R F hF U
  exact (Module.injective_iff_injective_object (ULift.{1} R) (Sec F U)).mpr h

end LateralTheory.E.LeafSecInjPf
