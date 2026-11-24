module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleModelOfIsColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleTensorProductLeft
import Mathlib.Algebra.Category.Ring.FinitePresentation
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtaleComp

theorem isIndEtale_of_model (X E Y G F : Type) [CommRing X] [CommRing E] [CommRing Y] [CommRing G]
    [CommRing F] [Algebra X E] [Algebra X Y] [Algebra E Y] [IsScalarTower X E Y]
    [Algebra.Etale X E] [Algebra E G] [Algebra.Etale E G] [Algebra Y F]
    (e : Y ⊗[E] G ≃ₐ[Y] F) (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap X Y)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap Y F).comp (algebraMap X Y)) := by
  have h1 := GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale X E Y h
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left E Y G h1
  letI : Algebra G F :=
    ((e : Y ⊗[E] G →+* F).comp (Algebra.TensorProduct.includeRight : G →ₐ[E] Y ⊗[E] G).toRingHom).toAlgebra
  let e' : G ⊗[E] Y ≃ₐ[G] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm E G Y).toRingEquiv.trans e.toRingEquiv)
      (fun g => rfl)
  have h3 := GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e' h2
  have h4 : RingHom.Etale ((algebraMap E G).comp (algebraMap X E)) :=
    RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 inferInstance)
      (RingHom.etale_algebraMap.2 inferInstance)
  have h5 := GlobalTheory.EtC.isIndEtale_comp_etale _ h4 _ h3
  have h6 : (algebraMap Y F).comp (algebraMap X Y) =
      (algebraMap G F).comp ((algebraMap E G).comp (algebraMap X E)) := by
    ext x
    change _ = e ((1 : Y) ⊗ₜ[E] algebraMap E G (algebraMap X E x))
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply E Y (Y ⊗[E] G),
      e.commutes, ← IsScalarTower.algebraMap_apply X E Y]
    rfl
  rw [h6]
  exact h5

theorem isIndEtale_etale_comp {X Y F : Type} [CommRing X] [CommRing Y] [CommRing F]
    (f : X →+* Y) (g : Y →+* F) (hf : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f) (hg : g.Etale) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  have hf' := hf
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hf'
  letI : Algebra Y F := g.toAlgebra
  haveI : Algebra.Etale Y F := hg
  obtain ⟨i, G, _, _, hG, ⟨e⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D (Cocone.mk (CommRingCat.of Y) t) hs F
  letI : Algebra (D.obj i) Y := (t.app i).hom.toAlgebra
  letI : Algebra X (D.obj i) := (s.app i).hom.toAlgebra
  letI : Algebra X Y := f.toAlgebra
  haveI : Algebra.Etale X (D.obj i) := (hj i).1
  haveI : IsScalarTower X (D.obj i) Y := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun φ : CommRingCat.of X ⟶ CommRingCat.of Y => φ.hom x) (hj i).2).symm)
  exact isIndEtale_of_model X (D.obj i) Y G F e hf

theorem isIndEtale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  intro X Y Z _ _ _ f g hf hg
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom f) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · exact isIndEtale_etale_comp (F := D.obj j) f (s.app j).hom hf (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom f ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp f)
    rw [h2]
    rfl

end GlobalTheory.IndEtaleComp
