module

public import Development.EtaleCohomology.EtaleSheaves.LineOneCut
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FiberCover
open LateralTheory.E.LineOneCut

lemma fibMap_eq {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fibMap p ι = (pullbackRightPullbackFstIso p (cpt A) ι).inv ≫ pullback.snd ι (pullback.fst p (cpt A)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]; exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    simp [fibMap]

lemma fibMap_open {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z)
    [IsOpenImmersion ι] : IsOpenImmersion (fibMap p ι) := by
  rw [fibMap_eq]; infer_instance

lemma fibMap_range {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    Set.range (fibMap p ι) = (pullback.fst p (cpt A)) ⁻¹' Set.range ι := by
  rw [fibMap_eq, ← Scheme.Pullback.range_snd]
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackRightPullbackFstIso p (cpt A) ι).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem FibCover_of : FibCover := by
  intro A _ _ Z U V p ι₁ ι₂ h1 h2 hcov
  refine ⟨fibMap_open p ι₁, fibMap_open p ι₂, ?_⟩
  rw [fibMap_range, fibMap_range, ← Set.preimage_union, hcov, Set.preimage_univ]

end LateralTheory.E.FiberCover
