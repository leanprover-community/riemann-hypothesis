module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_eval_regular_at_fieldPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z),
      ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k,
        (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧
        ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u →
          ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  intro F _ Y Z _ k _ w
  set z := w (IsLocalRing.closedPoint k) with hz
  let ι := algebraMap (Z.presheaf.stalk z) Z.functionField
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  let e : Z.presheaf.stalk z ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), fun u => by
      obtain ⟨a, ha⟩ := u.2
      exact ⟨a, Subtype.ext ha⟩⟩
  let s : Z.presheaf.stalk z →+* k := (Scheme.stalkClosedPointTo (R := .of k) w).hom
  haveI : IsLocalHom s := Scheme.isLocalHom_stalkClosedPointTo' w
  have he : ∀ a, e.symm ⟨ι a, ⟨a, rfl⟩⟩ = a := fun a => e.symm_apply_eq.2 rfl
  refine ⟨s.comp e.symm.toRingHom, ?_, ?_⟩
  · rintro ⟨_, a, rfl⟩
    change s (e.symm ⟨ι a, ⟨a, rfl⟩⟩) ≠ 0 ↔ _
    rw [he]
    constructor
    · intro h0
      exact ⟨a, isUnit_of_map_unit s a (isUnit_iff_ne_zero.2 h0), rfl⟩
    · rintro ⟨b, hb, hba⟩
      rw [← hι hba]
      exact (hb.map s).ne_zero
  · intro q _ u ⟨a, ha⟩
    subst ha
    have hm := functionFieldMap_algebraMap q z a
    refine ⟨⟨_, hm.symm⟩, ?_⟩
    have h1 : (⟨functionFieldMap q (algebraMap _ Y.X.functionField a), ⟨_, hm.symm⟩⟩ : ι.range) =
        ⟨ι ((q.stalkMap z).hom a), ⟨_, rfl⟩⟩ := Subtype.ext hm
    change s (e.symm _) = _
    rw [h1, he]
    have hw : w ≫ q = spMap (s.comp (q.stalkMap z).hom) ≫ Y.X.fromSpecStalk (q z) := by
      conv_lhs => rw [← spMap_stalkClosedPointTo w]
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
      congr 1
      rw [spMap, spMap, ← Spec.map_comp]
      rfl
    have hv := val_ratOf (Y := Y) (s.comp (q.stalkMap z).hom) a
    exact hv.symm.trans (congrArg (fun p => (ratOf Y).val p (algebraMap _ Y.X.functionField a)) hw.symm)

end GlobalTheory.FlagPush
