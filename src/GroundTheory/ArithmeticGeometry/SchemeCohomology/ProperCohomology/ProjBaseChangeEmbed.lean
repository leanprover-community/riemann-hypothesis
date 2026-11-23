module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChangeTwist
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} {Y : Scheme.{u}}


variable (A B n) in
def baseChangeIso :
    projectiveSpace B n ≅
      pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  (isPullback_baseChange A B n).isoPullback

lemma baseChangeIso_inv_baseChangeMap :
    (baseChangeIso A B n).inv ≫ baseChangeMap A B n = pullback.fst _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_fst

lemma baseChangeIso_inv_toSpecBase :
    (baseChangeIso A B n).inv ≫ toSpecBase B n = pullback.snd _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_snd

def toBaseChange (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    Y ⟶ projectiveSpace B n :=
  ι ≫ (baseChangeIso A B n).inv

instance (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [IsClosedImmersion ι] : IsClosedImmersion (toBaseChange ι) := by
  rw [toBaseChange]
  infer_instance

lemma toBaseChange_baseChangeMap
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ baseChangeMap A B n = ι ≫ pullback.fst _ _ := by
  rw [toBaseChange]
  calc
    _ = ι ≫ ((baseChangeIso A B n).inv ≫ baseChangeMap A B n) := by rw [Category.assoc]
    _ = _ := congrArg (fun f => ι ≫ f) (baseChangeIso_inv_baseChangeMap (A := A) (B := B) (n := n))

lemma toBaseChange_toSpecBase
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ toSpecBase B n = ι ≫ pullback.snd _ _ := by
  rw [toBaseChange]
  calc
    _ = ι ≫ ((baseChangeIso A B n).inv ≫ toSpecBase B n) := by rw [Category.assoc]
    _ = _ := congrArg (fun f => ι ≫ f) (baseChangeIso_inv_toSpecBase (A := A) (B := B) (n := n))


variable (A) in
def twistingSheafBaseChangeIso (g : Y ⟶ projectiveSpace B n) (k : ℤ) :
    ProjScheme.twistingSheaf (g ≫ baseChangeMap A B n) k ≅ ProjScheme.twistingSheaf g k :=
  ((Scheme.Modules.pullbackComp g (baseChangeMap A B n)).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (pullbackTwistingSheafIso A B n k)


variable (A) in
def twistBaseChangeIso (g : Y ⟶ projectiveSpace B n) (F : Y.Modules) (k : ℤ) :
    ProjScheme.twist (g ≫ baseChangeMap A B n) F k ≅ ProjScheme.twist g F k :=
  whiskerLeftIso F (twistingSheafBaseChangeIso A g k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
