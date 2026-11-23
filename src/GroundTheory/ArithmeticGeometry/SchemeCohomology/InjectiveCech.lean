module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Sheaves.SheafOfFunctions

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits

universe w u

variable {X : TopCat.{u}}

lemma discPresheaf_isSheaf (A : X → AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (discPresheaf A) := by
  have h := TopCat.Presheaf.toTypes_isSheaf X (fun x => A x)
  have := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u}) (discPresheaf A)).2
  exact this h

noncomputable def germSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨discPresheaf (fun x => F.presheaf.stalk x), discPresheaf_isSheaf _⟩

noncomputable def toGerms (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.presheaf ⟶ discPresheaf (fun x => F.presheaf.stalk x) where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s x => F.presheaf.germ W.unop x.1 x.2 s
      map_zero' := by funext x; simp
      map_add' := fun s t => by funext x; simp }
  naturality W W' h := by
    ext s
    funext x
    exact F.presheaf.germ_res_apply h.unop x.1 x.2 s

lemma toGerms_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : (Opens X)ᵒᵖ) :
    Function.Injective ((toGerms F).app W) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F W.unop s t
  intro x hx
  exact congrFun h ⟨x, hx⟩

noncomputable def toGermSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F ⟶ germSheaf F :=
  ObjectProperty.homMk (toGerms F)

instance (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono (toGermSheaf F) := by
  have : ∀ W, Mono ((toGerms F).app W) := fun W =>
    (AddCommGrpCat.mono_iff_injective _).2 (toGerms_injective F W)
  have : Mono (toGermSheaf F).hom := NatTrans.mono_of_mono_app (toGerms F)
  exact Sheaf.Hom.mono_of_presheaf_mono (f := toGermSheaf F)

theorem cechAcyclic_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I]
    {ι : Type w} (U : ι → Opens X) : CechAcyclic I.obj U := by
  let r := Injective.factorThru (𝟙 I) (toGermSheaf I)
  have hr : toGermSheaf I ≫ r = 𝟙 I := Injective.comp_factorThru _ _
  have hr' : toGerms I ≫ r.hom = 𝟙 I.obj := congrArg (fun f => f.hom) hr
  exact CechAcyclic.of_retract (U := U) (toGerms I) r.hom hr' (cechAcyclic_discPresheaf U _)

end GroundTheory.Arith.SchemeCoh
