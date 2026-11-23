module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory Opposite Limits Abelian

universe w v u

noncomputable section

namespace GlobalTheory.SiteCoh

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

abbrev freeSheaf : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf _ _

variable {J}

def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeSheaf J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj).trans yonedaEquiv)
  map_add' _ _ := rfl

lemma freeSheafHomEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) (f : F ⟶ G) :
    freeSheafHomEquiv U G (φ ≫ f) = f.hom.app (op U) (freeSheafHomEquiv U F φ) := rfl

def freePresheafIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents
    (fun V ↦
      letI : Unique (V.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ ↦ hT.hom_ext _ _⟩
      ((FreeAbelianGroup.uniqueEquiv (V.unop ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {V W} f ↦ by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro x
      rfl)

def freeSheafIsoConst {T : C} (hT : IsTerminal T) :
    (freeSheaf J).obj T ≅ (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf J _).mapIso (freePresheafIsoConst hT)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

def extEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    F.H' n U ≃+ Ext.{w} ((freeSheaf J).obj U) F n :=
  AddEquiv.refl _

abbrev map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C) :
    F.H' n U ⟶ G.H' n U :=
  ((Sheaf.cohomologyPresheafFunctor J n).map f).app (op U)

abbrev res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U) :
    F.H' n U ⟶ F.H' n V :=
  (F.cohomologyPresheaf n).map i.op

lemma extEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C)
    (x : F.H' n U) :
    extEquiv G n U (map f n U x) = (extEquiv F n U x).comp (Ext.mk₀ f) (add_zero n) := rfl

instance cohomologyPresheafFunctor_additive (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor.{w} J n).Additive where
  map_add {F G f g} := by
    ext U x
    apply (extEquiv G n U.unop).injective
    change (extEquiv F n U.unop x).comp (Ext.mk₀ (f + g)) (add_zero n) =
      (extEquiv F n U.unop x).comp (Ext.mk₀ f) (add_zero n) +
        (extEquiv F n U.unop x).comp (Ext.mk₀ g) (add_zero n)
    rw [Ext.mk₀_add, Ext.comp_add]

def zeroEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) : F.H' 0 U ≃+ F.obj.obj (op U) :=
  (extEquiv F 0 U).trans (Ext.addEquiv₀.trans (freeSheafHomEquiv U F))

private lemma extAddEquiv₀_comp_mk₀ {D : Type*} [Category D] [Abelian D] [HasExt.{w} D]
    {X Y Z : D} (x : Ext.{w} X Y 0) (f : Y ⟶ Z) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective X Z).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

private lemma trans_extAddEquiv₀_apply_mk₀ {D : Type*} [Category D] [Abelian D] [HasExt.{w} D]
    {X F : D} {A S : Type*} [Add A] [Add S] (a : A ≃+ Ext.{w} X F 0)
    (s : (X ⟶ F) ≃+ S) (φ : X ⟶ F) :
    (a.trans (Ext.addEquiv₀.trans s)) (a.symm (Ext.mk₀ φ)) = s φ := by
  change s (Ext.addEquiv₀ (a (a.symm (Ext.mk₀ φ)))) = s φ
  rw [a.apply_symm_apply]
  exact congrArg s (Ext.addEquiv₀.apply_symm_apply φ)

lemma zeroEquiv_mk₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) (φ : (freeSheaf J).obj U ⟶ F) :
    zeroEquiv F U ((extEquiv F 0 U).symm (Ext.mk₀ φ)) = freeSheafHomEquiv U F φ :=
  trans_extAddEquiv₀_apply_mk₀ (extEquiv F 0 U) (freeSheafHomEquiv U F) φ

lemma zeroEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    zeroEquiv G U (map f 0 U x) = f.hom.app (op U) (zeroEquiv F U x) := by
  let y := extEquiv F 0 U x
  exact (congrArg (freeSheafHomEquiv U G) (extAddEquiv₀_comp_mk₀ y f)).trans
    (freeSheafHomEquiv_comp U (Ext.addEquiv₀ y) f)

def terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T) :
    F.H' n T ≃+ F.H n :=
  (extEquiv F n T).trans
    (((extFunctor n).mapIso (freeSheafIsoConst (J := J) hT).symm.op).app F).addCommGroupIsoToAddEquiv

private lemma extFunctorIso_apply {D : Type*} [Category D] [Abelian D] [HasExt.{w} D]
    {X Y : D} (e : X ≅ Y) (F : D) (n : ℕ) {A : Type*} [Add A]
    (a : A ≃+ Ext.{w} X F n) (x : A) :
    (a.trans (((extFunctor n).mapIso e.symm.op).app F).addCommGroupIsoToAddEquiv) x =
      (Ext.mk₀ e.inv).comp (a x) (zero_add n) := rfl

lemma terminalEquiv_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C} (hT : IsTerminal T)
    (x : F.H' n T) :
    terminalEquiv F n hT x =
      (Ext.mk₀ (freeSheafIsoConst hT).inv).comp (extEquiv F n T x) (zero_add n) :=
  extFunctorIso_apply (freeSheafIsoConst hT) F n (extEquiv F n T) x

private lemma addCommGroupIso_naturality {D : Type*} [Category D]
    {P Q : D ⥤ AddCommGrpCat.{w}} (e : P ≅ Q) {F G : D} (f : F ⟶ G) (x : P.obj F) :
    (e.app G).addCommGroupIsoToAddEquiv (P.map f x) =
      Q.map f ((e.app F).addCommGroupIsoToAddEquiv x) := by
  have h := ConcreteCategory.congr_hom (e.hom.naturality f) x
  exact h

lemma terminalEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) {T : C}
    (hT : IsTerminal T) (x : F.H' n T) :
    terminalEquiv G n hT (map f n T x) = Sheaf.H.map f n (terminalEquiv F n hT x) := by
  let e := (extFunctor.{w} n).mapIso (freeSheafIsoConst (J := J) hT).symm.op
  have h := addCommGroupIso_naturality e f (extEquiv F n T x)
  exact h

private lemma ext_degree_zero_compare {D : Type*} [Category D] [Abelian D] [HasExt.{w} D]
    {X Y F : D} {A S : Type*} [Add A] [Add S] (e : X ≅ Y)
    (a : A ≃+ Ext.{w} X F 0) (x : A) (s : (Y ⟶ F) ≃+ S) (t : (X ⟶ F) ≃+ S)
    (h : ∀ ψ : Y ⟶ F, s ψ = t (e.hom ≫ ψ))
    {y : Ext.{w} Y F 0} (hy : y = (Ext.mk₀ e.inv).comp (a x) (zero_add 0)) :
    (Ext.addEquiv₀.trans s) y = (a.trans (Ext.addEquiv₀.trans t)) x := by
  change s (Ext.addEquiv₀ y) = t (Ext.addEquiv₀ (a x))
  rw [hy]
  generalize a x = z
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective X F).surjective z
  have hinv (ψ : Y ⟶ F) : Ext.addEquiv₀ (Ext.mk₀.{w} ψ) = ψ :=
    Ext.addEquiv₀.apply_symm_apply ψ
  rw [Ext.mk₀_comp_mk₀, hinv, h, Iso.hom_inv_id_assoc]
  exact congrArg t (Ext.addEquiv₀.apply_symm_apply φ).symm

lemma equiv₀_terminalEquiv (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T)
    (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (terminalEquiv F 0 hT x) = zeroEquiv F T x := by
  let e := freeSheafIsoConst (J := J) hT
  let s := ((constantSheafAdj J AddCommGrpCat hT).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  refine ext_degree_zero_compare e (extEquiv F 0 T) x s
    (freeSheafHomEquiv T F) ?_ (terminalEquiv_apply F 0 hT x)
  intro ψ
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (freePresheafIsoConst hT).hom) (op T))
    (FreeAbelianGroup.of (𝟙 T))
  exact (congrArg (ψ.hom.app (op T)) h₁).trans (freeSheafHomEquiv_comp T e.hom ψ).symm

end GlobalTheory.SiteCoh
