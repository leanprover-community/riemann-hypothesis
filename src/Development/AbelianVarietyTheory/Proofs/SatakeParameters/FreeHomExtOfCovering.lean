module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

theorem freePresheaf_map_app_freeMk (R : Type) [CommRing R] {P Q : Scheme.{0}ᵒᵖ ⥤ Type} (α : P ⟶ Q) (U : Scheme.{0}ᵒᵖ)
    (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).map α).app U) (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (α.app U x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ Type) {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V)
    (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).obj P).map f) (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map f x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_map_comp_app_freeMk (R : Type) [CommRing R] {P Q : Scheme.{0}ᵒᵖ ⥤ Type}
    {G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (α : P ⟶ Q) (β : (GlobalTheory.EtC.freeP R).obj Q ⟶ G)
    (U : Scheme.{0}ᵒᵖ) (x : P.obj U) :
    ConcreteCategory.hom (((GlobalTheory.EtC.freeP R).map α ≫ β).app U) (ModuleCat.freeMk (ULift.up x)) =
      ConcreteCategory.hom (β.app U) (ModuleCat.freeMk (ULift.up (α.app U x))) :=
  congrArg (ConcreteCategory.hom (β.app U)) (freePresheaf_map_app_freeMk R α U x)

theorem freePresheaf_hom_naturality_freeMk (R : Type) [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ Type}
    {G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (β : (GlobalTheory.EtC.freeP R).obj P ⟶ G)
    {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (x : P.obj U) :
    ConcreteCategory.hom (G.map f) (ConcreteCategory.hom (β.app U) (ModuleCat.freeMk (ULift.up x))) =
      ConcreteCategory.hom (β.app V) (ModuleCat.freeMk (ULift.up (P.map f x))) := by
  have h := ConcreteCategory.congr_hom (β.naturality f) (ModuleCat.freeMk (ULift.up x))
  exact h.symm.trans (congrArg (ConcreteCategory.hom (β.app V)) (freePresheaf_obj_map_freeMk R P f x))

end GlobalTheory.EtC.Tr

namespace GlobalTheory.EtC.Tr

theorem free_hom_ext_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R)
    (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S) (hT : T ∈ Scheme.etaleTopology S)
    (h : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v →
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) : φ = ψ := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((GlobalTheory.EtC.freeP R).obj (yoneda.obj S)) F).injective
  have key : ∀ ⦃W : Scheme.{0}⦄ (v : W ⟶ S), T v →
      ConcreteCategory.hom ((adj.homEquiv _ F φ).app (op W)) (ModuleCat.freeMk (ULift.up v)) =
      ConcreteCategory.hom ((adj.homEquiv _ F ψ).app (op W)) (ModuleCat.freeMk (ULift.up v)) := by
    intro W v hv
    have e : ∀ χ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F,
        adj.homEquiv _ F ((GlobalTheory.EtC.free R).map (yoneda.map v) ≫ χ) =
          (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F χ := fun χ =>
      adj.homEquiv_naturality_left _ _
    have h' : (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F φ =
        (GlobalTheory.EtC.freeP R).map (yoneda.map v) ≫ adj.homEquiv _ F ψ := by
      rw [← e φ, ← e ψ]; exact congrArg (adj.homEquiv _ F) (h v hv)
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app h' (op W)) (ModuleCat.freeMk (ULift.up (𝟙 W)))
    rw [freePresheaf_map_comp_app_freeMk, freePresheaf_map_comp_app_freeMk] at h1
    have hv1 : ConcreteCategory.hom ((yoneda.map v).app (op W)) (𝟙 W) = v := Category.id_comp v
    rw [hv1] at h1
    exact h1
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨g⟩
  apply Sheaf.isSeparated F U.unop (T.pullback g) (Scheme.etaleTopology.pullback_stable g hT)
  intro W w hw
  have nat : ∀ χ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F,
      ConcreteCategory.hom (F.obj.map w.op) (ConcreteCategory.hom ((adj.homEquiv _ F χ).app U)
        (ModuleCat.freeMk (ULift.up g))) =
        ConcreteCategory.hom ((adj.homEquiv _ F χ).app (op W)) (ModuleCat.freeMk (ULift.up (w ≫ g))) :=
    fun χ => freePresheaf_hom_naturality_freeMk R (adj.homEquiv _ F χ) w.op g
  exact (nat φ).trans ((key (w ≫ g) hw).trans (nat ψ).symm)

end GlobalTheory.EtC.Tr
