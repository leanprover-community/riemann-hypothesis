module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPf
public import Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPfEv
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sch_clsPfYon

variable (R : Type) [CommRing R]

def yon0 (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (freeP R).obj (yoneda.obj X) ⟶ G.obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (U.unop ⟶ X)) (TypeCat.ofHom (fun g : ULift.{1} (U.unop ⟶ X) => (G.obj.map g.down.op).hom z))
  naturality U V f := by
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    have e1 : (((freeP R).obj (yoneda.obj X)).map f).hom (ModuleCat.freeMk (ULift.up g)) =
        ModuleCat.freeMk (ULift.up (f.unop ≫ g)) := ModuleCat.free_map_apply (R := ULift.{1} R) _ _
    erw [ConcreteCategory.comp_apply, e1, ConcreteCategory.comp_apply, ModuleCat.freeDesc_apply]
    erw [ModuleCat.freeDesc_apply]
    show (G.obj.map (f.unop ≫ g).op).hom z = (G.obj.map f).hom ((G.obj.map g.op).hom z)
    rw [op_comp, Functor.map_comp]
    rfl

def yon (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (free R).obj (yoneda.obj X) ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.property⟩

theorem yon_gen (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : Sec.map (yon R G X z) (freeGen R _ X (𝟙 X)) = z := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.property
  have := congrArg (fun φ => (φ.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) h
  refine this.trans ?_
  dsimp only [yon0]
  erw [ModuleCat.freeDesc_apply]
  simp

theorem yon_ext {G : Shv R} {X : Scheme.{0}} (φ ψ : (free R).obj (yoneda.obj X) ⟶ G)
    (h : Sec.map φ (freeGen R _ X (𝟙 X)) = Sec.map ψ (freeGen R _ X (𝟙 X))) : φ = ψ := by
  have key : ∀ (U : Scheme.{0}) (g : U ⟶ X), Sec.map φ (freeGen R _ U g) = Sec.map ψ (freeGen R _ U g) := by
    intro U g
    have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
      rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
      simp
    rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, h]
  have hv : φ.hom = ψ.hom := by
    apply sheafify_hom_ext Scheme.etaleTopology _ _ G.property
    refine NatTrans.ext (funext fun U => ?_)
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    exact key U.unop g
  first | exact Sheaf.hom_ext hv | (cases φ; cases ψ; cases hv; rfl)

theorem yon_res {G : Shv R} {X : Scheme.{0}} (z : Sec G X) (U : Scheme.{0}) (g : U ⟶ X) :
    Sec.map (yon R G X z) (freeGen R _ U g) = Sec.res g z := by
  have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
    rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
    simp
  rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, yon_gen]

end LateralTheory.E.L_sch_clsPfYon
