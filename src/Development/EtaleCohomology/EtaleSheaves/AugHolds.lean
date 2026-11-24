module

public import Development.EtaleCohomology.EtaleSheaves.AugBij
public import Mathlib.Topology.Instances.ZMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationSheaf

variable (q : ℕ)

def CP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj U := ModuleCat.of _ C(U.unop, ULift.{1} (ZMod q))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ContinuousMap.comp g f.unop.base.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem isSheaf_etaleTopology_continuousMaps : Presheaf.IsSheaf Scheme.etaleTopology.{0} (CP q) := by
  apply Presheaf.IsSheaf.of_le (le_trans Scheme.etaleTopology_le_proetaleTopology Scheme.proetaleTopology_le_fpqcTopology)
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    reflectsLimitsOfSize_shrink.{1, 1, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))
  exact isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{1} (ZMod q))

def augA (U : Scheme.{0}) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U) →ₗ[ULift.{1} (ZMod q)] C(U, ULift.{1} (ZMod q)) :=
  (twRel q 0 Γ(U, ⊤)).liftQ (Finsupp.linearCombination _ (fun _ => (1 : C(U, ULift.{1} (ZMod q))))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, -, rfl⟩
    simp)

def augP : Scheme.Γ ⋙ twF q 0 ⟶ CP q where
  app U := ModuleCat.ofHom (augA q U.unop)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro ζ c
    apply ContinuousMap.ext; intro t
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change (augA q V.unop) (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ζ c))) t =
      (augA q U.unop (Submodule.Quotient.mk (Finsupp.single ζ c))) (f.unop.base t)
    simp only [augA]
    erw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    rfl

def augS : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0) ⟶ CP q :=
  sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q)

def augC (T : Scheme.{0}) (x : Sec (tw q 0) T) : C(T, ULift.{1} (ZMod q)) := ((augS q).app (Opposite.op T)).hom x

def aug (T : Scheme.{0}) : Sec (tw q 0) T →+ LocallyConstant T (ZMod q) :=
  AddMonoidHom.mk' (fun x => ⟨fun t => (augC q T x t).down,
      (IsLocallyConstant.iff_continuous _).2 (continuous_uliftDown.comp (ContinuousMap.continuous _))⟩)
    (fun x y => by
      ext t
      simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.coe_mk, augC]
      erw [LinearMap.map_add]
      rfl)

theorem aug_nat {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U) :
    aug q V (Sec.res g x) = (aug q U x).comap g.base.hom := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom h) x) ((augS q).naturality g.op)
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_comap, Function.comp_apply]
  exact congrArg (fun k : C(V, ULift.{1} (ZMod q)) => (k t).down) h

theorem aug_gen (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) : aug q U (twGen 0 ζ) = 1 := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom (NatTrans.app h (Opposite.op U))) (Submodule.Quotient.mk (Finsupp.single ζ 1)))
    (toSheafify_sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q))
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_one, Pi.one_apply]
  have h2 := congrArg (fun k : C(U, ULift.{1} (ZMod q)) => (k t).down) h
  refine h2.trans ?_
  simp only [augP, augA]
  erw [ModuleCat.hom_ofHom, Submodule.liftQ_apply, Finsupp.linearCombination_single]
  simp

theorem Aug_holds : LateralTheory.E.TateTwistZeroAugmentationBijective.Aug := fun q => ⟨aug q, fun g x => aug_nat q g x, aug_gen q⟩

theorem Tw0_of (hB : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij) : LateralTheory.E.LCIsoPf.Tw0 := LateralTheory.E.TateTwistZeroAugmentationBijective.Tw0_of Aug_holds hB

end LateralTheory.E.TateTwistZeroAugmentationSheaf
