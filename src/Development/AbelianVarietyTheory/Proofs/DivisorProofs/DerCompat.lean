module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSAgree

theorem dual_alg {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (dualMap r).comp (algebraMap S (DualNumber S)) = (algebraMap S' (DualNumber S')).comp r := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

theorem fst_dual {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (dualMap r) = r.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext a <;> (try simp [dualMap]) <;> rfl

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem eps_over {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') :
    spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ x' := by
  have h : spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap r := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', dual_alg]
  rw [← hx, ← Category.assoc, ← Category.assoc, h]

theorem tan_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t x' (spMap (dualMap r) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, eps_over r hx]
  · have h : spMap (TrivSqZeroExt.fstHom S' S' S').toRingHom ≫ spMap (dualMap r) =
        spMap r ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', fst_dual]
    rw [← Category.assoc, h, Category.assoc, hv.2]
    let k : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap r) hx
    exact congrArg CommaMorphism.left (comp_one k (M := t.G))

end Gen

theorem tan_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsTanAtG t (chart U) v → IsTanAtG t (chart W) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v) :=
  fun _ _ _ _ _ _ t U W hW _ hv => tan_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) hv

end GlobalTheory.KSAgree
