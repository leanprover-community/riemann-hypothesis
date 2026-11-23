module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.StalkJet

variable {k : Type} [Field k]

theorem isLocalRing_of_aug {A : Type} [CommRing A] [Algebra k A] (aug : A →ₐ[k] k) {n : ℕ}
    (h : RingHom.ker aug ^ n = ⊥) : IsLocalRing A := by
  haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial
  have nil : ∀ a : A, aug a = 0 → IsNilpotent a := fun a ha =>
    ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : aug a = 0
  · exact Or.inr (nil a ha).isUnit_one_sub
  · left
    have h1 : IsNilpotent (a - algebraMap k A (aug a)) := nil _ (by simp)
    have h2 : IsUnit (algebraMap k A (aug a)) := (IsUnit.mk0 _ ha).map _
    have := h1.isUnit_add_right_of_commute h2 (Commute.all _ _)
    simpa using this

theorem exists_factor {B : Over (Sp k)} (b : B.left) [Algebra k (B.left.presheaf.stalk b)]
    (hb : B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)))
    {A : Type} [CommRing A] [Algebra k A] [IsLocalRing A] (y : algOver k A ⟶ B)
    (hy : y.left (closedPoint A) = b) :
    ∃ τ : B.left.presheaf.stalk b →ₐ[k] A, IsLocalHom τ ∧
      spMap (τ : B.left.presheaf.stalk b →+* A) ≫ B.left.fromSpecStalk b = y.left := by
  subst hy
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left
  have w : y.left ≫ B.hom = spMap (algebraMap k A) := Over.w y
  have e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫
      Scheme.stalkClosedPointTo (R := .of A) y.left = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ w
    exact (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))
  refine ⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩
  · exact congrArg (fun q => q.hom c) e2
  · exact ⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩

end GlobalTheory.StalkJet
