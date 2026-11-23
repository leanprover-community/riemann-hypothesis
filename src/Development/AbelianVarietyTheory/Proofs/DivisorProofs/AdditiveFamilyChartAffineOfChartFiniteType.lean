module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffineStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualApprox

theorem evc_comp_of_same {S : Scheme.{0}} {A T T₀ Y : Over S} {N : LB (A ⊗ T).left} {N₀ : LB (A ⊗ T₀).left}
    (hN : N.IsLB) (hN₀ : N₀.IsLB) (h : T ⟶ T₀) (hs : Same A N N₀ (𝟙 T) h) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = evc hN₀ (fst A Y) (snd A Y ≫ y ≫ h) := by
  rw [same_iff hN hN₀, Category.comp_id] at hs
  have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) hs
  rw [pull_evc, pull_evc] at this
  simp only [lift_fst, lift_snd, lift_snd_assoc, Category.assoc] at this
  exact this

theorem chartAt_of_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → (∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro R _ _ A _ hA U M hM hfin T _ N hN
  obtain ⟨T₀, h, N₀, hT₀, hft, hN₀, hs⟩ := GlobalTheory.T.exists_finiteType_additiveLineBundleFamily_affine R A hA T N hN
  obtain ⟨W₀, hW₀⟩ := hfin T₀ hft N₀ hN₀
  refine ⟨h.left ⁻¹ᵁ W₀, fun Y y ↦ ?_⟩
  have key : ∀ u : Y ⟶ U, Same A N M y u ↔ Same A N₀ M (y ≫ h) u := fun u ↦ by
    rw [same_iff hN.isLB hM.isLB, same_iff hN₀.isLB hM.isLB, evc_comp_of_same hN.isLB hN₀.isLB h hs y]
  simp_rw [key, hW₀ Y (y ≫ h)]
  rfl

end GlobalTheory.DualApprox
