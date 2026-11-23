module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GoodRed

theorem subsingleton_lattice_of_extends : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F)
    (ξ : Sp T.V ⟶ F.X), jK T.V ≫ ξ = T.y → Subsingleton T.D.toPre.X := by
  intro g n o _ ζ F T ξ hξ

  have hB := GlobalTheory.isAbelianScheme_pullback_obj ξ F.univ.A F.univ.ab
  haveI := T.U.gen_hom

  have h₁ := ((isGrpPullback_of_iso T.U.gen).comp T.cart).congr ((Category.id_comp _).trans hξ.symm) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj F.univ.A) (jK T.V)).comp (isGrpPullback_pullback F.univ.A ξ)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨E, -, -⟩ := TraitUniq.extIso T.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.G.hom := by
    have := hB.proper
    have : IsIso E.hom.left := inferInstanceAs (IsIso ((Over.forget _).map E.hom))
    rw [← Over.w E.hom]
    infer_instance

  have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  letI := hF.toField
  let k := T.U.gt 0
  have m : Mono k.i := ⟨fun a b h => k.isKernel.hom_ext h (CartesianMonoidalCategory.toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus T.G T.semi _ hF _ (closedPoint _)
    (fun _ _ _ _ _ => inferInstance) T.D.toPre.X k.i k.i_hom

end GlobalTheory.Poinc.GoodRed
