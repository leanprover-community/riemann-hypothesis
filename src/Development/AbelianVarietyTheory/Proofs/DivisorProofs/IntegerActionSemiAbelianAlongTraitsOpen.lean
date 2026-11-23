module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionExtendsSemiAbelianThetaModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericSemiAbelianCompleteDVRStatement
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem oAct_along_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  obtain ⟨f, hfm, H0⟩ := GlobalTheory.T.integerAction_extends_semiAbelian_thetaModel E H Dw l Xo c C X₁ M U₀ EE out hAdm
  refine ⟨f, hfm, ?_⟩
  rintro T ξ ⟨ξ₀, hξ₀, hlies⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) ξ₀ T.y hlies tK ⟨m₂⟩
  obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi M.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart
    (hγ.congr hξ₀ rfl)
  refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
  have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    exact ⟨w, hw⟩
  have hL := out.L.isLB
  refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
  exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
    (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
      (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
