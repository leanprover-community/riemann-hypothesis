module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_grpPullback_chart_to_ext : ∀ (X S : Scheme.{0}) (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  intro X S j _ _ A _ G _ e hG he x C
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R
  have hG' : IsSemiAbelian ((Over.pullback C.ξ).obj G) := IsSemiAbelian.pullback C.ξ G hG
  have hp : IsGrpPullback ((Over.pullback C.ξ).obj G) G C.ξ (pullback.fst G.hom C.ξ) := isGrpPullback_pullback G C.ξ
  have h1 : IsGrpPullback ((Over.pullback (jK C.R)).obj C.G) G (jK C.R ≫ C.ξ) (C.α ≫ e) :=
    (C.gen.comp he).congr C.hy rfl
  have h2 : IsGrpPullback ((Over.pullback (jK C.R)).obj ((Over.pullback C.ξ).obj G)) G (jK C.R ≫ C.ξ)
      (pullback.fst ((Over.pullback C.ξ).obj G).hom (jK C.R) ≫ pullback.fst G.hom C.ξ) :=
    (isGrpPullback_pullback _ (jK C.R)).comp hp
  obtain ⟨ε, hε, hεc⟩ := grpPullback_iso h1 h2
  obtain ⟨Φ, ⟨hΦ, hFε⟩, -⟩ := GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing C.R) C.G
    ((Over.pullback C.ξ).obj G) C.semi hG' ε
  replace hFε : (Over.pullback (jK C.R)).map Φ.hom = ε.hom := hFε
  refine ⟨Φ.hom.left ≫ pullback.fst G.hom C.ξ, ((isGrpPullback_of_iso Φ).comp hp).congr (Category.id_comp _) rfl, ?_⟩
  rw [← hεc, ← hFε]
  have hl : ((Over.pullback (jK C.R)).map Φ.hom).left ≫ pullback.fst ((Over.pullback C.ξ).obj G).hom (jK C.R) =
      pullback.fst C.G.hom (jK C.R) ≫ Φ.hom.left := pullback.lift_fst _ _ _
  rw [← Category.assoc, hl, Category.assoc]

end GlobalTheory.Desc
