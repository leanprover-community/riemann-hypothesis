module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByChartsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DualCon.FieldRep

theorem hasRep_field : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  intro S A _ hA g hg K _ s
  have hA' : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hg' : SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K _ hA')
  have hAF : HasRepAF ((Over.pullback s).obj A) g (𝟙_ _) := GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian K _ g hA' hg' L hL hamp
  have h := (GlobalTheory.DualCon.hasRep_baseChange_iff S (Sp K) s A ((Over.pullback s).obj A) (pullback.fst A.hom s)
    (isGrpPullback_pullback A s) g (𝟙_ _)).1.1
  obtain ⟨B, b, P, hR, hG, -⟩ := hAF
  have h2 := h ⟨B, b, P, hR, hG⟩
  have e : (𝟙_ (Over (Sp K))).hom ≫ s = s := Category.id_comp s
  rw [e] at h2
  exact h2

end GlobalTheory.DualCon.FieldRep
