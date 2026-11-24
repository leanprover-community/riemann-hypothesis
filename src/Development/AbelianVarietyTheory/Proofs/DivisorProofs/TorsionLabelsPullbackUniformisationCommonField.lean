module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

namespace GlobalTheory.Poinc.Sep.BaseChangeLabels

theorem qkToAkU_pullback_common_field : ∀ {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], IsCN V → IsCN V' → ∀ (j : V →+* V') (hj : Function.Injective j), IsLocalHom j → ∀ {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left) (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)), IsPullUnif j hD (Iso.refl _) U U' → IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j) → ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F'], (∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), QkToAkU U.toUnifPre F' k p₁ x₁ → ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧ QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left := by
  intro V V' _ _ _ _ _ _ hV hV' j hj _ D A G _ _ _ U D' hD A' gA U' hPU hgU hgA F' _ _ _ hF k hk p₁ x₁ hQ

  have hcomp : algebraMap (FractionRing V) F' = (algebraMap (FractionRing V') F').comp (fracMap hj) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors V)
    ext r
    simp only [RingHom.comp_apply, fracMap_algebraMap]
    exact hF r

  have P := GlobalTheory.UT.EndBaseChange.points GlobalTheory.firstFiveLaws.1.globalFns hD D.tau_bimult D'.tau_bimult F' hF
  obtain ⟨g', hg', -⟩ := P.1 p₁.g
  obtain ⟨h, hn, hi⟩ := p₁.eq
  obtain ⟨h', hh', -⟩ := P.1 h
  have hn' := (P.2.2.2 k p₁.g g' h h' hg' hh').1 hn
  have hi' : GtPtF.IsIota (hD.xe.symm p₁.y) h' := (P.2.2.1 h h' (hD.xe.symm p₁.y) hh').1 (by simpa using hi)
  let p' : QkPt D'.toPre F' k := ⟨hD.xe.symm p₁.y, g', ⟨h', hn', hi'⟩⟩

  have sq : x₁.left ≫ A.A.hom = (TFK (R := V') F').hom ≫ spMap (fracMap hj) := by
    rw [Over.w x₁]
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F')) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V') F')) ≫ Spec.map (CommRingCat.ofHom (fracMap hj))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let l := hgU.1.lift x₁.left (TFK (R := V') F').hom sq
  have hl₁ : l ≫ gA = x₁.left := hgU.1.lift_fst _ _ sq
  have hl₂ : l ≫ A'.A.hom = (TFK (R := V') F').hom := hgU.1.lift_snd _ _ sq
  let x' : TFK (R := V') F' ⟶ A'.A := Over.homMk l hl₂
  have hx' : x'.left ≫ gA = x₁.left := hl₁

  have hA : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hA' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf j)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  refine ⟨p', x', rfl, ?_, hx'⟩
  refine GlobalTheory.firstFiveLaws.2.2.2.2.qkBaseChange V V' (maximalIdeal V) (maximalIdeal V') hA hA' j D A G U
    ((Over.pullback (specOf j)).obj G) (Iso.refl _) mR A' D' hD U' hPU F' hF k hk p₁ x₁ p' x' rfl hg' ?_ hQ
  rw [Iso.refl_hom, Over.id_left, Category.id_comp, ← hx', Category.assoc, hgA]

end GlobalTheory.Poinc.Sep.BaseChangeLabels
