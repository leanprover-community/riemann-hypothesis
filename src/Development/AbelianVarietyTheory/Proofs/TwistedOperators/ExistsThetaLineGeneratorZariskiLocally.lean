module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFactorOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_secGen_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  intro E _ _ _ H Dw l Xo c T _ _ x hx q
  have hS := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨xF, h1, h2⟩ : ∃ xF : Sp T ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = x ∧
      xF ≫ pullback.snd _ _ = spMap (algebraMap c.F T) := by
    refine ⟨pullback.lift x (spMap (algebraMap c.F T)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hx]
    simp only [sOf, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.Frames.exists_openChart_testRing hS E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj T xF h2 q hp
  refine ⟨g, hg, ?_⟩
  let lam : T →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F T (Localization.Away g)
  obtain ⟨ψ, hψ⟩ := hT (Localization.Away g) lam (IsLocalization.Away.algebraMap_isUnit g)
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R _ ψ y₀
  have hzx : z.x = spMap (algebraMap T (Localization.Away g)) ≫ x := by
    rw [hz.1, ← hj.2.1, ← Category.assoc, ← hψ, Category.assoc, h1]
    rfl
  have key : ∀ x' : Sp (Localization.Away g) ⟶ Xo.X, z.x = x' → ∃ s : LB.Sec (PPx x'), SecGen x' s := by
    rintro _ rfl
    exact ⟨z.s, z.gen⟩
  exact key _ hzx

end GlobalTheory.HeckeEx
