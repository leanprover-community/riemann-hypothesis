module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.GoodBaseChange

theorem good_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r → (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → xOf y' = spMap i ≫ xOf y → GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y' := by
  intro E _ _ _ H Dw l Xo c T T' io io' y y' i r _ hv hx hy
  obtain ⟨G, t, m1, m2, hp⟩ := hy
  obtain ⟨φ, hφ⟩ := GlobalTheory.IntFrBaseChange.exists_restrict T T' i r hv
  obtain ⟨G', mG⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', mt⟩ : ∃ t' : SAB H (Sp T'.Fr), Nonempty (SABMap t' t (spMap i)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap i) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mG⟩ := mG
  obtain ⟨mt⟩ := mt
  obtain ⟨n1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 mt
  have hsq : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => (hφ a).symm))
  rw [hsq] at n2
  obtain ⟨n3, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG n2
  have n4 : SABMap t' Xo.univ.t (xOf y') := by
    rw [hx]
    exact n1
  exact ⟨G', t', n4, n3, MorphismProperty.of_isPullback (P := @IsProper) mG.cart.1 hp⟩

end GlobalTheory.GoodBaseChange
