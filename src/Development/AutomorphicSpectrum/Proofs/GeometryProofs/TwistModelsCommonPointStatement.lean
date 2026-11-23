module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistModelsCommonPoint
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twist_models_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ := by
  exact @GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist
